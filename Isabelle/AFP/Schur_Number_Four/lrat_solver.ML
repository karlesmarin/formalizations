(*  LRAT proofs replayed by Isabelle's kernel through HOL/Tools/sat.ML.

    The solver "lrat" receives the CNF that sat.ML builds from the goal, writes it in DIMACS form and
    looks for a precomputed LRAT proof named after the SHA1 digest of that DIMACS text, in the
    directory LRAT_Solver.dir.  If there is none, it writes the .cnf file and fails, so that an
    external solver (CaDiCaL) can produce the proof.  Otherwise every RUP step of the LRAT proof is
    turned into a trivial resolution chain (conflict clause first, then the used unit clauses
    backwards) in the format of SAT_Solver.proof.  The kernel replays the chain in sat.ML; nothing
    here is trusted: a wrong conversion makes the replay fail, it cannot produce a theorem.
*)

structure LRAT_Solver =
struct

val dir = Unsynchronized.ref Path.current;

fun clauses_of fm =
  let
    fun lits (Prop_Logic.Or (a, b)) acc = lits a (lits b acc)
      | lits (Prop_Logic.BoolVar i) acc = i :: acc
      | lits (Prop_Logic.Not (Prop_Logic.BoolVar i)) acc = ~ i :: acc
      | lits _ _ = error "LRAT_Solver: formula is not in CNF"
    fun cls (Prop_Logic.And (a, b)) acc = cls a (cls b acc)
      | cls c acc = lits c [] :: acc
  in cls fm [] end;

fun int_str i = if i < 0 then "-" ^ string_of_int (~ i) else string_of_int i;

fun dimacs cls =
  let
    val n = fold (fn c => fold (fn l => Integer.max (abs l)) c) cls 0
    val body = map (fn c => space_implode " " (map int_str c @ ["0"]) ^ "\n") cls
  in String.concat (("p cnf " ^ string_of_int n ^ " " ^ string_of_int (length cls) ^ "\n") :: body) end;

fun to_int s =
  (case Int.fromString s of
    SOME i => i
  | NONE => error ("LRAT_Solver: number expected, found " ^ quote s));

(* split a token list at the first "0" *)
fun upto_zero (t :: ts) acc =
      if t = 0 then (rev acc, ts) else upto_zero ts (t :: acc)
  | upto_zero [] _ = error "LRAT_Solver: missing terminating 0";

exception DONE of int;

(* lines of a file in blocks of 1 MB (File.read of a very large certificate would exceed the size of one ML string) *)
fun iter_lines path f =
  File_Stream.open_input (fn ins =>
    let
      fun loop rest =
        (case File_Stream.input_size 1048576 ins of
          "" => if rest = "" then () else f rest
        | chunk =>
            let val parts = String.fields (fn ch => ch = #"\n") (rest ^ chunk)
            in List.app f (fst (split_last parts)); loop (List.last parts) end)
    in loop "" end) path;

fun convert cls text = convert_with cls (fn f => List.app f (split_lines text))
and convert_with cls iter =
  let
    val n = length cls
    (* arrays instead of functional tables.  Clause records indexed by LRAT id (growing arrays); the
       assignment of the forward pass and the literal set of the backward pass are «stamped» arrays indexed by
       literal (2v or 2v+1), so nothing is cleared between steps.  Same chains as before. *)
    val maxv = Unsynchronized.ref (fold (fn c => fold (fn l => fn m => Int.max (m, abs l)) c) cls 1)
    val lits = Unsynchronized.ref (Array.array (2 * n + 16, NONE : int list option))
    val sid = Unsynchronized.ref (Array.array (2 * n + 16, ~1))
    fun grow i =
      if i < Array.length (!lits) then ()
      else
        let
          val cap = Int.max (i + 1, 2 * Array.length (!lits))
          val l2 = Array.array (cap, NONE) and s2 = Array.array (cap, ~1)
        in
          Array.copy {src = !lits, dst = l2, di = 0}; Array.copy {src = !sid, dst = s2, di = 0};
          lits := l2; sid := s2
        end
    val _ = List.app (fn (k, c) => (grow (k + 1); Array.update (!lits, k + 1, SOME c); Array.update (!sid, k + 1, k)))
      (map_index I cls)
    val next = Unsynchronized.ref n
    val tab = Unsynchronized.ref (Inttab.empty : int list Inttab.table)
    fun lits_of h =
      (case (if h < Array.length (!lits) then Array.sub (!lits, h) else NONE) of
        SOME c => c
      | NONE => error ("LRAT_Solver: hint " ^ string_of_int h ^ " refers to an unknown clause"))
    fun sid_of h = Array.sub (!sid, h)
    fun ix l = if l > 0 then 2 * l else 2 * (~ l) + 1
    val asg = Unsynchronized.ref (Array.array (2 * !maxv + 2, 0))   (* asg[ix l] = stamp: l is assigned true *)
    val acc = Unsynchronized.ref (Array.array (2 * !maxv + 2, 0))   (* acc[ix l] = stamp: l is in the resolvent *)
    fun fit v =
      if 2 * v + 1 < Array.length (!asg) then ()
      else
        let val cap = 2 * (2 * v + 2)
            val a2 = Array.array (cap, 0) and c2 = Array.array (cap, 0)
        in Array.copy {src = !asg, dst = a2, di = 0}; Array.copy {src = !acc, dst = c2, di = 0}; asg := a2; acc := c2 end
    val stamp = Unsynchronized.ref 0
    fun add i c hs =
      let
        val _ = if exists (fn h => h <= 0) hs then error "LRAT_Solver: RAT steps are not supported" else ()
        val _ = Unsynchronized.inc stamp
        val st = !stamp
        val _ = List.app (fn l => (fit (abs l); Array.update (!asg, ix (~ l), st))) c
        fun true_now l = Array.sub (!asg, ix l) = st
        fun fwd [] _ = error ("LRAT_Solver: step " ^ string_of_int i ^ " ends without a conflict")
          | fwd (h :: rest) recs =
              (case filter (fn l => (fit (abs l); not (true_now (~ l)))) (lits_of h) of
                [] => (h, recs)
              | [u] => (Array.update (!asg, ix u, st); fwd rest ((h, u) :: recs))
              | _ => error ("LRAT_Solver: hint " ^ string_of_int h ^ " is not unit in step " ^ string_of_int i))
        val (conf, recs) = fwd hs []
        val cand = Unsynchronized.ref ([] : int list)   (* literals ever added to the resolvent *)
        fun ins l = if Array.sub (!acc, ix l) = st then () else (Array.update (!acc, ix l, st); cand := l :: !cand)
        val _ = List.app ins (lits_of conf)
        fun bwd [] ch = rev ch
          | bwd ((h, u) :: rs) ch =
              if Array.sub (!acc, ix (~ u)) = st then
                (Array.update (!acc, ix (~ u), 0); List.app (fn l => if l <> u then ins l else ()) (lits_of h);
                 bwd rs (h :: ch))
              else bwd rs ch
        val chain = bwd recs [conf]
        val d = sort int_ord (filter (fn l => Array.sub (!acc, ix l) = st) (distinct (op =) (!cand)))
        val s = !next
      in
        next := s + 1;
        tab := Inttab.update (s, map sid_of chain) (!tab);
        grow i; Array.update (!sid, i, s); Array.update (!lits, i, SOME d);
        if null d then raise DONE s else ()
      end
    fun line l =
      (case String.tokens Char.isSpace l of
        [] => ()
      | "c" :: _ => ()
      | _ :: "d" :: _ => ()
      | t :: ts =>
          let
            val (c, rest) = upto_zero (map to_int ts) []
            val (hs, _) = upto_zero rest []
          in add (to_int t) c hs end)
  in
    (iter line;
     error "LRAT_Solver: the proof never derives the empty clause")
    handle DONE e => (!tab, e)
  end;

(* lines of an XZ-compressed proof (<file>.xz), uncompressed in memory by Isabelle's XZ (AFP: 7.5 MB instead of 35) *)
fun iter_lines_xz path f =
  let
    fun loop rest [] = if rest = "" then () else f rest
      | loop rest (chunk :: chunks) =
          let val parts = String.fields (fn ch => ch = #"\n") (rest ^ chunk)
          in List.app f (fst (split_last parts)); loop (List.last parts) chunks end
  in loop "" (Bytes.contents (XZ.uncompress (Bytes.read path))) end;

fun xz_of path = Path.ext "xz" path;
fun proof_exists path = File.exists path orelse File.exists (xz_of path);

fun convert_file cls path =
  convert_with cls (if File.exists path then iter_lines path else iter_lines_xz (xz_of path));

fun solver fm =
  let
    val cls = clauses_of fm
    val text = dimacs cls
    val base = "lrat_" ^ Message_Digest.rep (SHA1.digest text)
    val cnf = Path.append (!dir) (Path.basic (base ^ ".cnf"))
    val prf = Path.append (!dir) (Path.basic (base ^ ".lrat"))
  in
    if File.exists prf then SAT_Solver.UNSATISFIABLE (SOME (convert_file cls prf))
    else
      (File.write cnf text;
       error ("LRAT_Solver: no proof for this formula; wrote " ^ Path.print cnf ^
         " (run an LRAT-producing solver on it, save the proof as " ^ base ^ ".lrat, rebuild)"))
  end;

val _ = SAT_Solver.add_solver ("lrat", solver);

end;
