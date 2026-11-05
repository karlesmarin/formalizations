(*  Forward LCF replay of LRAT proofs with release at last use (a variant of the replay in HOL/Tools/sat.ML).

    sat.ML (Weber and Amjad 2009) replays backwards and lazily, and keeps the theorem of every proved
    clause until the end, so memory grows with the whole needed proof.  Here a cheap pass over
    integers first computes which derived clauses are needed for the empty clause and, for each
    clause, the step that uses it last.  The replay then goes forwards and drops every clause
    theorem right after its last use, so the live set is bounded by the needed clauses that are
    still to be used.  The clause representation and the resolution step are those of sat.ML
    ("CNF sequent": [C_1 && ... && C_n, literals] |- False), adapted here because sat.ML does not
    export them.  As in sat.ML, nothing outside the kernel is trusted.
*)

structure LRAT_Replay =
struct

val counter = Unsynchronized.ref 0;
val peak_live = Unsynchronized.ref 0;
val parallel = Unsynchronized.ref false;  (* level-parallel replay *)
val parallel_min_width = Unsynchronized.ref 256;
val levels_report = Unsynchronized.ref (0, 0);  (* (number of levels, widest level) of the last parallel replay *)

fun lit_ord (i, j) = int_ord (abs i, abs j);

(* resolution of two raw clauses, as resolve_raw_clauses in sat.ML (binary step) *)
fun resolve (c1, hyps1) (c2, hyps2) =
  let
    fun merge xs [] = xs
      | merge [] ys = ys
      | merge (x :: xs) (y :: ys) =
          (case lit_ord (apply2 fst (x, y)) of
            LESS => x :: merge xs (y :: ys)
          | EQUAL => x :: merge xs ys
          | GREATER => y :: merge (x :: xs) ys)
    fun find ([], _) _ = raise THM ("LRAT_Replay: no literal for resolution", 0, [])
      | find (_, []) _ = raise THM ("LRAT_Replay: no literal for resolution", 0, [])
      | find (h1 :: t1, h2 :: t2) acc =
          (case lit_ord (apply2 fst (h1, h2)) of
            LESS => find (t1, h2 :: t2) (h1 :: acc)
          | EQUAL =>
              let val ((i1, ch1), (i2, ch2)) = (h1, h2) in
                if i1 = ~ i2 then (i1 < 0, ch1, ch2, rev acc @ merge t1 t2)
                else find (t1, t2) (h1 :: acc)
              end
          | GREATER => find (h1 :: t1, t2) (h2 :: acc))
    val (neg1, hyp1, hyp2, new_hyps) = find (hyps1, hyps2) []
    val c1' = Thm.implies_intr hyp1 c1
    val c2' = Thm.implies_intr hyp2 c2
    val P = HOLogic.dest_judgment (if neg1 then hyp2 else hyp1)
    val res_thm =
      \<^instantiate>\<open>P in
        lemma \<open>(P \<Longrightarrow> False) \<Longrightarrow> (\<not> P \<Longrightarrow> False) \<Longrightarrow> False\<close> by (rule case_split)\<close>
    val c = Thm.implies_elim (Thm.implies_elim res_thm (if neg1 then c2' else c1')) (if neg1 then c1' else c2')
  in Unsynchronized.inc counter; (c, new_hyps) end;

(* which derived clauses are needed, and the step at which each clause is used for the last time *)
fun plan n (tab : int list Inttab.table) empty =
  let
    fun visit s needed =
      if s < n orelse Inttab.defined needed s then needed
      else fold visit (the (Inttab.lookup tab s)) (Inttab.update (s, ()) needed)
    val needed = visit empty Inttab.empty
    val steps = Inttab.keys needed  (* increasing = forward order of the LRAT proof *)
    val last = fold (fn s => fold (fn m => Inttab.update (m, s)) (the (Inttab.lookup tab s))) steps Inttab.empty
  in (steps, last) end;

fun replay ctxt atom_table orig n proof = replay_raw ctxt atom_table (CNF.clause2raw_thm ctxt o orig) n proof
(* raw0 i: the RAW theorem of original clause i («[¬l1, …, ¬lk] ⊢ False») *)
and replay_raw ctxt atom_table raw0 n (tab, empty) =
  let
    fun index_of_literal chyp =
      (case (HOLogic.dest_Trueprop o Thm.term_of) chyp of
        (Const (\<^const_name>\<open>Not\<close>, _) $ atom) => SOME (~ (the (Termtab.lookup atom_table atom)))
      | atom => SOME (the (Termtab.lookup atom_table atom)))
      handle TERM _ => NONE | Option.Option => NONE
    fun raw_of i =
      let
        val raw = raw0 i  (* called only for clauses the proof uses *)
        val hyps = sort (lit_ord o apply2 fst)
          (map_filter (fn ch => Option.map (rpair ch) (index_of_literal ch)) (Thm.chyps_of raw))
      in (raw, hyps) end
    val (steps, last) = plan n tab empty
    val live = Unsynchronized.ref (Inttab.empty : (thm * (int * cterm) list) Inttab.table)
    fun get m =
      (case Inttab.lookup (!live) m of
        SOME c => c
      | NONE =>
          if m < n then let val c = raw_of m in live := Inttab.update (m, c) (!live); c end
          else raise THM ("LRAT_Replay: clause " ^ string_of_int m ^ " used after release", 0, []))
    fun step s =
      let
        val chain = the (Inttab.lookup tab s)
        val c = (case map get chain of c0 :: cs => fold (fn c' => fn acc => resolve acc c') cs c0
                   | [] => raise THM ("LRAT_Replay: empty chain", 0, []))
        (* With proof terms on, Thm.implies_intr walks the WHOLE proof term of the clause
           (Proofterm.gen_implies_intr_proof / abshyp), which contains the whole derivation history:
           quadratic or worse.  Boxing each derived clause (Thm.close_derivation makes a PThm node
           applied to its hyps) stops that walk at the box: every later step only sees a pointer. *)
        val c = if Proofterm.any_proofs_enabled () then apfst (Thm.close_derivation \<^here>) c else c
        val _ = live := Inttab.update (s, c) (!live)
        val _ = peak_live := Int.max (!peak_live, Inttab.size (!live))
        val _ = List.app (fn m => if Inttab.lookup last m = SOME s then live := Inttab.delete_safe m (!live) else ())
          (distinct (op =) chain)
      in () end
    val _ = (counter := 0; peak_live := 0)
    (* Parallel replay: steps grouped by level (1 + the highest level of the derived clauses they use);
       the steps of one level are independent and are resolved with Par_List.map (theorems are immutable values,
       so this is safe); then inserted, and released after their last use, as in the sequential replay. *)
    fun level_of tab_levels s =
      fold (fn m => fn acc => if m < n then acc else Int.max (acc, 1 + the (Inttab.lookup tab_levels m)))
        (the (Inttab.lookup tab s)) 0
    fun run_parallel () =
      let
        val levels = fold (fn s => fn t => Inttab.update (s, level_of t s) t) steps Inttab.empty
        val by_level = Inttab.fold (fn (s, l) => Inttab.map_default (l, []) (cons s)) levels Inttab.empty
        (* last use BY LEVEL (the sequential «last» is by step id; a later step can sit at a lower level,
           run first, and release a clause that a higher level still needs: «used after release») *)
        val last_level = fold (fn s => fn t =>
            let val l = the (Inttab.lookup levels s)
            in fold (fn m => Inttab.map_default (m, l) (fn l' => Int.max (l, l'))) (the (Inttab.lookup tab s)) t end)
          steps Inttab.empty
        fun do_level (lv, ss) =
          let
            val ss = sort int_ord ss
            val _ = List.app (fn s => List.app (fn m => ignore (get m)) (the (Inttab.lookup tab s))) ss
            val snapshot = !live
            fun get_ro m = the (Inttab.lookup snapshot m)
            fun resolve_step s =
              let
                val chain = the (Inttab.lookup tab s)
                val c = (case map get_ro chain of c0 :: cs => fold (fn c' => fn acc => resolve acc c') cs c0
                           | [] => raise THM ("LRAT_Replay: empty chain", 0, []))
              in (s, if Proofterm.any_proofs_enabled () then apfst (Thm.close_derivation \<^here>) c else c) end
            (* a barrier per level costs more than it saves on narrow levels *)
            val res = (if length ss >= !parallel_min_width then Par_List.map else map) resolve_step ss
          in
            List.app (fn (s, c) => live := Inttab.update (s, c) (!live)) res;
            peak_live := Int.max (!peak_live, Inttab.size (!live));
            List.app (fn s => List.app (fn m =>
                if Inttab.lookup last_level m = SOME lv then live := Inttab.delete_safe m (!live) else ())
              (distinct (op =) (the (Inttab.lookup tab s)))) ss
          end
        val _ = levels_report := (Inttab.size by_level, Inttab.fold (fn (_, ss) => Integer.max (length ss)) by_level 0)
      in List.app do_level (Inttab.dest by_level) end  (* Inttab.dest: ascending levels *)
    (* the sequential replay on DENSE indices: originals 0 … n-1, the p-th needed step n + p.  Chains
       are translated once; the live clauses and the last use are arrays, so the inner loop does no table lookups *)
    fun run_dense () =
      let
        val nsteps = length steps
        val pos = fold (fn (p, s) => Inttab.update (s, p)) (map_index I steps) Inttab.empty
        fun dense m = if m < n then m else n + the (Inttab.lookup pos m)
        val chains = Array.fromList (map (fn s => map dense (the (Inttab.lookup tab s))) steps)
        val last_a = Array.array (n + nsteps, ~1)
        val _ = Array.appi (fn (p, ch) => List.app (fn d => Array.update (last_a, d, p)) ch) chains
        val live_a = Array.array (n + nsteps, NONE : (thm * (int * cterm) list) option)
        val nlive = Unsynchronized.ref 0
        fun put d c = (Array.update (live_a, d, SOME c); Unsynchronized.inc nlive; ())
        fun get_d d =
          (case Array.sub (live_a, d) of
            SOME c => c
          | NONE =>
              if d < n then let val c = raw_of d in put d c; c end
              else raise THM ("LRAT_Replay: clause " ^ string_of_int d ^ " used after release", 0, []))
        fun step_d p =
          let
            val ch = Array.sub (chains, p)
            val c = (case map get_d ch of c0 :: cs => fold (fn c' => fn acc => resolve acc c') cs c0
                       | [] => raise THM ("LRAT_Replay: empty chain", 0, []))
            val c = if Proofterm.any_proofs_enabled () then apfst (Thm.close_derivation \<^here>) c else c
          in
            put (n + p) c;
            peak_live := Int.max (!peak_live, !nlive);
            List.app (fn d => if Array.sub (last_a, d) = p andalso is_some (Array.sub (live_a, d))
                              then (Array.update (live_a, d, NONE); nlive := !nlive - 1) else ()) ch
          end
        val _ = if Inttab.lookup pos empty = SOME (nsteps - 1) then ()
                else raise THM ("LRAT_Replay: the empty clause is not the last needed step", 0, [])
        val _ = List.app step_d (0 upto nsteps - 1)
      in fst (the (Array.sub (live_a, n + nsteps - 1))) end
  in
    if !parallel then (run_parallel (); fst (the (Inttab.lookup (!live) empty)))
    else run_dense ()
  end;

fun lrat_thm ctxt prems =
  let
    val nontrivial = filter (not o CNF.clause_is_trivial o HOLogic.dest_Trueprop o Thm.term_of) prems
    val sorted = sort Thm.fast_term_ord nontrivial
    val (fms, atom_table) =
      fold_map (Prop_Logic.prop_formula_of_term o HOLogic.dest_Trueprop o Thm.term_of) sorted Termtab.empty
    val fm = Prop_Logic.all fms
    val cls = LRAT_Solver.clauses_of fm
    val text = LRAT_Solver.dimacs cls
    val base = "lrat_" ^ Message_Digest.rep (SHA1.digest text)
    val cnf = Path.append (!LRAT_Solver.dir) (Path.basic (base ^ ".cnf"))
    val prf = Path.append (!LRAT_Solver.dir) (Path.basic (base ^ ".lrat"))
    val _ = if LRAT_Solver.proof_exists prf then ()   (* <base>.lrat or <base>.lrat.xz *)
      else (File.write cnf text; error ("LRAT_Replay: no proof for this formula; wrote " ^ Path.print cnf))
    val proof = LRAT_Solver.convert_file cls prf
    val clauses_thm = Conjunction.intr_balanced (map Thm.assume sorted)
    val clauses_cprop = Thm.cprop_of clauses_thm
    val orig = Conjunction.elim_balanced (length sorted) (Thm.assume clauses_cprop)
    val raw = replay ctxt atom_table (nth orig) (length sorted) proof
  in Thm.implies_elim (Thm.implies_intr clauses_cprop raw) clauses_thm end;

fun tac ctxt i =
  Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
    resolve_tac ctxt' [lrat_thm ctxt' (map Thm.cprop_of prems)] 1) ctxt i;

(* Encoding by KNOWN instances (Schur, Ramsey, van der Waerden, ...): the author knows which instance of
   each schema gives each clause, so nothing is searched.  instances ctxt th names tuples: for each tuple of natural
   numbers, instantiate the schematic variables «names» of th (in that order) with those numerals and prove every
   premise, now ground, by simp; the conclusions are returned unchanged (e.g. «¬ f 3 = 2 ∨ ¬ f 5 = 2 ∨ ¬ f 8 = 2»).
   A premise simp cannot prove raises an error naming the tuple: a wrong range in the theory, not a silent drop. *)
fun instances ctxt th names tuples =
  let
    val vars = Term.add_vars (Thm.prop_of th) []
    fun var_of nm = (case find_first (fn ((x, _), _) => x = nm) vars of SOME v => v
                     | NONE => error ("instances: no schematic variable ?" ^ nm))
    val vs = map var_of names
    fun one tup =
      let
        val insts = map2 (fn (xi, T) => fn k => (xi, Thm.cterm_of ctxt (HOLogic.mk_number T k))) vs tup
        val th1 = Drule.infer_instantiate ctxt insts th
        fun discharge t =
          (case Thm.prems_of t of
            [] => t
          | p :: _ =>
              let val pt = Goal.prove ctxt [] [] p (fn _ => simp_tac ctxt 1)
                    handle ERROR msg => error ("instances: premise not proved by simp for " ^
                                               ML_Syntax.print_list string_of_int tup ^ ": " ^ msg)
              in discharge (Thm.implies_elim t pt) end)
      in discharge th1 end
  in map one tuples end;

end;
