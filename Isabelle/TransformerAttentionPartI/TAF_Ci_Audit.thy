(* Title: Kernel dependency audit of the complete finite and cosine session
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Ci_Audit
  imports TAF_RoPE_Scores TAF_Affine_Limits TAF_All_Null TAF_Smooth_Family
    TAF_Power_Support TAF_Strict_Family TAF_RoPE_Variation
begin

ML \<open>
  val authored = filter (fn ((n, _), _) => String.isPrefix "TAF_" n)
    (Global_Theory.all_thms_of \<^theory> false)
  val _ = if null authored then error "Empty authored-fact audit" else ()
  fun audit_fact ((n, ix), th) =
    let val deps = Thm_Deps.all_oracles [th]
        val labels = map (#1 o #1) deps
        val _ = if null labels then () else error ("Untrusted dependency in " ^ n)
    in n ^ "[" ^ string_of_int ix ^ "]\t" ^ space_implode "," labels end
  val rows = map audit_fact authored
  val _ = File.write
    (Path.append (Resources.master_directory \<^theory>) (Path.basic "ci_proof_dependencies.tsv"))
    (cat_lines ("fact\tdependencies" :: rows) ^ "\n")
  val _ = writeln ("TAF_CI_KERNEL_AUDIT: " ^ string_of_int (length rows) ^ " facts checked")
\<close>

end
