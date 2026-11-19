(* Title: Dependency check for the standard Euler/Ein/Gamma bridge
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Ci_Probe
  imports "Exp_Log_Integral.Exp_Log_Integral" TAF_RoPE_Grid
begin

ML \<open>
  val names = ["Gamma_incu_0_conv_Ei_complex", "has_field_derivative_Ein",
    "has_field_derivative_Gamma_incu_complex", "Gamma_incu_at_top_complex"]
  fun check n =
    let val ths = Proof_Context.get_thms \<^context> n
        val deps = map (#1 o #1) (Thm_Deps.all_oracles ths)
        val _ = if null deps then () else error ("Untrusted dependency: " ^ n)
    in n ^ "\t" ^ space_implode "," deps end
  val _ = File.write
    (Path.append (Resources.master_directory \<^theory>) (Path.basic "ci_library_dependencies.tsv"))
    (cat_lines ("fact\tdependencies" :: map check names) ^ "\n")
\<close>

end
