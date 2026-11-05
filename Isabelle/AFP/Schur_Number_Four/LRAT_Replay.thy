(*  Title:      LRAT_Replay.thy
    Author:     Carles Marín
*)

section \<open>Kernel replay of LRAT proofs\<close>

theory LRAT_Replay
  imports Main
begin

text \<open>A goal \<open>\<lbrakk>C\<^sub>1; \<dots>; C\<^sub>n\<rbrakk> \<Longrightarrow> False\<close>, whose premises are propositional clauses over
  arbitrary HOL atoms, is closed by the method \<open>lrat\<close> from a precomputed LRAT proof of the unsatisfiability of
  the corresponding CNF.  The proof file is found in \<open>LRAT_Solver.dir\<close> under the SHA1 digest of the DIMACS text
  that Isabelle generates from the goal; if it is missing, that DIMACS file is written and the method fails.

  Only RUP steps are accepted.  Each step is turned into a resolution chain and replayed by the kernel with the
  clause representation of \<open>HOL/Tools/sat.ML\<close> (Weber and Amjad), forwards: a first pass over integers computes
  which derived clauses are needed and the step that uses each one last, and the replay drops every clause theorem
  right after its last use.  Nothing outside the kernel is trusted: the SAT solver, the proof file and its parser
  can only make the method fail.

  \<open>LRAT_Replay.instances\<close> produces the clauses of an encoding from schema facts and explicit instances: the
  ground side conditions of each instance are proved by \<open>simp\<close>.\<close>

ML_file \<open>lrat_solver.ML\<close>
ML_file \<open>lrat_replay.ML\<close>

method_setup lrat = \<open>Scan.succeed (SIMPLE_METHOD' o LRAT_Replay.tac)\<close>
  "kernel replay of a precomputed LRAT proof"

end
