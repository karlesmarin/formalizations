(*  Title:      Family_Anomaly.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: su7-proton-decay, Proposition prop:identity: [SU(2)_L]^2 U(1)' = (1/2) sum_j A_j with A_j = 3 a_j + l_j, and
   its consequences (N = 1 forces A = 0; N > 1 escapes; universal a gives A_j = l_j - mean l) *)
theory Family_Anomaly
  imports Complex_Main
begin

text \<open>Proposition \<open>prop:identity\<close> of the note on proton decay in SU(7) gauge-Higgs unification. Model input (from
  the note, not proved here): per generation $j$ the $SU(2)_L$ doublets charged under $U(1)'$ are the quark doublet $Q_j$
  (three colours, charge $a_j$) and the lepton doublet $L_j$ (charge $l_j$); the Dynkin index of the doublet is
  $T=\tfrac12$, so the mixed anomaly is $[SU(2)_L]^2U(1)'=\tfrac12\sum_j(3a_j+l_j)$. The proton-operator charge of
  generation $j$ is $A_j=3a_j+l_j$. Attribution: the identity and its reading are the note's (its \S9); the
  family-dependent escape mirrors Lee and Ma's family $U(1)$ (the note's reference [FamilyU1]: $\sum x_i=3$,
  $x_i\neq 1$); anomaly cancellation itself is textbook.\<close>

definition anomaly :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "anomaly a l N = (\<Sum>j<N. 1/2 * (3 * a j + 1 * l j))"   (* T(2) = 1/2; 3 colours for Q, 1 for L *)

definition Acharge :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Acharge a l j = 3 * a j + l j"

theorem anomaly_identity: "anomaly a l N = 1/2 * (\<Sum>j<N. Acharge a l j)"
  unfolding anomaly_def Acharge_def by (simp add: sum_distrib_left)

text \<open>One generation: cancellation and protection are the same equation, so they exclude each other.\<close>
corollary one_generation: "anomaly a l 1 = 0 \<longleftrightarrow> Acharge a l 0 = 0"
  by (simp add: anomaly_identity)

text \<open>Three generations: the sum can vanish with no term vanishing (the escape exists only for $N>1$).\<close>
corollary three_generations_escape:
  "\<exists>a l. anomaly a l 3 = 0 \<and> (\<forall>j<3. Acharge a l j \<noteq> 0)"
proof -
  define a :: "nat \<Rightarrow> real" where "a = (\<lambda>j. 0)"
  define l :: "nat \<Rightarrow> real" where "l = (\<lambda>j. if j = 0 then 1 else if j = 1 then 1 else -2)"
  have "anomaly a l 3 = 0" unfolding anomaly_def a_def l_def by (simp add: numeral_3_eq_3)
  moreover have "\<forall>j<3. Acharge a l j \<noteq> 0" unfolding Acharge_def a_def l_def by (auto simp: less_Suc_eq numeral_3_eq_3)
  ultimately show ?thesis by blast
qed

text \<open>Family-universal quark charge $a_j=a$: cancellation gives $a=-\sum l/(3N)$ (for $N=3$, $-\sum l/9$), then
  $A_j=l_j-\bar l$, so protection ($A_j\neq0$ for all $j$) holds iff no generation sits at the mean.\<close>
theorem universal_quark_charge:
  assumes N: "0 < N" and univ: "\<And>j. a j = c" and canc: "anomaly a l N = 0"
  shows "c = - (\<Sum>j<N. l j) / (3 * N)"
    and "\<And>j. Acharge a l j = l j - (\<Sum>i<N. l i) / N"
proof -
  have h: "(\<Sum>j<N. (3 * c + l j) / 2) = 0" using canc univ unfolding anomaly_def by simp
  have "(\<Sum>j<N. 3 * c + l j) = 0" using h by (simp add: sum_divide_distrib[symmetric])
  then have s: "3 * c * N + (\<Sum>j<N. l j) = 0" by (simp add: sum.distrib mult.commute)
  show c: "c = - (\<Sum>j<N. l j) / (3 * N)" using s N by (simp add: field_simps)
  show "\<And>j. Acharge a l j = l j - (\<Sum>i<N. l i) / N"
    using c N univ unfolding Acharge_def by (simp add: field_simps)
qed

corollary protection_iff_off_mean:
  assumes "0 < N" "\<And>j. a j = c" "anomaly a l N = 0"
  shows "(\<forall>j<N. Acharge a l j \<noteq> 0) \<longleftrightarrow> (\<forall>j<N. l j \<noteq> (\<Sum>i<N. l i) / N)"
  using universal_quark_charge(2)[OF assms] by simp

end
