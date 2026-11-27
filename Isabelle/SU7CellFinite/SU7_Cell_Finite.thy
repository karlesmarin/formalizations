(*  Title:      SU7_Cell_Finite.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Finite fibres of the two SU(7) matter moments; the numerical moment coefficients are inputs from the Lean eight_generator_moments theorem.
*)

section \<open>A cell of the SU(7) moment map is a finite set\<close>

theory SU7_Cell_Finite
  imports Main
begin

text \<open>The eight bulk multiplets of the model carry the moments \<open>(8D, 2A\<^sub>4)\<close>
\<open>(-6,0), (8,2), (16,34), (2,8), (0,36), (28,16), (10,136), (80,218)\<close>, in the order \<open>7(+,+)\<close>, \<open>7(+,-)\<close>,
\<open>28(+,+)\<close>, \<open>28(+,-)\<close>, \<open>48(+,+)\<close>, \<open>48(+,-)\<close>, \<open>84(+,+)\<close>, \<open>84(+,-)\<close> (computed from the weights in Lean:
\<open>eight_generator_moments\<close>). A content is a tuple of multiplicities \<open>n\<^sub>1, \<dots>, n\<^sub>8\<close>, and a cell fixes the two
totals \<open>d = 8D\<close> and \<open>a = 2A\<^sub>4\<close> of the matter part.

Only the first multiplet has \<open>2A\<^sub>4 = 0\<close>. The other seven have \<open>2A\<^sub>4 \<ge> 2\<close>, so the second equation bounds their
multiplicities by \<open>a\<close>; the first equation then fixes \<open>n\<^sub>1\<close>, the only one left that still moves \<open>8D\<close>. Hence a
cell is finite: it can be enumerated rather than searched.\<close>

definition cell :: "int \<Rightarrow> int \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) set" where
  "cell d a = {(n1, n2, n3, n4, n5, n6, n7, n8).
     - 6 * int n1 + 8 * int n2 + 16 * int n3 + 2 * int n4 + 28 * int n6 + 10 * int n7 + 80 * int n8 = d
   \<and> 2 * int n2 + 34 * int n3 + 8 * int n4 + 36 * int n5 + 16 * int n6 + 136 * int n7 + 218 * int n8 = a}"

text \<open>The seven multiplets with \<open>2A\<^sub>4 > 0\<close> are bounded by \<open>a\<close>.\<close>

lemma cell_bound_seven:
  assumes "(n1, n2, n3, n4, n5, n6, n7, n8) \<in> cell d a"
  shows "int n2 \<le> a" "int n3 \<le> a" "int n4 \<le> a" "int n5 \<le> a" "int n6 \<le> a" "int n7 \<le> a" "int n8 \<le> a"
  using assms unfolding cell_def by auto

text \<open>The multiplicity of \<open>7(+,+)\<close> is forced by \<open>d\<close> and the other seven.\<close>

lemma cell_first_forced:
  assumes "(n1, n2, n3, n4, n5, n6, n7, n8) \<in> cell d a"
  shows "6 * int n1 = 8 * int n2 + 16 * int n3 + 2 * int n4 + 28 * int n6 + 10 * int n7 + 80 * int n8 - d"
  using assms unfolding cell_def by auto

lemma cell_bound_first:
  assumes "(n1, n2, n3, n4, n5, n6, n7, n8) \<in> cell d a"
  shows "int n1 \<le> \<bar>d\<bar> + 40 * \<bar>a\<bar>"
  using assms unfolding cell_def by auto

theorem cell_finite: "finite (cell d a)"
proof -
  define B where "B = nat (\<bar>d\<bar> + 40 * \<bar>a\<bar>)"
  have "cell d a \<subseteq> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B}"
  proof
    fix x assume x: "x \<in> cell d a"
    obtain n1 n2 n3 n4 n5 n6 n7 n8 where e: "x = (n1, n2, n3, n4, n5, n6, n7, n8)"
      by (metis surj_pair)
    from cell_bound_seven[OF x[unfolded e]] cell_bound_first[OF x[unfolded e]]
    show "x \<in> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B} \<times> {..B}"
      unfolding e B_def by auto
  qed
  then show ?thesis
    by (rule finite_subset) simp
qed

text \<open>A whole rung is not finite: \<open>48(+,+)\<close> has \<open>8D = 0\<close>, so at fixed \<open>d\<close> it can be added without limit.\<close>

theorem rung_infinite: "infinite {(n1, n2, n3, n4, n5::nat, n6, n7, n8).
     - 6 * int n1 + 8 * int n2 + 16 * int n3 + 2 * int n4 + 28 * int n6 + 10 * int n7 + 80 * int n8 = (0::int)}"
proof -
  let ?S = "{(n1, n2, n3, n4, n5::nat, n6, n7, n8).
     - 6 * int n1 + 8 * int n2 + 16 * int n3 + 2 * int n4 + 28 * int n6 + 10 * int n7 + 80 * int n8 = (0::int)}"
  let ?f = "\<lambda>k::nat. (0::nat, 0::nat, 0::nat, 0::nat, k, 0::nat, 0::nat, 0::nat)"
  have "inj ?f" by (simp add: inj_on_def)
  then have inf: "infinite (range ?f)" using finite_imageD infinite_UNIV_nat by blast
  have sub: "range ?f \<subseteq> ?S" by auto
  have infS: "infinite ?S" using infinite_super[OF sub inf] .
  show ?thesis using infS by simp
qed

end
