(* Title: Positivity of the instrumental null and zero-query attention
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Uniform_Null
  imports TAF_Softmax TAF_Secants
begin

lemma probe_null_positive:
  assumes p: "finite_probability R (a k)"
    and count: "\<And>r. r\<in>R \<Longrightarrow> 0<n k r"
  shows "0<probe_null R a n k"
proof -
  interpret p: finite_probability R "a k" by (rule p)
  obtain r where r: "r\<in>R" "0<a k r"
    using positive_sum_has_positive_term[where f="a k" and S=R] p.p_sum by auto
  have nr: "0<real (n k r)" using count[OF r(1)] by simp
  have quot: "0<a k r/real (n k r)" by (rule divide_pos_pos[OF r(2) nr])
  have ex: "\<exists>r\<in>R. 0<a k r/real (n k r)" using r(1) quot by blast
  show ?thesis unfolding probe_null_def
    by (rule p.positive_sum; use p.p_nonneg count ex in \<open>auto intro: divide_nonneg_nonneg\<close>)
qed

lemma uniform_softmax:
  "finite_softmax S (\<lambda>_. c) i=1/real (card S)"
  by (simp add: finite_softmax_def)

lemma zero_query_uniform:
  fixes key :: "'a \<Rightarrow> 'v::real_inner"
  shows "finite_softmax S (\<lambda>i. inner 0 (key i)/sqrt h) j=1/real (card S)"
  by (simp add: uniform_softmax)

lemma linear_zero_query_uniform:
  fixes query_rotation :: "'v::real_inner \<Rightarrow> 'v"
    and key :: "'a \<Rightarrow> 'v"
  assumes "linear query_rotation"
  shows "finite_softmax S (\<lambda>i. inner (query_rotation 0) (key i)/sqrt h) j=1/real (card S)"
  using linear_0[OF assms] by (simp add: uniform_softmax)

lemma causal_row_uniform:
  "finite_softmax {0..n::nat} (\<lambda>_. 0) j=1/(real n+1)"
  by (simp add: uniform_softmax)

end
