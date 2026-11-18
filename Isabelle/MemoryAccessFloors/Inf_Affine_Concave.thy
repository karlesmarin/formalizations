(*  Title:      Inf_Affine_Concave.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The infimum of a family of affine functions with non-negative slopes is non-decreasing and concave.
*)

theory Inf_Affine_Concave
  imports "HOL-Analysis.Analysis"
begin

definition inf_affine :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real"
  where "inf_affine I \<alpha> \<beta> r = Inf ((\<lambda>i. \<alpha> i + \<beta> i * r) ` I)"

lemma inf_affine_le:
  assumes "bdd_below ((\<lambda>i. \<alpha> i + \<beta> i * r) ` I)" "i \<in> I"
  shows "inf_affine I \<alpha> \<beta> r \<le> \<alpha> i + \<beta> i * r"
  unfolding inf_affine_def using assms by (intro cInf_lower) simp_all

lemma inf_affine_monotone:
  assumes "I \<noteq> {}" "\<forall>i\<in>I. 0 \<le> \<beta> i"
    "\<forall>r\<ge>0. bdd_below ((\<lambda>i. \<alpha> i + \<beta> i * r) ` I)"
  shows "monotone_on {0..} (\<le>) (\<le>) (inf_affine I \<alpha> \<beta>)"
proof (rule monotone_onI)
  fix r s :: real
  assume rs: "r \<in> {0..}" "s \<in> {0..}" "r \<le> s"
  have "\<forall>i\<in>I. inf_affine I \<alpha> \<beta> r \<le> \<alpha> i + \<beta> i * s"
  proof
    fix i assume i: "i \<in> I"
    have "inf_affine I \<alpha> \<beta> r \<le> \<alpha> i + \<beta> i * r"
      using inf_affine_le[where r = r and i = i] assms(3) rs(1) i by simp
    moreover have "\<beta> i * r \<le> \<beta> i * s" using assms(2) i rs(3) by (simp add: mult_left_mono)
    ultimately show "inf_affine I \<alpha> \<beta> r \<le> \<alpha> i + \<beta> i * s" by linarith
  qed
  then show "inf_affine I \<alpha> \<beta> r \<le> inf_affine I \<alpha> \<beta> s"
    unfolding inf_affine_def using assms(1) by (intro cInf_greatest) auto
qed

lemma inf_affine_concave:
  assumes "I \<noteq> {}" "\<forall>r\<ge>0. bdd_below ((\<lambda>i. \<alpha> i + \<beta> i * r) ` I)"
  shows "concave_on {0..} (inf_affine I \<alpha> \<beta>)"
proof (rule concave_on_linorderI)
  fix r s t :: real
  assume t: "0 < t" "t < 1" and rs: "r \<in> {0..}" "s \<in> {0..}" "r < s"
  have "\<forall>i\<in>I. (1 - t) * inf_affine I \<alpha> \<beta> r + t * inf_affine I \<alpha> \<beta> s
                \<le> \<alpha> i + \<beta> i * ((1 - t) *\<^sub>R r + t *\<^sub>R s)"
  proof
    fix i assume i: "i \<in> I"
    have a: "inf_affine I \<alpha> \<beta> r \<le> \<alpha> i + \<beta> i * r"
      using inf_affine_le[where r = r and i = i] assms(2) rs(1) i by simp
    have b: "inf_affine I \<alpha> \<beta> s \<le> \<alpha> i + \<beta> i * s"
      using inf_affine_le[where r = s and i = i] assms(2) rs(2) i by simp
    have "(1 - t) * inf_affine I \<alpha> \<beta> r + t * inf_affine I \<alpha> \<beta> s
          \<le> (1 - t) * (\<alpha> i + \<beta> i * r) + t * (\<alpha> i + \<beta> i * s)"
      using a b t by (intro add_mono mult_left_mono) simp_all
    also have "\<dots> = \<alpha> i + \<beta> i * ((1 - t) *\<^sub>R r + t *\<^sub>R s)" by (simp add: real_scaleR_def algebra_simps)
    finally show "(1 - t) * inf_affine I \<alpha> \<beta> r + t * inf_affine I \<alpha> \<beta> s
                  \<le> \<alpha> i + \<beta> i * ((1 - t) *\<^sub>R r + t *\<^sub>R s)" .
  qed
  then show "(1 - t) * inf_affine I \<alpha> \<beta> r + t * inf_affine I \<alpha> \<beta> s
             \<le> inf_affine I \<alpha> \<beta> ((1 - t) *\<^sub>R r + t *\<^sub>R s)"
    unfolding inf_affine_def using assms(1) by (intro cInf_greatest) auto
qed (simp add: convex_real_interval)

end
