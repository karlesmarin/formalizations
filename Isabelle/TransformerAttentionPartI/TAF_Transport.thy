(* Title: Sharp diameter transport bound in a finite probability space
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Transport
  imports TAF_Vector_Output TAF_Softmax
begin

lemma positive_part_abs:
  fixes x :: real
  shows "max x 0=(abs x+x)/2"
  by (auto simp: max_def abs_if)

lemma tv_zero_equal:
  assumes fin: "finite S" and z: "tv_distance S p q=0" and i: "i\<in>S"
  shows "p i=q i"
proof -
  have total: "(\<Sum>i\<in>S. abs (p i-q i))=0" using z by (simp add: tv_distance_def)
  have "abs (p i-q i)=0"
    by (rule sum_nonneg_0[OF fin _ total i]) simp
  then show ?thesis by simp
qed

lemma diameter_tv_transport:
  assumes p: "finite_probability S p" and q: "finite_probability S q"
    and diam: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> norm (v i-v j)\<le>D"
  shows "norm (vector_mean S p v-vector_mean S q v)\<le>D*tv_distance S p q"
proof -
  interpret p: finite_probability S p by (rule p)
  interpret q: finite_probability S q by (rule q)
  let ?T = "tv_distance S p q"
  let ?a = "\<lambda>i. max (p i-q i) 0"
  let ?b = "\<lambda>i. max (q i-p i) 0"
  have Tnn: "0\<le>?T" unfolding tv_distance_def by (intro divide_nonneg_nonneg sum_nonneg) auto
  have suma: "sum ?a S=?T"
    by (simp add: positive_part_abs tv_distance_def sum_divide_distrib[symmetric]
        sum.distrib sum_subtractf p.p_sum q.p_sum)
  have sumb: "sum ?b S=?T"
    by (simp add: positive_part_abs tv_distance_def sum_divide_distrib[symmetric]
        sum.distrib sum_subtractf p.p_sum q.p_sum abs_minus_commute)
  show ?thesis
  proof (cases "?T=0")
    case True
    have "vector_mean S p v=vector_mean S q v"
      unfolding vector_mean_def
      by (rule sum.cong[OF refl]; simp only: tv_zero_equal[OF p.finite_S True])
    then show ?thesis using True by simp
  next
    case False
    have Tp: "0<?T" using Tnn False by linarith
    have an: "finite_probability S (\<lambda>i. ?a i/?T)"
      by (unfold_locales; use p.finite_S Tp suma in
          \<open>auto simp: sum_divide_distrib[symmetric] intro: divide_nonneg_nonneg\<close>)
    have bn: "finite_probability S (\<lambda>i. ?b i/?T)"
      by (unfold_locales; use p.finite_S Tp sumb in
          \<open>auto simp: sum_divide_distrib[symmetric] intro: divide_nonneg_nonneg\<close>)
    have diff: "p i-q i=?a i-?b i" for i
      by (auto simp: max_def)
    have pt: "(p i-q i) *\<^sub>R v i = ?T *\<^sub>R ((?a i/?T) *\<^sub>R v i-(?b i/?T) *\<^sub>R v i)" for i
    proof -
      have cancel: "?T*(?a i/?T)-?T*(?b i/?T)=?a i-?b i" using False by simp
      have scalar: "?T*(?a i/?T)-?T*(?b i/?T)=p i-q i" using cancel diff[of i] by argo
      have rhs: "?T *\<^sub>R ((?a i/?T) *\<^sub>R v i-(?b i/?T) *\<^sub>R v i) =
        (?T*(?a i/?T)-?T*(?b i/?T)) *\<^sub>R v i"
        by (simp only: scaleR_diff_right scaleR_scaleR scaleR_diff_left)
      show ?thesis by (simp only: rhs scalar)
    qed
    have id: "vector_mean S p v-vector_mean S q v =
      ?T *\<^sub>R (vector_mean S (\<lambda>i. ?a i/?T) v-vector_mean S (\<lambda>i. ?b i/?T) v)"
    proof -
      have a: "vector_mean S p v-vector_mean S q v = (\<Sum>i\<in>S. (p i-q i) *\<^sub>R v i)"
        by (simp add: vector_mean_def sum_subtractf scaleR_diff_left)
      have b: "(\<Sum>i\<in>S. (p i-q i) *\<^sub>R v i) =
        (\<Sum>i\<in>S. ?T *\<^sub>R ((?a i/?T) *\<^sub>R v i-(?b i/?T) *\<^sub>R v i))"
        by (rule sum.cong[OF refl]; rule pt)
      have c: "(\<Sum>i\<in>S. ?T *\<^sub>R ((?a i/?T) *\<^sub>R v i-(?b i/?T) *\<^sub>R v i)) =
        ?T *\<^sub>R (vector_mean S (\<lambda>i. ?a i/?T) v-vector_mean S (\<lambda>i. ?b i/?T) v)"
        by (simp only: vector_mean_def scaleR_sum_right scaleR_diff_right sum_subtractf)
      show ?thesis using a b c by argo
    qed
    have bound: "norm (vector_mean S (\<lambda>i. ?a i/?T) v-vector_mean S (\<lambda>i. ?b i/?T) v)\<le>D"
      by (rule convex_diameter[OF an bn diam])
    show ?thesis using mult_left_mono[OF bound Tnn]
      by (simp add: id norm_scaleR abs_of_nonneg Tnn mult.commute)
  qed
qed

lemma softmax_output_oscillation:
  assumes fin: "finite S" and ne: "S\<noteq>{}"
    and lo: "\<And>i. i\<in>S \<Longrightarrow> l\<le>r i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> r i\<le>u"
    and D: "0\<le>D"
    and diam: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> norm (v i-v j)\<le>D"
  shows "norm (vector_mean S (finite_softmax S s) v-
    vector_mean S (finite_softmax S (\<lambda>i. s i+r i)) v)\<le>D*tanh ((u-l)/4)"
proof -
  have tr: "norm (vector_mean S (finite_softmax S s) v-
    vector_mean S (finite_softmax S (\<lambda>i. s i+r i)) v)\<le>
      D*tv_distance S (finite_softmax S s) (finite_softmax S (\<lambda>i. s i+r i))"
    by (rule diameter_tv_transport[OF softmax_probability[OF fin ne]
        softmax_probability[OF fin ne] diam])
  have b: "D*tv_distance S (finite_softmax S s) (finite_softmax S (\<lambda>i. s i+r i))\<le>D*tanh ((u-l)/4)"
    by (rule mult_left_mono[OF softmax_oscillation_bound[OF fin ne lo hi, where s=s] D])
  show ?thesis using tr b by linarith
qed

context finite_truncation
begin

lemma frozen_output_diameter:
  assumes "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> norm (v i-v j)\<le>D"
  shows "norm (vector_mean S p v-vector_mean S (cut_prob K p) v)\<le>D*(1-sum p K)"
  using diameter_tv_transport[OF finite_probability_axioms cut_probability assms] truncation_tv by simp

end
end
