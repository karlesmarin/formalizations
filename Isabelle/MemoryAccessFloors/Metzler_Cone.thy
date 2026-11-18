(*  Title:      Metzler_Cone.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Invariant cones of 2x2 linear systems with continuous coefficients whose off-diagonal entries are
    non-negative (Metzler matrices): if y' = A(t) y and y(0) >= 0 componentwise then y(t) >= 0 for all
    t in [0, T].  The proof is the first-exit argument on the perturbation y + eps exp(K t).
    Also: a ratio is non-increasing when its logarithmic derivative is non-positive.
*)
theory Metzler_Cone
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. First exit\<close>

lemma exit_contra:
  fixes f :: "real \<Rightarrow> real" and l t0 :: real
  assumes d: "(f has_real_derivative l) (at t0)" and lp: "0 < l" and ft: "f t0 \<le> 0" and t0p: "0 < t0"
    and pos: "\<forall>s. 0 \<le> s \<longrightarrow> s < t0 \<longrightarrow> 0 < f s"
  shows False
proof -
  obtain e where ep: "0 < e" and ee: "\<forall>h>0. h < e \<longrightarrow> f (t0 - h) < f t0"
    using DERIV_pos_inc_left[OF d lp] by blast
  define h where "h = min e t0 / 2"
  have m1: "min e t0 \<le> e" and m2: "min e t0 \<le> t0" by simp_all
  have mp: "0 < min e t0" using ep t0p by simp
  have hp: "0 < h" unfolding h_def using mp by simp
  have h1: "h < e" unfolding h_def using m1 mp by linarith
  have h2: "h < t0" unfolding h_def using m2 mp by linarith
  have "0 \<le> t0 - h" using h2 by simp
  moreover have "t0 - h < t0" using hp by simp
  ultimately have "0 < f (t0 - h)" using pos by blast
  moreover have "f (t0 - h) < f t0" using ee hp h1 by blast
  ultimately show False using ft by linarith
qed

lemma left_nonneg:
  fixes f :: "real \<Rightarrow> real" and T t0 :: real
  assumes cf: "continuous_on {0..T} f" and t0p: "0 < t0" and t0T: "t0 \<le> T"
    and pos: "\<forall>s. 0 \<le> s \<longrightarrow> s < t0 \<longrightarrow> 0 < f s"
  shows "0 \<le> f t0"
proof -
  have cl: "closed {s \<in> {0..T}. 0 \<le> f s}"
    by (rule continuous_on_closed_Collect_le[OF continuous_on_const cf closed_atLeastAtMost])
  have sub: "{0..<t0} \<subseteq> {s \<in> {0..T}. 0 \<le> f s}"
  proof
    fix s assume s: "s \<in> {0..<t0}"
    then have "0 < f s" using pos by simp
    moreover have "s \<in> {0..T}" using s t0T by simp
    ultimately show "s \<in> {s \<in> {0..T}. 0 \<le> f s}" by simp
  qed
  have "t0 \<in> closure {0..<t0}" using t0p by (simp add: closure_atLeastLessThan)
  then have "t0 \<in> {s \<in> {0..T}. 0 \<le> f s}" using closure_minimal[OF sub cl] by blast
  then show ?thesis by simp
qed

section \<open>B. The invariant cone\<close>

theorem metzler_cone_2x2:
  fixes a11 a12 a21 a22 y1 y2 :: "real \<Rightarrow> real" and T :: real
  assumes T0: "0 \<le> T"
    and c11: "continuous_on {0..T} a11" and c12: "continuous_on {0..T} a12"
    and c21: "continuous_on {0..T} a21" and c22: "continuous_on {0..T} a22"
    and n12: "\<forall>t\<in>{0..T}. 0 \<le> a12 t" and n21: "\<forall>t\<in>{0..T}. 0 \<le> a21 t"
    and d1: "\<forall>t\<in>{0..T}. (y1 has_real_derivative a11 t * y1 t + a12 t * y2 t) (at t)"
    and d2: "\<forall>t\<in>{0..T}. (y2 has_real_derivative a21 t * y1 t + a22 t * y2 t) (at t)"
    and i1: "0 \<le> y1 0" and i2: "0 \<le> y2 0"
  shows "\<forall>t\<in>{0..T}. 0 \<le> y1 t \<and> 0 \<le> y2 t"
proof -
  have bd: "\<exists>B. \<forall>t\<in>{0..T}. \<bar>a t\<bar> \<le> B" if "continuous_on {0..T} a" for a :: "real \<Rightarrow> real"
  proof -
    from that have "bounded (a ` {0..T})" by (intro compact_imp_bounded compact_continuous_image) simp_all
    then obtain B where "\<forall>x\<in>a ` {0..T}. norm x \<le> B" unfolding bounded_iff by blast
    then show "\<exists>B. \<forall>t\<in>{0..T}. \<bar>a t\<bar> \<le> B" by (auto simp: real_norm_def)
  qed
  obtain B11 where b11: "\<forall>t\<in>{0..T}. \<bar>a11 t\<bar> \<le> B11" using bd[OF c11] by blast
  obtain B12 where b12: "\<forall>t\<in>{0..T}. \<bar>a12 t\<bar> \<le> B12" using bd[OF c12] by blast
  obtain B21 where b21: "\<forall>t\<in>{0..T}. \<bar>a21 t\<bar> \<le> B21" using bd[OF c21] by blast
  obtain B22 where b22: "\<forall>t\<in>{0..T}. \<bar>a22 t\<bar> \<le> B22" using bd[OF c22] by blast
  have T0m: "(0::real) \<in> {0..T}" using T0 by simp
  have p11: "0 \<le> B11" using b11 T0m by (meson abs_ge_zero order_trans)
  have p12: "0 \<le> B12" using b12 T0m by (meson abs_ge_zero order_trans)
  have p21: "0 \<le> B21" using b21 T0m by (meson abs_ge_zero order_trans)
  have p22: "0 \<le> B22" using b22 T0m by (meson abs_ge_zero order_trans)
  define K where "K = B11 + B12 + B21 + B22 + 1"
  have K1: "\<forall>t\<in>{0..T}. 0 < K - a11 t - a12 t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have "a11 t \<le> B11" using b11 t by (meson abs_ge_self order_trans)
    moreover have "a12 t \<le> B12" using b12 t by (meson abs_ge_self order_trans)
    ultimately show "0 < K - a11 t - a12 t" unfolding K_def using p21 p22 by linarith
  qed
  have K2: "\<forall>t\<in>{0..T}. 0 < K - a21 t - a22 t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have "a21 t \<le> B21" using b21 t by (meson abs_ge_self order_trans)
    moreover have "a22 t \<le> B22" using b22 t by (meson abs_ge_self order_trans)
    ultimately show "0 < K - a21 t - a22 t" unfolding K_def using p11 p12 by linarith
  qed
  have key: "\<forall>t\<in>{0..T}. 0 < y1 t + eps * exp (K * t) \<and> 0 < y2 t + eps * exp (K * t)" if ep: "0 < eps" for eps :: real
  proof -
    define f1 where "f1 = (\<lambda>t. y1 t + eps * exp (K * t))"
    define f2 where "f2 = (\<lambda>t. y2 t + eps * exp (K * t))"
    have de: "\<And>t. ((\<lambda>t. eps * exp (K * t)) has_real_derivative eps * exp (K * t) * K) (at t)"
      by (auto intro!: derivative_eq_intros)
    have hf1: "\<forall>t\<in>{0..T}. (f1 has_real_derivative
        a11 t * f1 t + a12 t * f2 t + eps * exp (K * t) * (K - a11 t - a12 t)) (at t)"
    proof
      fix t assume t: "t \<in> {0..T}"
      have "(f1 has_real_derivative (a11 t * y1 t + a12 t * y2 t) + eps * exp (K * t) * K) (at t)"
        unfolding f1_def by (rule DERIV_add[OF d1[rule_format, OF t] de])
      moreover have "(a11 t * y1 t + a12 t * y2 t) + eps * exp (K * t) * K
          = a11 t * f1 t + a12 t * f2 t + eps * exp (K * t) * (K - a11 t - a12 t)"
        unfolding f1_def f2_def by (simp add: algebra_simps)
      ultimately show "(f1 has_real_derivative
        a11 t * f1 t + a12 t * f2 t + eps * exp (K * t) * (K - a11 t - a12 t)) (at t)" by simp
    qed
    have hf2: "\<forall>t\<in>{0..T}. (f2 has_real_derivative
        a21 t * f1 t + a22 t * f2 t + eps * exp (K * t) * (K - a21 t - a22 t)) (at t)"
    proof
      fix t assume t: "t \<in> {0..T}"
      have "(f2 has_real_derivative (a21 t * y1 t + a22 t * y2 t) + eps * exp (K * t) * K) (at t)"
        unfolding f2_def by (rule DERIV_add[OF d2[rule_format, OF t] de])
      moreover have "(a21 t * y1 t + a22 t * y2 t) + eps * exp (K * t) * K
          = a21 t * f1 t + a22 t * f2 t + eps * exp (K * t) * (K - a21 t - a22 t)"
        unfolding f1_def f2_def by (simp add: algebra_simps)
      ultimately show "(f2 has_real_derivative
        a21 t * f1 t + a22 t * f2 t + eps * exp (K * t) * (K - a21 t - a22 t)) (at t)" by simp
    qed
    have cf1: "continuous_on {0..T} f1"
      by (rule continuous_at_imp_continuous_on) (use hf1 in \<open>auto intro: DERIV_isCont\<close>)
    have cf2: "continuous_on {0..T} f2"
      by (rule continuous_at_imp_continuous_on) (use hf2 in \<open>auto intro: DERIV_isCont\<close>)
    have f10: "0 < f1 0" and f20: "0 < f2 0" unfolding f1_def f2_def using i1 i2 ep by simp_all
    have main: "\<forall>t\<in>{0..T}. 0 < f1 t \<and> 0 < f2 t"
    proof (rule ccontr)
      assume "\<not> (\<forall>t\<in>{0..T}. 0 < f1 t \<and> 0 < f2 t)"
      then obtain tb where tb: "tb \<in> {0..T}" "f1 tb \<le> 0 \<or> f2 tb \<le> 0" by auto
      define S where "S = {t \<in> {0..T}. f1 t \<le> 0} \<union> {t \<in> {0..T}. f2 t \<le> 0}"
      have Sne: "S \<noteq> {}" unfolding S_def using tb by auto
      have Sbb: "bdd_below S" unfolding S_def by (intro bdd_belowI[of _ 0]) auto
      have Scl: "closed S" unfolding S_def
        by (intro closed_Un continuous_on_closed_Collect_le[OF cf1 continuous_on_const closed_atLeastAtMost]
                  continuous_on_closed_Collect_le[OF cf2 continuous_on_const closed_atLeastAtMost])
      have t0S: "Inf S \<in> S" by (rule closed_contains_Inf[OF Sne Sbb Scl])
      define t0 where "t0 = Inf S"
      have t0T: "t0 \<in> {0..T}" using t0S unfolding S_def t0_def by auto
      have t0ex: "f1 t0 \<le> 0 \<or> f2 t0 \<le> 0" using t0S unfolding S_def t0_def by auto
      have before: "\<forall>s. 0 \<le> s \<longrightarrow> s < t0 \<longrightarrow> 0 < f1 s \<and> 0 < f2 s"
      proof (intro allI impI)
        fix s assume s0: "0 \<le> s" and st: "s < t0"
        have sT: "s \<in> {0..T}" using s0 st t0T by simp
        show "0 < f1 s \<and> 0 < f2 s"
        proof (rule ccontr)
          assume "\<not> (0 < f1 s \<and> 0 < f2 s)"
          then have "s \<in> S" unfolding S_def using sT by auto
          then have "t0 \<le> s" unfolding t0_def by (rule cInf_lower[OF _ Sbb])
          then show False using st by simp
        qed
      qed
      have t0p: "0 < t0"
      proof (rule ccontr)
        assume "\<not> 0 < t0"
        then have "t0 = 0" using t0T by simp
        then show False using t0ex f10 f20 by simp
      qed
      have b1: "\<forall>s. 0 \<le> s \<longrightarrow> s < t0 \<longrightarrow> 0 < f1 s" using before by blast
      have b2: "\<forall>s. 0 \<le> s \<longrightarrow> s < t0 \<longrightarrow> 0 < f2 s" using before by blast
      have n1: "0 \<le> f1 t0" using left_nonneg[OF cf1 t0p _ b1] t0T by simp
      have n2: "0 \<le> f2 t0" using left_nonneg[OF cf2 t0p _ b2] t0T by simp
      have ee: "0 < eps * exp (K * t0)" using ep by simp
      from t0ex show False
      proof
        assume c1: "f1 t0 \<le> 0"
        then have z1: "f1 t0 = 0" using n1 by simp
        have "0 < a11 t0 * f1 t0 + a12 t0 * f2 t0 + eps * exp (K * t0) * (K - a11 t0 - a12 t0)"
        proof -
          have "0 \<le> a12 t0" using n12 t0T by blast
          then have "0 \<le> a12 t0 * f2 t0" using n2 by (intro mult_nonneg_nonneg)
          moreover have "0 < eps * exp (K * t0) * (K - a11 t0 - a12 t0)"
            by (rule mult_pos_pos[OF ee]) (use K1 t0T in blast)
          ultimately show ?thesis using z1 by simp
        qed
        then show False using exit_contra[OF hf1[rule_format, OF t0T] _ c1 t0p b1] by blast
      next
        assume c2: "f2 t0 \<le> 0"
        then have z2: "f2 t0 = 0" using n2 by simp
        have "0 < a21 t0 * f1 t0 + a22 t0 * f2 t0 + eps * exp (K * t0) * (K - a21 t0 - a22 t0)"
        proof -
          have "0 \<le> a21 t0" using n21 t0T by blast
          then have "0 \<le> a21 t0 * f1 t0" using n1 by (intro mult_nonneg_nonneg)
          moreover have "0 < eps * exp (K * t0) * (K - a21 t0 - a22 t0)"
            by (rule mult_pos_pos[OF ee]) (use K2 t0T in blast)
          ultimately show ?thesis using z2 by simp
        qed
        then show False using exit_contra[OF hf2[rule_format, OF t0T] _ c2 t0p b2] by blast
      qed
    qed
    then show "\<forall>t\<in>{0..T}. 0 < y1 t + eps * exp (K * t) \<and> 0 < y2 t + eps * exp (K * t)"
      unfolding f1_def f2_def by simp
  qed
  show ?thesis
  proof (intro ballI conjI)
    fix t assume t: "t \<in> {0..T}"
    show "0 \<le> y1 t"
    proof (rule ccontr)
      assume "\<not> 0 \<le> y1 t"
      then have neg: "y1 t < 0" by simp
      define eps where "eps = - y1 t / (2 * exp (K * t))"
      have ep: "0 < eps" unfolding eps_def by (intro divide_pos_pos) (use neg in simp_all)
      have "eps * exp (K * t) = - y1 t / 2" unfolding eps_def by simp
      then have "y1 t + eps * exp (K * t) = y1 t / 2" by simp
      moreover have "0 < y1 t + eps * exp (K * t)" using key[OF ep] t by blast
      ultimately show False using neg by simp
    qed
    show "0 \<le> y2 t"
    proof (rule ccontr)
      assume "\<not> 0 \<le> y2 t"
      then have neg: "y2 t < 0" by simp
      define eps where "eps = - y2 t / (2 * exp (K * t))"
      have ep: "0 < eps" unfolding eps_def by (intro divide_pos_pos) (use neg in simp_all)
      have "eps * exp (K * t) = - y2 t / 2" unfolding eps_def by simp
      then have "y2 t + eps * exp (K * t) = y2 t / 2" by simp
      moreover have "0 < y2 t + eps * exp (K * t)" using key[OF ep] t by blast
      ultimately show False using neg by simp
    qed
  qed
qed

section \<open>C. A ratio whose logarithmic derivative is non-positive\<close>

theorem ratio_nonincreasing:
  fixes N D N' D' :: "real \<Rightarrow> real" and T :: real
  assumes T0: "0 \<le> T"
    and dN: "\<forall>t\<in>{0..T}. (N has_real_derivative N' t) (at t)"
    and dD: "\<forall>t\<in>{0..T}. (D has_real_derivative D' t) (at t)"
    and Dp: "\<forall>t\<in>{0..T}. 0 < D t"
    and lg: "\<forall>t\<in>{0..T}. N' t * D t \<le> N t * D' t"
  shows "N T / D T \<le> N 0 / D 0"
proof (rule DERIV_nonpos_imp_nonincreasing[OF T0, of "\<lambda>t. N t / D t"])
  fix t :: real
  assume t: "0 \<le> t" "t \<le> T"
  then have tm: "t \<in> {0..T}" by simp
  have "0 < D t" using Dp tm by blast
  then have dp: "D t \<noteq> 0" by simp
  have "((\<lambda>t. N t / D t) has_real_derivative (N' t * D t - N t * D' t) / (D t)\<^sup>2) (at t)"
    using DERIV_divide[OF dN[rule_format, OF tm] dD[rule_format, OF tm] dp] by (simp add: power2_eq_square)
  moreover have "(N' t * D t - N t * D' t) / (D t)\<^sup>2 \<le> 0"
  proof -
    have n: "N' t * D t - N t * D' t \<le> 0" using lg tm by force
    have "0 \<le> (D t)\<^sup>2" by simp
    then show ?thesis using n by (simp add: divide_le_0_iff)
  qed
  ultimately show "\<exists>d. DERIV (\<lambda>t. N t / D t) t :> d \<and> d \<le> 0" by blast
qed

end
