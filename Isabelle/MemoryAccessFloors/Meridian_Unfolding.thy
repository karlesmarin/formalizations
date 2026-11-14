(*  Title:      Meridian_Unfolding.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD
*)

section \<open>Unfolding a piecewise meridian curve onto one plane\<close>

text \<open>
  Setting: the U-turn curve of the memory-floor problem.  A tangent curve n on the unit sphere with speed at
  most nu (locale @{text sphere_curve} of Robust_Core) goes from the north pole to the south pole, and its
  position r(t) = int_0^t n ends on the axis.  Suppose [0,T] is cut into k pieces
  0 = ts 0 < ... < ts k = T and that, on piece j, both n and r lie in the meridian plane of angle ph j
  (a plane containing the axis e3).  If consecutive planes differ, the junctions are on the axis and the curve
  folds, piece by piece, onto the plane x2 = 0: m = Rot(-ph j) n on piece j is again a curve of the same
  locale, lies in the plane x2 = 0 and has the same total displacement.
\<close>

theory Meridian_Unfolding
  imports Robust_Core
begin

section \<open>A. Rotations about the axis e3 and meridian planes\<close>

definition rot :: "real \<Rightarrow> real^3 \<Rightarrow> real^3" where
  "rot a v = vector [cos a * v $ 1 - sin a * v $ 2, sin a * v $ 1 + cos a * v $ 2, v $ 3]"

text \<open>@{text "pln a v = 0"} says that v lies in the meridian plane of angle a, the plane spanned by
  (cos a, sin a, 0) and e3.\<close>

definition pln :: "real \<Rightarrow> real^3 \<Rightarrow> real" where
  "pln a v = - sin a * v $ 1 + cos a * v $ 2"

lemma rot_1 [simp]: "rot a v $ 1 = cos a * v $ 1 - sin a * v $ 2"
  by (simp add: rot_def)

lemma rot_2 [simp]: "rot a v $ 2 = sin a * v $ 1 + cos a * v $ 2"
  by (simp add: rot_def)

lemma rot_3 [simp]: "rot a v $ 3 = v $ 3"
  by (simp add: rot_def)

lemma rot_linear: "linear (rot a)"
  unfolding linear_iff by (simp add: vec_eq_iff forall_3 algebra_simps)

lemma rot_bounded: "bounded_linear (rot a)"
  using rot_linear by (simp add: linear_conv_bounded_linear)

lemma rot_inner: "inner (rot a v) (rot a w) = inner v w"
proof -
  have p: "inner (rot a v) (rot a w) = (cos a * v $ 1 - sin a * v $ 2) * (cos a * w $ 1 - sin a * w $ 2)
      + (sin a * v $ 1 + cos a * v $ 2) * (sin a * w $ 1 + cos a * w $ 2) + v $ 3 * w $ 3"
    by (simp add: inner_vec_def sum_3)
  have sc: "sin a * sin a + cos a * cos a = 1"
    using sin_cos_squared_add[of a] by (simp add: power2_eq_square)
  have i: "inner v w = (v $ 1 * w $ 1 + v $ 2 * w $ 2) + v $ 3 * w $ 3"
    by (simp add: inner_vec_def sum_3)
  show ?thesis unfolding p i using sc by algebra
qed

lemma rot_norm: "norm (rot a v) = norm v"
  by (simp add: norm_eq_sqrt_inner rot_inner)

lemma rot_axis:
  assumes "v $ 1 = 0" "v $ 2 = 0"
  shows "rot a v = v"
  using assms by (simp add: vec_eq_iff forall_3)

lemma pln_rot: "rot (- a) v $ 2 = pln a v"
  by (simp add: pln_def)

lemma pln_inner: "pln a v = inner v (vector [- sin a, cos a, 0])"
  by (simp add: pln_def inner_vec_def sum_3)

text \<open>A vector lying in two different meridian planes lies on the axis.\<close>

lemma two_planes:
  assumes "sin (a - b) \<noteq> 0" "pln a v = 0" "pln b v = 0"
  shows "v $ 1 = 0 \<and> v $ 2 = 0"
proof -
  have e1: "sin a * v $ 1 - cos a * v $ 2 = 0" using assms(2) unfolding pln_def by linarith
  have e2: "sin b * v $ 1 - cos b * v $ 2 = 0" using assms(3) unfolding pln_def by linarith
  have x1: "v $ 1 * sin (a - b) =
      cos b * (sin a * v $ 1 - cos a * v $ 2) - cos a * (sin b * v $ 1 - cos b * v $ 2)"
    by (simp add: sin_diff algebra_simps)
  have x2: "v $ 2 * sin (a - b) =
      sin a * (cos b * v $ 2 - sin b * v $ 1) - sin b * (cos a * v $ 2 - sin a * v $ 1)"
    by (simp add: sin_diff algebra_simps)
  have "v $ 1 * sin (a - b) = 0" using x1 e1 e2 by simp
  moreover have "v $ 2 * sin (a - b) = 0"
  proof -
    have "cos b * v $ 2 - sin b * v $ 1 = 0" using e2 by linarith
    moreover have "cos a * v $ 2 - sin a * v $ 1 = 0" using e1 by linarith
    ultimately show ?thesis using x2 by simp
  qed
  ultimately show ?thesis using assms(1) by simp
qed

section \<open>B. A function that vanishes on one side has zero derivative there\<close>

lemma real_deriv_zero_left:
  fixes g :: "real \<Rightarrow> real"
  assumes d: "(g has_real_derivative l) (at x)" and ax: "a < x"
    and z: "\<And>y. a \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> g y = 0"
  shows "l = 0"
proof (rule ccontr)
  assume "l \<noteq> 0"
  then consider "0 < l" | "l < 0" by linarith
  then show False
  proof cases
    case 1
    obtain d0 where d0: "0 < d0" and dd: "\<forall>h>0. h < d0 \<longrightarrow> g (x - h) < g x"
      using DERIV_pos_inc_left[OF d 1] by blast
    define h where "h = min d0 (x - a) / 2"
    have h0: "0 < h" "h < d0" "h < x - a" unfolding h_def using d0 ax by auto
    have "g (x - h) = 0" using z h0 by auto
    moreover have "g x = 0" using z ax by auto
    ultimately show False using dd h0 by auto
  next
    case 2
    obtain d0 where d0: "0 < d0" and dd: "\<forall>h>0. h < d0 \<longrightarrow> g x < g (x - h)"
      using DERIV_neg_dec_left[OF d 2] by blast
    define h where "h = min d0 (x - a) / 2"
    have h0: "0 < h" "h < d0" "h < x - a" unfolding h_def using d0 ax by auto
    have "g (x - h) = 0" using z h0 by auto
    moreover have "g x = 0" using z ax by auto
    ultimately show False using dd h0 by auto
  qed
qed

lemma real_deriv_zero_right:
  fixes g :: "real \<Rightarrow> real"
  assumes d: "(g has_real_derivative l) (at x)" and xb: "x < b"
    and z: "\<And>y. x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g y = 0"
  shows "l = 0"
proof (rule ccontr)
  assume "l \<noteq> 0"
  then consider "0 < l" | "l < 0" by linarith
  then show False
  proof cases
    case 1
    obtain d0 where d0: "0 < d0" and dd: "\<forall>h>0. h < d0 \<longrightarrow> g x < g (x + h)"
      using DERIV_pos_inc_right[OF d 1] by blast
    define h where "h = min d0 (b - x) / 2"
    have h0: "0 < h" "h < d0" "h < b - x" unfolding h_def using d0 xb by auto
    have "g (x + h) = 0" using z h0 by auto
    moreover have "g x = 0" using z xb by auto
    ultimately show False using dd h0 by auto
  next
    case 2
    obtain d0 where d0: "0 < d0" and dd: "\<forall>h>0. h < d0 \<longrightarrow> g (x + h) < g x"
      using DERIV_neg_dec_right[OF d 2] by blast
    define h where "h = min d0 (b - x) / 2"
    have h0: "0 < h" "h < d0" "h < b - x" unfolding h_def using d0 xb by auto
    have "g (x + h) = 0" using z h0 by auto
    moreover have "g x = 0" using z xb by auto
    ultimately show False using dd h0 by auto
  qed
qed

text \<open>If g and f are at the same distance from their values at t, in a neighbourhood, and f has zero
  derivative at t, so has g.  This is what makes the folded curve differentiable at a junction.\<close>

lemma has_deriv_zero_transfer:
  fixes f g :: "real \<Rightarrow> real^3"
  assumes "(f has_derivative (\<lambda>h. 0)) (at t)" and "0 < d"
    and "\<And>y. dist y t < d \<Longrightarrow> norm (g y - g t) = norm (f y - f t)"
  shows "(g has_derivative (\<lambda>h. 0)) (at t)"
proof -
  have f0: "((\<lambda>y. norm (f y - f t) / norm (y - t)) \<longlongrightarrow> 0) (at t)"
    using assms(1) by (simp add: has_derivative_iff_norm)
  have ev: "eventually (\<lambda>y. norm (f y - f t) / norm (y - t) = norm (g y - g t) / norm (y - t)) (at t)"
    unfolding eventually_at using assms(2,3) by (auto intro!: exI[of _ d])
  have "((\<lambda>y. norm (g y - g t) / norm (y - t)) \<longlongrightarrow> 0) (at t)"
    by (rule Lim_transform_eventually[OF f0 ev])
  then show ?thesis by (simp add: has_derivative_iff_norm)
qed

section \<open>C. The locale of a piecewise meridian curve\<close>

text \<open>Pieces are numbered 0 .. k-1; piece j is the interval [ts j, ts (Suc j)] and lies in the meridian
  plane of angle ph j.  The position is r(t) = integral {0..t} n.  The hypotheses are exactly those of the
  statement: n and r lie in the plane of the piece, for every t of the closed interval; consecutive planes
  are different (sin of the angle difference non-zero); and the position at the end of the curve is on the
  axis (the datum r(T) = s e3).\<close>

locale meridian_curve = sphere_curve n n' T nu
  for n n' :: "real \<Rightarrow> real^3" and T nu :: real +
  fixes ts ph :: "nat \<Rightarrow> real" and k :: nat
  assumes k_pos: "0 < k"
    and ts_0: "ts 0 = 0" and ts_k: "ts k = T"
    and ts_mono: "\<And>j. j < k \<Longrightarrow> ts j < ts (Suc j)"
    and plane_n: "\<And>j t. j < k \<Longrightarrow> ts j \<le> t \<Longrightarrow> t \<le> ts (Suc j) \<Longrightarrow> pln (ph j) (n t) = 0"
    and plane_r: "\<And>j t. j < k \<Longrightarrow> ts j \<le> t \<Longrightarrow> t \<le> ts (Suc j) \<Longrightarrow>
      pln (ph j) (integral {0..t} n) = 0"
    and distinct: "\<And>j. Suc j < k \<Longrightarrow> sin (ph j - ph (Suc j)) \<noteq> 0"
    and axis_end: "integral {0..T} n $ 1 = 0" "integral {0..T} n $ 2 = 0"
begin

definition seg :: "real \<Rightarrow> nat" where
  "seg t = (LEAST j. t \<le> ts (Suc j))"

definition m :: "real \<Rightarrow> real^3" where
  "m t = rot (- ph (seg t)) (n t)"

definition m' :: "real \<Rightarrow> real^3" where
  "m' t = rot (- ph (seg t)) (n' t)"

subsection \<open>The partition\<close>

lemma ts_less:
  assumes "i < j" "j \<le> k"
  shows "ts i < ts j"
  using assms
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have jk: "j < k" using Suc.prems(2) by simp
  have s1: "ts j < ts (Suc j)" by (rule ts_mono[OF jk])
  show ?case
  proof (cases "i < j")
    case True
    then have "ts i < ts j" using Suc.IH jk by simp
    then show ?thesis using s1 by linarith
  next
    case False
    then have "i = j" using Suc.prems(1) by simp
    then show ?thesis using s1 by simp
  qed
qed

lemma ts_le:
  assumes "i \<le> j" "j \<le> k"
  shows "ts i \<le> ts j"
proof (cases "i = j")
  case True
  then show ?thesis by simp
next
  case False
  then have "i < j" using assms(1) by simp
  then show ?thesis using ts_less assms(2) by fastforce
qed

lemma ts_range:
  assumes "j \<le> k"
  shows "0 \<le> ts j" "ts j \<le> T"
proof -
  have "ts 0 \<le> ts j" by (rule ts_le[OF _ assms]) simp
  then show "0 \<le> ts j" using ts_0 by simp
  have "ts j \<le> ts k" by (rule ts_le[OF assms order_refl])
  then show "ts j \<le> T" using ts_k by simp
qed

lemma seg_props:
  assumes t: "0 \<le> t" "t \<le> T"
  shows "seg t < k" "ts (seg t) \<le> t" "t \<le> ts (Suc (seg t))" "0 < t \<Longrightarrow> ts (seg t) < t"
proof -
  have ex: "t \<le> ts (Suc (k - 1))"
  proof -
    have "Suc (k - 1) = k" using k_pos by (cases k) simp_all
    then show ?thesis using ts_k t by simp
  qed
  have s3: "t \<le> ts (Suc (seg t))"
    unfolding seg_def by (rule LeastI[of "\<lambda>j. t \<le> ts (Suc j)" "k - 1", OF ex])
  have s1: "seg t \<le> k - 1"
    unfolding seg_def by (rule Least_le[of "\<lambda>j. t \<le> ts (Suc j)" "k - 1", OF ex])
  show "seg t < k" using s1 k_pos by simp
  show "t \<le> ts (Suc (seg t))" by (rule s3)
  have pos: "ts (seg t) < t" if "0 < t"
  proof (cases "seg t")
    case 0
    then show ?thesis using ts_0 that by simp
  next
    case (Suc j)
    have "\<not> t \<le> ts (Suc j)"
      using not_less_Least[of j "\<lambda>j. t \<le> ts (Suc j)"] Suc unfolding seg_def by simp
    then show ?thesis using Suc by (simp add: seg_def not_le)
  qed
  show "0 < t \<Longrightarrow> ts (seg t) < t" using pos by simp
  show "ts (seg t) \<le> t"
  proof (cases "t = 0")
    case True
    have "seg t = 0"
    proof -
      have "seg t \<le> 0"
        unfolding seg_def by (rule Least_le[of "\<lambda>j. t \<le> ts (Suc j)" 0])
          (use True ts_range[of "Suc 0"] k_pos in auto)
      then show ?thesis by simp
    qed
    then show ?thesis using True ts_0 by simp
  next
    case False
    then have "0 < t" using t(1) by simp
    then show ?thesis using pos by simp
  qed
qed

subsection \<open>The junctions lie on the axis\<close>

lemma junction_n:
  assumes "Suc j < k"
  shows "n (ts (Suc j)) $ 1 = 0" "n (ts (Suc j)) $ 2 = 0"
proof -
  have jk: "j < k" using assms by simp
  have a: "pln (ph j) (n (ts (Suc j))) = 0"
    by (rule plane_n[OF jk]) (use ts_mono[OF jk] in auto)
  have b: "pln (ph (Suc j)) (n (ts (Suc j))) = 0"
    by (rule plane_n[OF assms]) (use ts_mono[OF assms] in auto)
  have "n (ts (Suc j)) $ 1 = 0 \<and> n (ts (Suc j)) $ 2 = 0"
    by (rule two_planes[OF distinct[OF assms] a b])
  then show "n (ts (Suc j)) $ 1 = 0" "n (ts (Suc j)) $ 2 = 0" by simp_all
qed

lemma junction_r:
  assumes "Suc j < k"
  shows "integral {0..ts (Suc j)} n $ 1 = 0" "integral {0..ts (Suc j)} n $ 2 = 0"
proof -
  have jk: "j < k" using assms by simp
  have a: "pln (ph j) (integral {0..ts (Suc j)} n) = 0"
    by (rule plane_r[OF jk]) (use ts_mono[OF jk] in auto)
  have b: "pln (ph (Suc j)) (integral {0..ts (Suc j)} n) = 0"
    by (rule plane_r[OF assms]) (use ts_mono[OF assms] in auto)
  have "integral {0..ts (Suc j)} n $ 1 = 0 \<and> integral {0..ts (Suc j)} n $ 2 = 0"
    by (rule two_planes[OF distinct[OF assms] a b])
  then show "integral {0..ts (Suc j)} n $ 1 = 0" "integral {0..ts (Suc j)} n $ 2 = 0" by simp_all
qed

lemma axis_r:
  assumes "j \<le> k"
  shows "integral {0..ts j} n $ 1 = 0 \<and> integral {0..ts j} n $ 2 = 0"
proof (cases j)
  case 0
  then show ?thesis by (simp add: ts_0)
next
  case (Suc i)
  show ?thesis
  proof (cases "j = k")
    case True
    then show ?thesis using axis_end ts_k by simp
  next
    case False
    then have ik: "Suc i < k" using Suc assms by simp
    have "integral {0..ts (Suc i)} n $ 1 = 0" "integral {0..ts (Suc i)} n $ 2 = 0"
      by (rule junction_r[OF ik])+
    then show ?thesis using Suc by simp
  qed
qed

lemma tramo_agree:
  assumes "s < k" "j < k" "ts s \<le> t" "t \<le> ts (Suc s)" "ts j \<le> t" "t \<le> ts (Suc j)"
  shows "rot (- ph s) (n t) = rot (- ph j) (n t)"
proof -
  have on_axis: "n t $ 1 = 0 \<and> n t $ 2 = 0" if "a < b" "a < k" "b < k" "ts a \<le> t" "t \<le> ts (Suc a)"
      "ts b \<le> t" "t \<le> ts (Suc b)" for a b t
  proof -
    have "Suc a \<le> b" using that(1) by simp
    have "Suc a = b"
    proof (rule ccontr)
      assume "Suc a \<noteq> b"
      then have "Suc a < b" using \<open>Suc a \<le> b\<close> by simp
      then have "ts (Suc a) < ts b" using ts_less that(3) by simp
      then show False using that(5,6) by linarith
    qed
    then have "t = ts b" using that(5,6,7) by (simp add: ts_le)
    have "Suc a < k" using \<open>Suc a = b\<close> that(3) by simp
    then have j: "n (ts (Suc a)) $ 1 = 0" "n (ts (Suc a)) $ 2 = 0" using junction_n by blast+
    show ?thesis using j \<open>t = ts b\<close> \<open>Suc a = b\<close> by simp
  qed
  show ?thesis
  proof (cases "s = j")
    case True
    then show ?thesis by simp
  next
    case False
    then have ax: "n t $ 1 = 0 \<and> n t $ 2 = 0"
    proof (cases "s < j")
      case True
      show ?thesis by (rule on_axis[OF True assms(1,2,3,4,5,6)])
    next
      case False
      then have "j < s" using \<open>s \<noteq> j\<close> by simp
      show ?thesis by (rule on_axis[OF \<open>j < s\<close> assms(2,1,5,6,3,4)])
    qed
    then show ?thesis using rot_axis by simp
  qed
qed

lemma m_tramo:
  assumes "j < k" "ts j \<le> t" "t \<le> ts (Suc j)"
  shows "m t = rot (- ph j) (n t)"
proof -
  have t: "0 \<le> t" "t \<le> T"
    using ts_range[of j] ts_range[of "Suc j"] assms by auto
  show ?thesis unfolding m_def
    by (rule tramo_agree[OF seg_props(1)[OF t] assms(1) seg_props(2)[OF t] seg_props(3)[OF t] assms(2,3)])
qed

subsection \<open>Derivatives of n at a junction\<close>

lemma pln_derivative:
  assumes "0 < t" "t < T"
  shows "((\<lambda>x. pln a (n x)) has_real_derivative pln a (n' t)) (at t)"
  using u_derivative[OF assms, of "vector [- sin a, cos a, 0]"] by (simp add: pln_inner)

lemma n'_junction:
  assumes "Suc s < k"
  shows "n' (ts (Suc s)) = 0"
proof -
  define t0 where "t0 = ts (Suc s)"
  have sk: "s < k" using assms by simp
  have t0: "0 < t0" "t0 < T"
  proof -
    have "ts s < ts (Suc s)" by (rule ts_mono[OF sk])
    then show "0 < t0" using ts_range[of s] sk unfolding t0_def by simp
    have "ts (Suc s) < ts k" by (rule ts_less[OF assms order_refl])
    then show "t0 < T" using ts_k unfolding t0_def by simp
  qed
  have z1: "pln (ph s) (n' t0) = 0"
  proof (rule real_deriv_zero_left[OF pln_derivative[OF t0]])
    show "ts s < t0" unfolding t0_def by (rule ts_mono[OF sk])
    show "pln (ph s) (n y) = 0" if "ts s \<le> y" "y \<le> t0" for y
      by (rule plane_n[OF sk that(1)]) (use that(2) in \<open>simp add: t0_def\<close>)
  qed
  have z2: "pln (ph (Suc s)) (n' t0) = 0"
  proof (rule real_deriv_zero_right[OF pln_derivative[OF t0]])
    show "t0 < ts (Suc (Suc s))" unfolding t0_def by (rule ts_mono[OF assms])
    show "pln (ph (Suc s)) (n y) = 0" if "t0 \<le> y" "y \<le> ts (Suc (Suc s))" for y
      by (rule plane_n[OF assms _ that(2)]) (use that(1) in \<open>simp add: t0_def\<close>)
  qed
  have xy: "n' t0 $ 1 = 0 \<and> n' t0 $ 2 = 0" by (rule two_planes[OF distinct[OF assms] z1 z2])
  have n12: "n t0 $ 1 = 0" "n t0 $ 2 = 0" using junction_n[OF assms] unfolding t0_def by simp_all
  have n3: "(n t0 $ 3)\<^sup>2 = 1" using norm3[of t0] t0 n12 by simp
  have o: "inner (n t0) (n' t0) = 0" using orth[OF t0] by simp
  have "n t0 $ 3 * n' t0 $ 3 = 0" using o n12 by (simp add: inner_vec_def sum_3)
  moreover have "n t0 $ 3 \<noteq> 0" using n3 by auto
  ultimately have "n' t0 $ 3 = 0" by simp
  then show ?thesis using xy unfolding t0_def by (simp add: vec_eq_iff forall_3)
qed

subsection \<open>The folded curve is continuous, unit, planar and has the same displacement\<close>

lemma cont_m_upto:
  assumes "j \<le> k"
  shows "continuous_on {0..ts j} m"
  using assms
proof (induction j)
  case 0
  then show ?case by (simp add: ts_0)
next
  case (Suc j)
  have jk: "j < k" using Suc.prems by simp
  have c1: "continuous_on {0..ts j} m" using Suc.IH jk by simp
  have rng: "0 \<le> ts j" "ts j \<le> ts (Suc j)" "ts (Suc j) \<le> T"
    using ts_range[of j] ts_range[of "Suc j"] ts_mono[OF jk] jk by auto
  have cn: "continuous_on {ts j..ts (Suc j)} n"
    by (rule continuous_on_subset[OF cont]) (use rng in auto)
  have cr: "continuous_on {ts j..ts (Suc j)} (\<lambda>t. rot (- ph j) (n t))"
    by (rule continuous_on_compose2[OF linear_continuous_on[OF rot_bounded] cn subset_UNIV])
  have c2: "continuous_on {ts j..ts (Suc j)} m"
    by (rule continuous_on_eq[OF cr]) (use m_tramo[OF jk] in auto)
  have un: "{0..ts (Suc j)} = {0..ts j} \<union> {ts j..ts (Suc j)}" using rng by auto
  show ?case unfolding un by (rule continuous_on_closed_Un[OF closed_atLeastAtMost closed_atLeastAtMost c1 c2])
qed

lemma cont_m: "continuous_on {0..T} m"
  using cont_m_upto[of k] ts_k k_pos by simp

lemma norm_m:
  assumes "0 \<le> t" "t \<le> T"
  shows "norm (m t) = 1"
  using unit[OF assms] by (simp add: m_def rot_norm)

lemma plane_m:
  assumes "0 \<le> t" "t \<le> T"
  shows "m t $ 2 = 0"
proof -
  have "m t $ 2 = pln (ph (seg t)) (n t)" unfolding m_def by (rule pln_rot)
  also have "\<dots> = 0"
    by (rule plane_n[OF seg_props(1)[OF assms] seg_props(2)[OF assms] seg_props(3)[OF assms]])
  finally show ?thesis .
qed

lemma m_north: "m 0 = axis 3 1"
proof -
  have a: "(axis 3 (1::real) :: real^3) $ 1 = 0" "(axis 3 (1::real) :: real^3) $ 2 = 0"
    by (simp_all add: axis_def)
  show ?thesis unfolding m_def north using rot_axis[OF a] .
qed

lemma m_south: "m T = - axis 3 1"
proof -
  have a: "(- axis 3 (1::real) :: real^3) $ 1 = 0" "(- axis 3 (1::real) :: real^3) $ 2 = 0"
    by (simp_all add: axis_def)
  show ?thesis unfolding m_def south using rot_axis[OF a] .
qed

lemma int_m_upto:
  assumes "j \<le> k"
  shows "integral {0..ts j} m = integral {0..ts j} n"
  using assms
proof (induction j)
  case 0
  then show ?case by (simp add: ts_0)
next
  case (Suc j)
  have jk: "j < k" using Suc.prems by simp
  have rng: "0 \<le> ts j" "ts j \<le> ts (Suc j)" "ts (Suc j) \<le> T"
    using ts_range[of j] ts_range[of "Suc j"] ts_mono[OF jk] jk by auto
  have im: "m integrable_on {0..ts (Suc j)}"
    by (rule integrable_continuous_real, rule continuous_on_subset[OF cont_m]) (use rng in auto)
  have in_: "n integrable_on {0..ts (Suc j)}"
    by (rule integrable_continuous_real, rule continuous_on_subset[OF cont]) (use rng in auto)
  have in2: "n integrable_on {ts j..ts (Suc j)}"
    by (rule integrable_continuous_real, rule continuous_on_subset[OF cont]) (use rng in auto)
  have cm: "integral {0..ts j} m + integral {ts j..ts (Suc j)} m = integral {0..ts (Suc j)} m"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF rng(1) rng(2) im])
  have cn: "integral {0..ts j} n + integral {ts j..ts (Suc j)} n = integral {0..ts (Suc j)} n"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF rng(1) rng(2) in_])
  have d12: "integral {ts j..ts (Suc j)} n $ 1 = 0" "integral {ts j..ts (Suc j)} n $ 2 = 0"
  proof -
    have e: "integral {ts j..ts (Suc j)} n = integral {0..ts (Suc j)} n - integral {0..ts j} n"
      by (simp add: cn[symmetric])
    show "integral {ts j..ts (Suc j)} n $ 1 = 0" "integral {ts j..ts (Suc j)} n $ 2 = 0"
      using e axis_r[of j] axis_r[of "Suc j"] Suc.prems jk by auto
  qed
  have tram: "integral {ts j..ts (Suc j)} m = integral {ts j..ts (Suc j)} n"
  proof -
    have "integral {ts j..ts (Suc j)} m = integral {ts j..ts (Suc j)} (\<lambda>t. rot (- ph j) (n t))"
      by (rule integral_cong) (use m_tramo[OF jk] in auto)
    also have "\<dots> = integral {ts j..ts (Suc j)} (rot (- ph j) \<circ> n)" by (simp add: o_def)
    also have "\<dots> = rot (- ph j) (integral {ts j..ts (Suc j)} n)"
      by (rule integral_linear[OF in2 rot_bounded])
    also have "\<dots> = integral {ts j..ts (Suc j)} n" by (rule rot_axis[OF d12])
    finally show ?thesis .
  qed
  show ?case using Suc.IH jk cm cn tram by simp
qed

lemma int_m: "integral {0..T} m = integral {0..T} n"
  using int_m_upto[of k] ts_k k_pos by simp

subsection \<open>Derivative of the folded curve\<close>

lemma m_derivative:
  assumes t: "0 < t" "t < T"
  shows "(m has_vector_derivative m' t) (at t)" "norm (m' t) \<le> nu"
proof -
  have t0: "0 \<le> t" "t \<le> T" using t by simp_all
  define s where "s = seg t"
  have sk: "s < k" and s1: "ts s < t" and s2: "t \<le> ts (Suc s)"
    using seg_props(1,3,4)[OF t0] t(1) unfolding s_def by simp_all
  have nrm: "norm (m' t) = norm (n' t)" unfolding m'_def by (simp add: rot_norm)
  show "norm (m' t) \<le> nu" using nrm speed[OF t] by simp
  have D: "(n has_derivative (\<lambda>h. h *\<^sub>R n' t)) (at t)"
    using der[OF t] by (simp add: has_vector_derivative_def)
  have rs: "m' t = rot (- ph s) (n' t)" unfolding m'_def s_def by simp
  show "(m has_vector_derivative m' t) (at t)"
  proof (cases "t < ts (Suc s)")
    case True
    have D2: "((\<lambda>x. rot (- ph s) (n x)) has_derivative (\<lambda>h. h *\<^sub>R rot (- ph s) (n' t))) (at t)"
    proof -
      have "((\<lambda>x. rot (- ph s) (n x)) has_derivative (\<lambda>h. rot (- ph s) (h *\<^sub>R n' t))) (at t)"
        by (rule bounded_linear.has_derivative[OF rot_bounded D])
      moreover have "(\<lambda>h. rot (- ph s) (h *\<^sub>R n' t)) = (\<lambda>h. h *\<^sub>R rot (- ph s) (n' t))"
        by (rule ext) (simp add: linear.scaleR[OF rot_linear])
      ultimately show ?thesis by simp
    qed
    have eq: "\<And>y. y \<in> {ts s<..<ts (Suc s)} \<Longrightarrow> rot (- ph s) (n y) = m y"
      using m_tramo[OF sk] by auto
    have "(m has_derivative (\<lambda>h. h *\<^sub>R rot (- ph s) (n' t))) (at t)"
      by (rule has_derivative_transform_within_open[OF D2 open_greaterThanLessThan _ eq])
        (use s1 True in auto)
    then show ?thesis unfolding has_vector_derivative_def rs .
  next
    case False
    then have tE: "t = ts (Suc s)" using s2 by simp
    have sk1: "Suc s < k"
    proof (rule ccontr)
      assume "\<not> Suc s < k"
      then have "Suc s = k" using sk by simp
      then show False using tE ts_k t(2) by simp
    qed
    have n0: "n' t = 0" using n'_junction[OF sk1] tE by simp
    have m0: "m' t = 0" using rs n0 by (simp add: linear_0[OF rot_linear])
    have Dn: "(n has_derivative (\<lambda>h. 0)) (at t)" using D n0 by simp
    define dl where "dl = min (t - ts s) (ts (Suc (Suc s)) - t)"
    have dl0: "0 < dl"
      unfolding dl_def using s1 tE ts_mono[OF sk1] by simp
    have dist: "norm (m y - m t) = norm (n y - n t)" if "dist y t < dl" for y
    proof -
      have yl: "ts s < y" "y < ts (Suc (Suc s))" using that unfolding dl_def dist_real_def by auto
      have mt: "m t = rot (- ph s) (n t)" by (rule m_tramo[OF sk _ s2]) (use s1 in simp)
      show ?thesis
      proof (cases "y \<le> t")
        case True
        have "m y = rot (- ph s) (n y)" by (rule m_tramo[OF sk _ _]) (use yl True tE in auto)
        then show ?thesis using mt rot_norm linear_diff[OF rot_linear] by metis
      next
        case False
        have "m y = rot (- ph (Suc s)) (n y)"
          by (rule m_tramo[OF sk1]) (use yl False tE in auto)
        moreover have "m t = rot (- ph (Suc s)) (n t)" by (rule m_tramo[OF sk1]) (use tE ts_mono[OF sk1] in auto)
        ultimately show ?thesis using rot_norm linear_diff[OF rot_linear] by metis
      qed
    qed
    have "(m has_derivative (\<lambda>h. 0)) (at t)" by (rule has_deriv_zero_transfer[OF Dn dl0 dist])
    then show ?thesis unfolding has_vector_derivative_def m0 by simp
  qed
qed

subsection \<open>Main theorem\<close>

theorem folded_curve: "sphere_curve m m' T nu"
proof (unfold_locales)
  show "0 < nu" by (rule nu_pos)
  show "continuous_on {0..T} m" by (rule cont_m)
  show "(m has_vector_derivative m' t) (at t)" if "0 < t" "t < T" for t
    using m_derivative(1)[OF that] .
  show "norm (m t) = 1" if "0 \<le> t" "t \<le> T" for t by (rule norm_m[OF that])
  show "norm (m' t) \<le> nu" if "0 < t" "t < T" for t using m_derivative(2)[OF that] .
  show "0 < T" by (rule T_pos)
  show "m 0 = axis 3 1" by (rule m_north)
  show "m T = - axis 3 1" by (rule m_south)
qed

theorem folded_planar: "0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> m t $ 2 = 0"
  by (rule plane_m)

theorem folded_displacement: "integral {0..T} m = integral {0..T} n"
  by (rule int_m)

text \<open>The position of the folded curve, rho(t) = int_0^t m, is a plane curve (it lies in x2 = 0).\<close>

theorem folded_position_planar:
  assumes "0 \<le> t" "t \<le> T"
  shows "integral {0..t} m $ 2 = 0"
proof -
  have im: "m integrable_on {0..t}"
    by (rule integrable_continuous_real, rule continuous_on_subset[OF cont_m]) (use assms in auto)
  have bl: "bounded_linear (\<lambda>v::real^3. v $ 2)"
    using linear_conv_bounded_linear[of "\<lambda>v::real^3. v $ 2"] by (simp add: linear_iff)
  have h: "((\<lambda>x. m x $ 2) has_integral (integral {0..t} m $ 2)) {0..t}"
    using has_integral_linear[OF integrable_integral[OF im] bl] by (simp add: o_def)
  have z: "((\<lambda>x. m x $ 2) has_integral 0) {0..t}"
    by (rule has_integral_eq[OF _ has_integral_0]) (use plane_m assms in auto)
  show ?thesis by (rule has_integral_unique[OF h z])
qed

end

end
