(*  Title:      Rational_Plane_Rotations.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational plane rotations: the algebraic piece common to Theorem 5.1 (thm:rational, converse direction) and
   Proposition 7.2 (prop:aux) of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal
   dilations" (Carles Marín, in preparation).

   Representation: vectors are rat^'n and matrices rat^'n^'n of HOL-Analysis (n = CARD('n), 'n finite), with
   our own standard scalar product dotp x y = sum_i x_i y_i (rat is not an inner product space, so the
   HOL-Analysis "inner" does not apply; the AFP's Jordan_Normal_Form is not used). Everything is over the
   rationals, with no classical assumption beyond the HOL axioms.

   Let lam be rational with -1 < lam < 1 and delta = 1 - lam^2. A "plane of type lam" is a pair (f, g) with
   f.g = 0, f.f = a > 0 and g.g = delta a.
   Proved without any assumption other than the hypotheses of each statement:
   (1) plane_rotation: on the plane, R f = lam f + g, R g = - delta f + lam g (extended linearly) preserves the
       scalar product, its adjoint is R* f = lam f - g, R* g = delta f + lam g, and R + R* = 2 lam on the plane.
   (2) orthogonal_planes_rotation: for k pairwise orthogonal planes of type lam, spanning V, there is a rational
       n x n matrix R with R^T R = I, R V subset V, R = identity on V-perp, and R + R^T = 2 lam P_V + 2 (I - P_V),
       P_V the orthogonal projection onto V, given by the orthogonal basis (sum of (x.f)/(f.f) f over the 2k
       vectors). Also (R x).(R y) = x.y for all x, y (in particular on V).
   (3) isotropic_gives_plane: w /= 0, v.w = 0, v.v = delta (w.w) gives the plane (w, v) of type lam.
   NOT formalized (PARTIAL with respect to the paper): the induction "q (x) L hyperbolic => q is an orthogonal
   sum of planes of type lam" needs Witt cancellation over L = Q(sqrt(-delta)), and the quadratic-form theory
   of the paper (trace form, Lemma 1 of Lewis); it is left out and no locale with witt_cancellation_L is given.
   Named assumptions: none.
*)
theory Rational_Plane_Rotations
  imports "HOL-Analysis.Analysis"
begin

section \<open>Scalar product and matrix helpers\<close>

definition dotp :: "rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat" where
  "dotp x y = (\<Sum>i\<in>UNIV. x $ i * y $ i)"

lemma dotp_comm: "dotp x y = dotp y x"
  by (simp add: dotp_def mult.commute)

lemma dotp_add_left: "dotp (x + y) z = dotp x z + dotp y z"
  by (simp add: dotp_def algebra_simps sum.distrib)

lemma dotp_add_right: "dotp z (x + y) = dotp z x + dotp z y"
  by (simp add: dotp_def algebra_simps sum.distrib)

lemma dotp_smult_left: "dotp (c *s x) y = c * dotp x y"
  by (simp add: dotp_def sum_distrib_left mult.assoc)

lemma dotp_smult_right: "dotp y (c *s x) = c * dotp y x"
  by (simp add: dotp_def sum_distrib_left mult.assoc mult.left_commute)

lemma dotp_diff_left: "dotp (x - y) z = dotp x z - dotp y z"
  by (simp add: dotp_def algebra_simps sum_subtractf)

lemma dotp_diff_right: "dotp z (x - y) = dotp z x - dotp z y"
  by (simp add: dotp_def algebra_simps sum_subtractf)

lemma dotp_zero_left [simp]: "dotp 0 y = 0"
  by (simp add: dotp_def)

lemma dotp_zero_right [simp]: "dotp y 0 = 0"
  by (simp add: dotp_def)

lemma dotp_sum_left: "dotp (\<Sum>i\<in>A. g i) y = (\<Sum>i\<in>A. dotp (g i) y)"
  by (induct A rule: infinite_finite_induct) (simp_all add: dotp_add_left)

lemma dotp_sum_right: "dotp y (\<Sum>i\<in>A. g i) = (\<Sum>i\<in>A. dotp y (g i))"
  by (induct A rule: infinite_finite_induct) (simp_all add: dotp_add_right)

lemma dotp_axis: "dotp (axis i (1::rat)) v = v $ i"
proof -
  have "(\<Sum>j\<in>UNIV. axis i (1::rat) $ j * v $ j) = (\<Sum>j\<in>UNIV. if j = i then v $ j else 0)"
    by (rule sum.cong) (simp_all add: axis_def)
  then show ?thesis by (simp add: dotp_def)
qed

lemma dotp_pos:
  assumes "w \<noteq> 0"
  shows "0 < dotp w w"
proof -
  obtain i where i: "w $ i \<noteq> 0"
    using assms by (auto simp: vec_eq_iff)
  have "0 < (w $ i)\<^sup>2" using i by simp
  then have "0 < w $ i * w $ i" by (simp add: power2_eq_square)
  also have "w $ i * w $ i \<le> dotp w w"
  proof -
    have "dotp w w = w $ i * w $ i + (\<Sum>j\<in>UNIV - {i}. w $ j * w $ j)"
      unfolding dotp_def by (rule sum.remove) simp_all
    moreover have "0 \<le> (\<Sum>j\<in>UNIV - {i}. w $ j * w $ j)"
      by (rule sum_nonneg) (rule zero_le_square)
    ultimately show ?thesis by linarith
  qed
  finally show ?thesis .
qed

lemma dotp_nondeg:
  assumes "\<And>x. dotp x v = dotp x u"
  shows "v = u"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix i
  have "dotp (axis i (1::rat)) v = dotp (axis i 1) u" by (rule assms)
  then show "v $ i = u $ i" by (simp add: dotp_axis)
qed

text \<open>The outer product matrix c * f g^T, and the scalar multiple of a matrix.\<close>

definition omat :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat^'n^'n" where
  "omat c f g = (\<chi> i j. c * f $ i * g $ j)"

definition sm :: "rat \<Rightarrow> rat^'n::finite^'n \<Rightarrow> rat^'n^'n" where
  "sm c A = (\<chi> i j. c * A $ i $ j)"

lemma omat_mv: "omat c f g *v x = (c * dotp g x) *s f"
  by (simp add: omat_def dotp_def matrix_vector_mult_def vec_eq_iff sum_distrib_left mult_ac)

lemma sm_mv: "sm c A *v x = c *s (A *v x)"
  by (simp add: sm_def matrix_vector_mult_def vec_eq_iff sum_distrib_left mult.assoc)

lemma mv_add: fixes A B :: "rat^'m::finite^'n::finite" shows "(A + B) *v x = A *v x + B *v x"
  by (simp add: matrix_vector_mult_def vec_eq_iff algebra_simps sum.distrib)

lemma mv_diff: fixes A B :: "rat^'m::finite^'n::finite" shows "(A - B) *v x = A *v x - B *v x"
  by (simp add: matrix_vector_mult_def vec_eq_iff left_diff_distrib sum_subtractf)

lemma mv_one: "mat (1::rat) *v x = x"
  by (rule matrix_vector_mul_lid)

lemma mv_sum: fixes M :: "'a \<Rightarrow> rat^'m::finite^'n::finite"
  shows "(\<Sum>i\<in>A. M i) *v x = (\<Sum>i\<in>A. M i *v x)"
proof -
  have z: "(0::rat^'m::finite^'n::finite) *v x = 0" by (simp add: matrix_vector_mult_def vec_eq_iff)
  show ?thesis by (induct A rule: infinite_finite_induct) (simp_all add: mv_add z)
qed

lemma mv_mv: "(A ** B) *v x = A *v (B *v x)"
  by (simp add: matrix_vector_mul_assoc)

lemma dotp_mv: "dotp (A *v x) y = dotp x (transpose A *v y)"
proof -
  have "dotp (A *v x) y = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. A $ i $ j * x $ j * y $ i)"
    by (simp add: dotp_def matrix_vector_mult_def sum_distrib_right)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. A $ i $ j * x $ j * y $ i)"
    by (rule sum.swap)
  also have "\<dots> = dotp x (transpose A *v y)"
    by (simp add: dotp_def matrix_vector_mult_def transpose_def sum_distrib_left mult_ac)
  finally show ?thesis .
qed

lemma mv_axis: fixes A :: "rat^'m::finite^'n::finite" shows "(A *v axis j (1::rat)) $ i = A $ i $ j"
proof -
  have "(\<Sum>k\<in>UNIV. A $ i $ k * axis j (1::rat) $ k) = (\<Sum>k\<in>UNIV. if k = j then A $ i $ k else 0)"
    by (rule sum.cong) (simp_all add: axis_def)
  then show ?thesis by (simp add: matrix_vector_mult_def)
qed

lemma mat_eq_by_mv:
  fixes A B :: "rat^'m::finite^'n::finite"
  assumes "\<And>x. A *v x = B *v x"
  shows "A = B"
proof (rule vec_eq_iff[THEN iffD2], rule allI, rule vec_eq_iff[THEN iffD2], rule allI)
  fix i j
  have "(A *v axis j (1::rat)) $ i = (B *v axis j 1) $ i" by (simp add: assms)
  then show "A $ i $ j = B $ i $ j" by (simp add: mv_axis)
qed

lemma mat_eq_by_dotp:
  assumes "\<And>x y. dotp x (A *v y) = dotp x (B *v y)"
  shows "A = B"
  using assms by (intro mat_eq_by_mv dotp_nondeg) simp

section \<open>One plane\<close>

definition plane :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> bool" where
  "plane lam f g \<longleftrightarrow> dotp f g = 0 \<and> 0 < dotp f f \<and> dotp g g = (1 - lam\<^sup>2) * dotp f f"

text \<open>The rotation R of the plane in coordinates (u, w), i.e. on u f + w g, and its adjoint R*.\<close>

definition rp :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat^'n" where
  "rp lam f g u w = u *s (lam *s f + g) + w *s (- (1 - lam\<^sup>2) *s f + lam *s g)"

definition rs :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat^'n" where
  "rs lam f g u w = u *s (lam *s f - g) + w *s ((1 - lam\<^sup>2) *s f + lam *s g)"

lemma plane_rotation:
  fixes f g :: "rat^'n::finite" and lam u w u' w' :: rat
  assumes pl: "plane lam f g"
  shows "dotp (rp lam f g u w) (rp lam f g u' w') = dotp (u *s f + w *s g) (u' *s f + w' *s g)"
    and "dotp (rs lam f g u w) (u' *s f + w' *s g) = dotp (u *s f + w *s g) (rp lam f g u' w')"
    and "rp lam f g u w + rs lam f g u w = (2 * lam) *s (u *s f + w *s g)"
    and "rp lam f g 1 0 = lam *s f + g" "rp lam f g 0 1 = - (1 - lam\<^sup>2) *s f + lam *s g"
    and "rs lam f g 1 0 = lam *s f - g" "rs lam f g 0 1 = (1 - lam\<^sup>2) *s f + lam *s g"
proof -
  have fg: "dotp f g = 0" and gf: "dotp g f = 0" and gg: "dotp g g = (1 - lam\<^sup>2) * dotp f f"
    using pl by (simp_all add: plane_def dotp_comm)
  show "dotp (rp lam f g u w) (rp lam f g u' w') = dotp (u *s f + w *s g) (u' *s f + w' *s g)"
    unfolding rp_def
    apply (simp only: dotp_add_left dotp_add_right dotp_smult_left dotp_smult_right fg gf gg)
    apply (simp only: power2_eq_square)
    apply (simp add: algebra_simps)
    done
  show "dotp (rs lam f g u w) (u' *s f + w' *s g) = dotp (u *s f + w *s g) (rp lam f g u' w')"
    unfolding rp_def rs_def
    apply (simp only: dotp_add_left dotp_add_right dotp_diff_left dotp_diff_right dotp_smult_left
        dotp_smult_right fg gf gg)
    apply (simp only: power2_eq_square)
    apply (simp add: algebra_simps)
    done
  show "rp lam f g u w + rs lam f g u w = (2 * lam) *s (u *s f + w *s g)"
    by (simp add: rp_def rs_def vec_eq_iff algebra_simps)
  show "rp lam f g 1 0 = lam *s f + g" "rp lam f g 0 1 = - (1 - lam\<^sup>2) *s f + lam *s g"
    "rs lam f g 1 0 = lam *s f - g" "rs lam f g 0 1 = (1 - lam\<^sup>2) *s f + lam *s g"
    by (simp_all add: rp_def rs_def)
qed

section \<open>Extraction of a plane from an isotropic vector\<close>

text \<open>If v + sqrt(-delta) w is isotropic for q (x) Q(sqrt(-delta)) then v.w = 0 and v.v = delta (w.w); with
  w /= 0 this is a plane of type lam, with f = w and g = v.\<close>

theorem isotropic_gives_plane:
  fixes v w :: "rat^'n::finite" and lam :: rat
  assumes "w \<noteq> 0" "dotp v w = 0" "dotp v v = (1 - lam\<^sup>2) * dotp w w"
  shows "plane lam w v" and "dotp w w \<noteq> 0"
proof -
  have "0 < dotp w w" by (rule dotp_pos[OF assms(1)])
  then show "dotp w w \<noteq> 0" by simp
  show "plane lam w v"
    using assms \<open>0 < dotp w w\<close> by (simp add: plane_def dotp_comm)
qed

section \<open>Orthogonal planes\<close>

definition Nvec :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat^'n \<Rightarrow> rat^'n" where
  "Nvec lam f g x =
     (((lam - 1) * dotp x f - dotp x g) / dotp f f) *s f
     + ((dotp x f + (lam - 1) * dotp x g / (1 - lam\<^sup>2)) / dotp f f) *s g"

definition Pvec :: "rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat^'n \<Rightarrow> rat^'n" where
  "Pvec f g x = (dotp x f / dotp f f) *s f + (dotp x g / dotp g g) *s g"

definition Nmat :: "rat \<Rightarrow> rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat^'n^'n" where
  "Nmat lam f g = omat ((lam - 1) / dotp f f) f f + omat (1 / dotp f f) g f
     + omat (- 1 / dotp f f) f g + omat ((lam - 1) / (1 - lam\<^sup>2) / dotp f f) g g"

definition Pmat :: "rat^'n::finite \<Rightarrow> rat^'n \<Rightarrow> rat^'n^'n" where
  "Pmat f g = omat (1 / dotp f f) f f + omat (1 / dotp g g) g g"

lemma Nmat_mv: "Nmat lam f g *v x = Nvec lam f g x"
  by (simp add: Nmat_def Nvec_def mv_add omat_mv dotp_comm[of f x] dotp_comm[of g x] vec_eq_iff
      algebra_simps divide_inverse inverse_mult_distrib)

lemma Pmat_mv: "Pmat f g *v x = Pvec f g x"
  by (simp add: Pmat_def Pvec_def mv_add omat_mv dotp_comm[of f x] dotp_comm[of g x] vec_eq_iff
      algebra_simps divide_inverse)

lemma cross_zero:
  assumes "dotp f f' = 0" "dotp f g' = 0" "dotp g f' = 0" "dotp g g' = 0"
  shows "dotp (u *s f + v *s g) (u' *s f' + v' *s g') = 0"
  using assms by (simp add: dotp_add_left dotp_add_right dotp_smult_left dotp_smult_right)

lemma plane_N_identities:
  assumes pl: "plane lam f g" and lam: "- 1 < lam" "lam < 1"
  shows "dotp x (Nvec lam f g y) + dotp (Nvec lam f g x) y + dotp (Nvec lam f g x) (Nvec lam f g y) = 0"
    and "dotp x (Nvec lam f g y) + dotp (Nvec lam f g x) y = 2 * (lam - 1) * dotp x (Pvec f g y)"
proof -
  have fg: "dotp f g = 0" and gf: "dotp g f = 0" and gg: "dotp g g = (1 - lam\<^sup>2) * dotp f f"
    and a: "0 < dotp f f"
    using pl by (simp_all add: plane_def dotp_comm)
  have d: "1 - lam\<^sup>2 \<noteq> 0"
  proof -
    have "0 < (1 - lam) * (1 + lam)" using lam by (intro mult_pos_pos) linarith+
    moreover have "1 - lam\<^sup>2 = (1 - lam) * (1 + lam)" by (simp add: algebra_simps power2_eq_square)
    ultimately have "0 < 1 - lam\<^sup>2" by linarith
    then show ?thesis by simp
  qed
  have c: "dotp f x = dotp x f" "dotp g x = dotp x g" "dotp f y = dotp y f" "dotp g y = dotp y g"
    by (simp_all add: dotp_comm)
  obtain e where e: "e = 1 - lam\<^sup>2" by blast
  have e0: "e \<noteq> 0" using d e by simp
  have gg': "dotp g g = e * dotp f f" using gg e by simp
  have Nv: "\<And>z. Nvec lam f g z = (((lam - 1) * dotp z f - dotp z g) / dotp f f) *s f
      + ((dotp z f + (lam - 1) * dotp z g / e) / dotp f f) *s g"
    by (simp add: Nvec_def e)
  have Pv: "\<And>z. Pvec f g z = (dotp z f / dotp f f) *s f + (dotp z g / (e * dotp f f)) *s g"
    by (simp add: Pvec_def gg')
  have a0: "dotp f f \<noteq> 0" using a by simp
  show "dotp x (Nvec lam f g y) + dotp (Nvec lam f g x) y + dotp (Nvec lam f g x) (Nvec lam f g y) = 0"
    apply (simp only: Nv dotp_add_left dotp_add_right dotp_smult_left dotp_smult_right fg gf gg' c)
    apply (simp add: divide_simps a0 e0)
    apply (simp add: e algebra_simps power2_eq_square)
    done
  show "dotp x (Nvec lam f g y) + dotp (Nvec lam f g x) y = 2 * (lam - 1) * dotp x (Pvec f g y)"
    apply (simp only: Nv Pv dotp_add_left dotp_add_right dotp_smult_left dotp_smult_right fg gf gg' c)
    apply (simp add: divide_simps a0 e0)
    apply (simp add: e algebra_simps power2_eq_square)
    done
qed


definition planes :: "rat \<Rightarrow> (nat \<Rightarrow> rat^'n::finite) \<Rightarrow> (nat \<Rightarrow> rat^'n) \<Rightarrow> nat \<Rightarrow> bool" where
  "planes lam f g k \<longleftrightarrow> (\<forall>i<k. plane lam (f i) (g i)) \<and>
     (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> dotp (f i) (f j) = 0 \<and> dotp (f i) (g j) = 0 \<and>
        dotp (g i) (f j) = 0 \<and> dotp (g i) (g j) = 0)"

definition Vspan :: "(nat \<Rightarrow> rat^'n::finite) \<Rightarrow> (nat \<Rightarrow> rat^'n) \<Rightarrow> nat \<Rightarrow> (rat^'n) set" where
  "Vspan f g k = {v. \<exists>c d. v = (\<Sum>i<k. c i *s f i + d i *s g i)}"

definition Rmat :: "rat \<Rightarrow> (nat \<Rightarrow> rat^'n::finite) \<Rightarrow> (nat \<Rightarrow> rat^'n) \<Rightarrow> nat \<Rightarrow> rat^'n^'n" where
  "Rmat lam f g k = mat 1 + (\<Sum>i<k. Nmat lam (f i) (g i))"

definition Pproj :: "(nat \<Rightarrow> rat^'n::finite) \<Rightarrow> (nat \<Rightarrow> rat^'n) \<Rightarrow> nat \<Rightarrow> rat^'n^'n" where
  "Pproj f g k = (\<Sum>i<k. Pmat (f i) (g i))"

lemma Rmat_mv: "Rmat lam f g k *v x = x + (\<Sum>i<k. Nvec lam (f i) (g i) x)"
  by (simp add: Rmat_def mv_add mv_one mv_sum Nmat_mv)

lemma Pproj_mv: "Pproj f g k *v x = (\<Sum>i<k. Pvec (f i) (g i) x)"
  by (simp add: Pproj_def mv_sum Pmat_mv)

lemma planes_cross:
  assumes "planes lam f g k" "i < k" "j < k" "i \<noteq> j"
  shows "dotp (Nvec lam (f i) (g i) x) (Nvec lam (f j) (g j) y) = 0"
  using assms unfolding planes_def Nvec_def by (intro cross_zero) auto

lemma planes_unit: "planes lam f g k \<Longrightarrow> i < k \<Longrightarrow> plane lam (f i) (g i)"
  by (simp add: planes_def)

lemma R_dotp:
  assumes pls: "planes lam f g k" and lam: "- 1 < lam" "lam < 1"
  shows "dotp (Rmat lam f g k *v x) (Rmat lam f g k *v y) = dotp x y"
proof -
  let ?N = "\<lambda>i z. Nvec lam (f i) (g i) z"
  have dd: "\<And>i. i \<in> {..<k} \<Longrightarrow> (\<Sum>j<k. dotp (?N i x) (?N j y)) = dotp (?N i x) (?N i y)"
  proof -
    fix i assume i: "i \<in> {..<k}"
    have "(\<Sum>j<k. dotp (?N i x) (?N j y)) = (\<Sum>j<k. if j = i then dotp (?N i x) (?N i y) else 0)"
      by (rule sum.cong) (use pls i in \<open>auto simp: planes_cross\<close>)
    also have "\<dots> = dotp (?N i x) (?N i y)" using i by simp
    finally show "(\<Sum>j<k. dotp (?N i x) (?N j y)) = dotp (?N i x) (?N i y)" .
  qed
  have dd': "(\<Sum>i<k. \<Sum>j<k. dotp (?N i x) (?N j y)) = (\<Sum>i<k. dotp (?N i x) (?N i y))"
    by (rule sum.cong[OF refl dd])
  have dd'': "(\<Sum>i<k. \<Sum>j<k. dotp (?N j x) (?N i y)) = (\<Sum>i<k. dotp (?N i x) (?N i y))"
    by (rule trans[OF sum.swap dd'])
  have zero: "(\<Sum>i<k. dotp x (?N i y) + dotp (?N i x) y + dotp (?N i x) (?N i y)) = 0"
    by (rule sum.neutral) (use pls lam in \<open>auto simp: plane_N_identities(1) planes_unit\<close>)
  have "dotp (Rmat lam f g k *v x) (Rmat lam f g k *v y)
      = dotp x y + (\<Sum>i<k. dotp x (?N i y) + dotp (?N i x) y + dotp (?N i x) (?N i y))"
    by (simp add: Rmat_mv dotp_add_left dotp_add_right dotp_sum_left dotp_sum_right sum.distrib dd' dd'')
  with zero show ?thesis by simp
qed

lemma R_orth:
  assumes "planes lam f g k" "- 1 < lam" "lam < 1"
  shows "transpose (Rmat lam f g k) ** Rmat lam f g k = mat 1"
proof (rule mat_eq_by_dotp)
  fix x y
  have "dotp x ((transpose (Rmat lam f g k) ** Rmat lam f g k) *v y)
      = dotp (Rmat lam f g k *v x) (Rmat lam f g k *v y)"
    by (simp add: mv_mv dotp_mv)
  also have "\<dots> = dotp x y" by (rule R_dotp[OF assms])
  finally show "dotp x ((transpose (Rmat lam f g k) ** Rmat lam f g k) *v y) = dotp x (mat 1 *v y)"
    by (simp add: mv_one)
qed

lemma R_sym:
  assumes pls: "planes lam f g k" and lam: "- 1 < lam" "lam < 1"
  shows "Rmat lam f g k + transpose (Rmat lam f g k)
       = sm (2 * lam) (Pproj f g k) + sm 2 (mat 1 - Pproj f g k)"
proof (rule mat_eq_by_dotp)
  fix x y
  let ?N = "\<lambda>i z. Nvec lam (f i) (g i) z"
  have "dotp x ((Rmat lam f g k + transpose (Rmat lam f g k)) *v y)
      = dotp x (Rmat lam f g k *v y) + dotp (Rmat lam f g k *v x) y"
    by (simp add: mv_add dotp_add_right dotp_mv)
  also have "\<dots> = 2 * dotp x y + (\<Sum>i<k. dotp x (?N i y) + dotp (?N i x) y)"
    by (simp add: Rmat_mv dotp_add_left dotp_add_right dotp_sum_left dotp_sum_right sum.distrib)
  also have "(\<Sum>i<k. dotp x (?N i y) + dotp (?N i x) y) = (\<Sum>i<k. 2 * (lam - 1) * dotp x (Pvec (f i) (g i) y))"
    by (rule sum.cong[OF refl]) (use pls lam in \<open>auto simp: plane_N_identities(2) planes_unit\<close>)
  also have "\<dots> = 2 * (lam - 1) * dotp x (Pproj f g k *v y)"
    by (simp add: Pproj_mv dotp_sum_right sum_distrib_left)
  finally show "dotp x ((Rmat lam f g k + transpose (Rmat lam f g k)) *v y)
      = dotp x ((sm (2 * lam) (Pproj f g k) + sm 2 (mat 1 - Pproj f g k)) *v y)"
    by (simp add: mv_add mv_diff sm_mv mv_one dotp_add_right dotp_smult_right dotp_diff_right algebra_simps)
qed

lemma R_identity_on_perp:
  assumes "\<And>i. i < k \<Longrightarrow> dotp x (f i) = 0" "\<And>i. i < k \<Longrightarrow> dotp x (g i) = 0"
  shows "Rmat lam f g k *v x = x"
proof -
  have "\<And>i. i < k \<Longrightarrow> Nvec lam (f i) (g i) x = 0"
    by (simp add: Nvec_def assms)
  then show ?thesis by (simp add: Rmat_mv)
qed

lemma R_invariant:
  assumes "x \<in> Vspan f g k"
  shows "Rmat lam f g k *v x \<in> Vspan f g k"
proof -
  obtain c d where x: "x = (\<Sum>i<k. c i *s f i + d i *s g i)" using assms by (auto simp: Vspan_def)
  let ?al = "\<lambda>i. ((lam - 1) * dotp x (f i) - dotp x (g i)) / dotp (f i) (f i)"
  let ?be = "\<lambda>i. (dotp x (f i) + (lam - 1) * dotp x (g i) / (1 - lam\<^sup>2)) / dotp (f i) (f i)"
  have hR: "Rmat lam f g k *v x = (\<Sum>i<k. (c i + ?al i) *s f i + (d i + ?be i) *s g i)"
  proof -
    have "Rmat lam f g k *v x = (\<Sum>i<k. c i *s f i + d i *s g i) + (\<Sum>i<k. ?al i *s f i + ?be i *s g i)"
      by (simp add: Rmat_mv Nvec_def x[symmetric])
    also have "\<dots> = (\<Sum>i<k. (c i *s f i + d i *s g i) + (?al i *s f i + ?be i *s g i))"
      by (simp add: sum.distrib)
    also have "\<dots> = (\<Sum>i<k. (c i + ?al i) *s f i + (d i + ?be i) *s g i)"
      by (rule sum.cong[OF refl]) (simp add: vec_eq_iff algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding Vspan_def mem_Collect_eq
    by (rule exI[of _ "\<lambda>i. c i + ?al i"], rule exI[of _ "\<lambda>i. d i + ?be i"], rule hR)
qed

lemma Vspan_gens: "i < k \<Longrightarrow> f i \<in> Vspan f g k" "i < k \<Longrightarrow> g i \<in> Vspan f g k"
proof -
  assume i: "i < k"
  have "f i = (\<Sum>j<k. (if j = i then 1 else 0) *s f j + (0::rat) *s g j)"
  proof -
    have "(\<Sum>j<k. (if j = i then 1 else 0) *s f j + (0::rat) *s g j) = (\<Sum>j<k. if j = i then f j else 0)"
      by (rule sum.cong) (simp_all add: vec_eq_iff)
    then show ?thesis using i by simp
  qed
  then show "f i \<in> Vspan f g k" unfolding Vspan_def mem_Collect_eq
    by (intro exI[of _ "\<lambda>j. if j = i then (1::rat) else 0"] exI[of _ "\<lambda>j. (0::rat)"]) simp
  have "g i = (\<Sum>j<k. (0::rat) *s f j + (if j = i then 1 else 0) *s g j)"
  proof -
    have "(\<Sum>j<k. (0::rat) *s f j + (if j = i then 1 else 0) *s g j) = (\<Sum>j<k. if j = i then g j else 0)"
      by (rule sum.cong) (simp_all add: vec_eq_iff)
    then show ?thesis using i by simp
  qed
  then show "g i \<in> Vspan f g k" unfolding Vspan_def mem_Collect_eq
    by (intro exI[of _ "\<lambda>j. (0::rat)"] exI[of _ "\<lambda>j. if j = i then (1::rat) else 0"]) simp
qed

theorem orthogonal_planes_rotation:
  fixes f g :: "nat \<Rightarrow> rat^'n::finite" and lam :: rat and k :: nat
  assumes lam: "- 1 < lam" "lam < 1" and pls: "planes lam f g k"
  shows "\<exists>R::rat^'n^'n.
      transpose R ** R = mat 1
    \<and> (\<forall>x\<in>Vspan f g k. R *v x \<in> Vspan f g k)
    \<and> (\<forall>x\<in>Vspan f g k. \<forall>y\<in>Vspan f g k. dotp (R *v x) (R *v y) = dotp x y)
    \<and> (\<forall>x. (\<forall>v\<in>Vspan f g k. dotp x v = 0) \<longrightarrow> R *v x = x)
    \<and> R + transpose R = sm (2 * lam) (Pproj f g k) + sm 2 (mat 1 - Pproj f g k)"
proof (rule exI[where x = "Rmat lam f g k"], intro conjI ballI allI impI)
  show "transpose (Rmat lam f g k) ** Rmat lam f g k = mat 1" by (rule R_orth[OF pls lam])
  show "\<And>x. x \<in> Vspan f g k \<Longrightarrow> Rmat lam f g k *v x \<in> Vspan f g k" by (rule R_invariant)
  show "\<And>x y. x \<in> Vspan f g k \<Longrightarrow> y \<in> Vspan f g k \<Longrightarrow>
      dotp (Rmat lam f g k *v x) (Rmat lam f g k *v y) = dotp x y" by (rule R_dotp[OF pls lam])
  show "\<And>x. \<forall>v\<in>Vspan f g k. dotp x v = 0 \<Longrightarrow> Rmat lam f g k *v x = x"
    by (rule R_identity_on_perp) (auto simp: Vspan_gens)
  show "Rmat lam f g k + transpose (Rmat lam f g k)
      = sm (2 * lam) (Pproj f g k) + sm 2 (mat 1 - Pproj f g k)" by (rule R_sym[OF pls lam])
qed

end
