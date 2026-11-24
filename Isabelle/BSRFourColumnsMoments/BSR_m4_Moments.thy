(*  Title:      BSR_m4_Moments.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Algebraic core of Lemma lem:moments ("All moments") of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation), label lem:moments.
    The lemma: if the Schur complement (M1) of (T_0 + t T_c)^* J (T_0 + t T_c) vanishes identically in t, then
    <p, A^j p> = 0 for all j >= 0.  The written proof has four steps; this theory proves the steps that are
    algebra of sequences and of linear maps:
    (1) unperturbed_coeff / coef_unperturbed: the coefficient of tau^j of
          mu_0 - <p, (I + 2 (I+tau B)^-1 + (I+tau B)^-2) p>   is   (-1)^(j+1) (j+3) mu_j,
        and in one variable 1 - (1 + 1/(1+x))^2 = -(2x+3)/(1+x)^2 has all coefficients (-1)^(j+1)(j+3) /= 0;
    (2) moments_vanish: the induction on j: if the coefficient of tau^j is (-1)^(j+1)(j+3) mu_j plus a sum
        of terms each containing some mu_i with i <= j-2, and all coefficients vanish, then every mu_j = 0;
    (3) shift_moments: if <p, B^k p> = 0 for all k, then <p, (B + alpha I)^j p> = 0 for all j
        (the last sentence of the proof, A = B + alpha I).
    NOT formalized (stays as written proof): the derivation of (M1) as a Schur complement in Witt coordinates,
    the division by 1 + t alpha, the formal Neumann expansion of (X^2 + E)^-1 and the word analysis showing
    that every word with n >= 1 contains a factor <p, g(tau B) p>; the hypothesis "remainder terms contain
    some mu_i, i <= j-2" of moments_vanish is exactly the output of that word analysis.
*)

theory BSR_m4_Moments
  imports "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Formal_Power_Series"
begin

subsection \<open>(1) The coefficient without the rank-two perturbation\<close>

lemma coef_unperturbed:
  fixes mu :: "nat \<Rightarrow> real"
  shows "(if j = 0 then mu 0 else 0)
         - ((if j = 0 then mu 0 else 0) + 2 * ((-1) ^ j * mu j) + real (j + 1) * ((-1) ^ j * mu j))
         = (-1) ^ (j + 1) * real (j + 3) * mu j"
  by (simp add: algebra_simps)

lemma coef_unperturbed_nonzero:
  fixes mu :: "nat \<Rightarrow> real"
  shows "((-1) ^ (j + 1) * real (j + 3) * mu j = 0) \<longleftrightarrow> mu j = 0"
  by simp

lemma nth_one_plus_X:
  fixes f :: "real fps"
  shows "fps_nth ((1 + fps_X) * f) n = (if n = 0 then fps_nth f 0 else fps_nth f n + fps_nth f (n - 1))"
  by (simp add: fps_mult_fps_X_plus_1_nth)

text \<open>One variable: 1 - (1 + 1/(1+x))^2 has coefficient (-1)^(j+1) (j+3) at x^j.\<close>

definition gser :: "real fps" where
  "gser = Abs_fps (\<lambda>j. (-1) ^ (j + 1) * real (j + 3))"

definition hser :: "real fps" where
  "hser = Abs_fps (\<lambda>j. if j = 0 then -3 else (-1) ^ (j + 1))"

lemma gser_h: "(1 + fps_X) * gser = hser"
proof (rule fps_ext)
  fix n
  show "fps_nth ((1 + fps_X) * gser) n = fps_nth hser n"
  proof (cases n)
    case 0
    then show ?thesis by (simp add: nth_one_plus_X gser_def hser_def)
  next
    case (Suc k)
    then show ?thesis
      by (simp add: nth_one_plus_X gser_def hser_def algebra_simps)
  qed
qed

lemma gser_sq: "(1 + fps_X) * ((1 + fps_X) * gser) = - (2 * fps_X) - 3"
proof (rule fps_ext)
  fix n
  show "fps_nth ((1 + fps_X) * ((1 + fps_X) * gser)) n = fps_nth (- (2 * fps_X) - 3 :: real fps) n"
  proof (cases n)
    case 0
    then show ?thesis by (simp add: gser_h nth_one_plus_X hser_def fps_numeral_nth)
  next
    case (Suc k)
    show ?thesis
    proof (cases k)
      case 0
      with Suc show ?thesis by (simp add: gser_h nth_one_plus_X hser_def fps_numeral_nth)
    next
      case (Suc l)
      with \<open>n = Suc k\<close> show ?thesis
        by (simp add: gser_h nth_one_plus_X hser_def fps_numeral_nth)
    qed
  qed
qed

theorem unperturbed_coeff:
  "fps_nth (1 - (1 + inverse (1 + fps_X)) ^ 2 :: real fps) j = (-1) ^ (j + 1) * real (j + 3)"
proof -
  let ?a = "1 + fps_X :: real fps"
  have a0: "fps_nth ?a 0 \<noteq> 0" by simp
  have ia: "inverse ?a * ?a = 1" by (rule inverse_mult_eq_1[OF a0])
  have a2: "?a * ?a \<noteq> 0" using a0 by (simp add: fps_nonzero_nth)
  have "(1 - (1 + inverse ?a) ^ 2) * (?a * ?a) = (?a * ?a) - (?a + 1) ^ 2"
  proof -
    have "(1 + inverse ?a) * ?a = ?a + 1" using ia by (simp add: algebra_simps)
    have "((1 + inverse ?a) ^ 2) * (?a * ?a) = ((1 + inverse ?a) * ?a) ^ 2"
      by (simp add: power2_eq_square mult_ac)
    also have "\<dots> = (?a + 1) ^ 2" using \<open>(1 + inverse ?a) * ?a = ?a + 1\<close> by simp
    finally have "((1 + inverse ?a) ^ 2) * (?a * ?a) = (?a + 1) ^ 2" .
    then show ?thesis by (simp add: algebra_simps)
  qed
  also have "(?a * ?a) - (?a + 1) ^ 2 = - (2 * fps_X) - 3"
    by (simp add: power2_eq_square algebra_simps)
  finally have "(1 - (1 + inverse ?a) ^ 2) * (?a * ?a) = - (2 * fps_X) - 3" .
  moreover have "gser * (?a * ?a) = - (2 * fps_X) - 3"
    using gser_sq by (simp add: algebra_simps)
  ultimately have "(1 - (1 + inverse ?a) ^ 2) * (?a * ?a) = gser * (?a * ?a)" by simp
  then have "1 - (1 + inverse ?a) ^ 2 = gser" using a2 by simp
  then show ?thesis by (simp add: gser_def)
qed

corollary unperturbed_coeff_nonzero:
  "fps_nth (1 - (1 + inverse (1 + fps_X)) ^ 2 :: real fps) j \<noteq> 0"
  by (subst unperturbed_coeff) simp

subsection \<open>(2) Induction on the moments\<close>

theorem moments_vanish:
  fixes mu a :: "nat \<Rightarrow> real"
    and Wd :: "nat \<Rightarrow> 'w set" and idx :: "nat \<Rightarrow> 'w \<Rightarrow> nat" and cf :: "nat \<Rightarrow> 'w \<Rightarrow> real"
  assumes fin: "\<And>j. finite (Wd j)"
    and low: "\<And>j w. w \<in> Wd j \<Longrightarrow> idx j w + 2 \<le> j"
    and dec: "\<And>j. a j = (-1) ^ (j + 1) * real (j + 3) * mu j + (\<Sum>w\<in>Wd j. cf j w * mu (idx j w))"
    and zero: "\<And>j. a j = 0"
  shows "mu j = 0"
proof (induction j rule: less_induct)
  case (less j)
  have "\<And>w. w \<in> Wd j \<Longrightarrow> cf j w * mu (idx j w) = 0"
  proof -
    fix w assume w: "w \<in> Wd j"
    from low[OF w] have "idx j w < j" by simp
    then show "cf j w * mu (idx j w) = 0" using less.IH by simp
  qed
  then have "(\<Sum>w\<in>Wd j. cf j w * mu (idx j w)) = 0" by (simp add: sum.neutral)
  then have "(-1) ^ (j + 1) * real (j + 3) * mu j = 0" using dec[of j] zero[of j] by simp
  then show ?case by simp
qed

subsection \<open>(3) The shift A = B + alpha I\<close>

lemma span_closed_under_linear:
  assumes B: "linear B" and S: "\<And>s. s \<in> S \<Longrightarrow> B s \<in> span S" and y: "y \<in> span S"
  shows "B y \<in> span S"
proof -
  have sub: "subspace {y. B y \<in> span S}"
    by (simp add: subspace_def linear_0[OF B] linear_add[OF B] linear_cmul[OF B] span_add span_scale span_0)
  have "S \<subseteq> {y. B y \<in> span S}" using S by auto
  from span_minimal[OF this sub] y show ?thesis by blast
qed

theorem shift_moments:
  fixes B :: "'v::real_vector \<Rightarrow> 'v" and phi :: "'v \<Rightarrow> real" and p :: 'v and alpha :: real
  assumes B: "linear B" and phi: "linear phi" and mom: "\<And>k. phi ((B ^^ k) p) = 0"
  shows "phi (((\<lambda>x. B x + alpha *\<^sub>R x) ^^ j) p) = 0"
proof -
  let ?S = "range (\<lambda>k. (B ^^ k) p)"
  have BS: "\<And>s. s \<in> ?S \<Longrightarrow> B s \<in> span ?S"
    by (auto intro: span_base)
       (metis funpow.simps(2) o_def range_eqI span_base)
  have ker: "subspace {y. phi y = 0}" by (simp add: subspace_def linear_0[OF phi] linear_add[OF phi] linear_cmul[OF phi])
  have phiS: "\<And>y. y \<in> span ?S \<Longrightarrow> phi y = 0"
  proof -
    fix y assume y: "y \<in> span ?S"
    have "?S \<subseteq> {y. phi y = 0}" using mom by auto
    from span_minimal[OF this ker] y show "phi y = 0" by blast
  qed
  have inS: "((\<lambda>x. B x + alpha *\<^sub>R x) ^^ j) p \<in> span ?S"
  proof (induction j)
    case 0
    have "p \<in> ?S" by (rule range_eqI[of p _ 0]) simp
    then show ?case by (simp add: span_base)
  next
    case (Suc j)
    have "((\<lambda>x. B x + alpha *\<^sub>R x) ^^ Suc j) p = B (((\<lambda>x. B x + alpha *\<^sub>R x) ^^ j) p)
        + alpha *\<^sub>R (((\<lambda>x. B x + alpha *\<^sub>R x) ^^ j) p)"
      by simp
    moreover have "B (((\<lambda>x. B x + alpha *\<^sub>R x) ^^ j) p) \<in> span ?S"
      by (rule span_closed_under_linear[OF B BS Suc])
    ultimately show ?case using Suc by (simp add: span_add span_scale)
  qed
  show ?thesis by (rule phiS[OF inS])
qed

end
