(*  Title:      BSR_m4_Polar.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Polarization of symmetric multilinear forms of any arity n (used by Lemma lem:invariant-plane and
    lem:low-index-four of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation)): a form
    f(v_0,...,v_{n-1}) that is additive and homogeneous in each slot, invariant under swapping adjacent slots,
    and vanishes on the diagonal f(x,...,x) = 0, vanishes identically.
    The proof: S(m): f(a_0,...,a_{m-1},x,...,x) = 0 for all a, x.  Expanding f(a, (x + t z)^(n-m)) by the binomial
    theorem (move lemma + Pascal) gives a polynomial in t that is identically zero; its coefficient of t is
    (n-m) f(a, z, x^(n-m-1)).  Works over the reals (char. 0).
*)

theory BSR_m4_Polar
  imports "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Polynomial"
begin

subsection \<open>Coefficients of an identically vanishing polynomial\<close>

lemma poly_coeff_zero:
  fixes a :: "nat \<Rightarrow> real"
  assumes z: "\<And>t. (\<Sum>j\<le>r. a j * t ^ j) = 0" and i: "i \<le> r"
  shows "a i = 0"
proof -
  let ?p = "(\<Sum>j\<le>r. monom (a j) j) :: real poly"
  have "\<And>t. poly ?p t = 0" using z by (simp add: poly_sum poly_monom)
  then have all0: "\<forall>t. poly ?p t = 0" by simp
  have "?p = 0" using all0 poly_all_0_iff_0[of ?p] by simp
  then have "coeff ?p i = 0" by simp
  moreover have "coeff ?p i = a i" using i by (simp add: coeff_sum coeff_monom sum.delta)
  ultimately show ?thesis by simp
qed

subsection \<open>Symmetric multilinear forms on slots 0..n-1\<close>

locale pol_form =
  fixes n :: nat and f :: "(nat \<Rightarrow> 'c::real_vector) \<Rightarrow> real"
  assumes dep: "\<And>v w. (\<And>i. i < n \<Longrightarrow> v i = w i) \<Longrightarrow> f v = f w"
    and add: "\<And>v i a b. i < n \<Longrightarrow> f (v(i := a + b)) = f (v(i := a)) + f (v(i := b))"
    and hom: "\<And>v i s a. i < n \<Longrightarrow> f (v(i := s *\<^sub>R a)) = s * f (v(i := a))"
    and sw: "\<And>v i. Suc i < n \<Longrightarrow> f (v \<circ> Fun.swap i (Suc i) id) = f v"
begin

definition cfg :: "nat \<Rightarrow> (nat \<Rightarrow> 'c) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c" where
  "cfg m a j x z = (\<lambda>i. if i < m then a i else if i < m + j then z else x)"

lemma move:
  "m + j < n \<Longrightarrow> f (cfg (m + 1) (a(m := x)) j x z) = f (cfg m a j x z)"
proof (induction j arbitrary: m a)
  case 0
  have "cfg (m + 1) (a(m := x)) 0 x z = cfg m a 0 x z"
    by (rule ext) (auto simp: cfg_def)
  then show ?case by (rule arg_cong[where f = f])
next
  case (Suc j)
  from Suc.prems have mn: "Suc m < n" by simp
  have e1: "cfg (m + 1) (a(m := x)) (Suc j) x z \<circ> Fun.swap m (Suc m) id
      = cfg (m + 1 + 1) ((a(m := z)) (m + 1 := x)) j x z"
    by (rule ext) (auto simp: cfg_def Fun.swap_def)
  have e4: "cfg (m + 1) (a(m := z)) j x z = cfg m a (Suc j) x z"
    by (rule ext) (auto simp: cfg_def)
  have "f (cfg (m + 1) (a(m := x)) (Suc j) x z)
      = f (cfg (m + 1) (a(m := x)) (Suc j) x z \<circ> Fun.swap m (Suc m) id)"
    using sw[OF mn] by simp
  also have "\<dots> = f (cfg (m + 1 + 1) ((a(m := z)) (m + 1 := x)) j x z)" using e1 by simp
  also have "\<dots> = f (cfg (m + 1) (a(m := z)) j x z)"
    by (rule Suc.IH[of "m + 1" "a(m := z)"]) (use Suc.prems in simp)
  also have "\<dots> = f (cfg m a (Suc j) x z)" using e4 by simp
  finally show ?case .
qed

lemma binom_sum:
  fixes g :: "nat \<Rightarrow> real"
  shows "(\<Sum>j\<le>Suc r. real (Suc r choose j) * t ^ j * g j)
       = (\<Sum>j\<le>r. real (r choose j) * t ^ j * g j) + t * (\<Sum>j\<le>r. real (r choose j) * t ^ j * g (Suc j))"
proof -
  have s1: "(\<Sum>j\<le>Suc r. real (Suc r choose j) * t ^ j * g j)
      = g 0 + (\<Sum>j\<le>r. real (Suc r choose Suc j) * t ^ Suc j * g (Suc j))"
    using sum.atMost_Suc_shift[of "\<lambda>j. real (Suc r choose j) * t ^ j * g j" r] by simp
  have s2: "(\<Sum>j\<le>r. real (Suc r choose Suc j) * t ^ Suc j * g (Suc j))
      = (\<Sum>j\<le>r. real (r choose j) * t ^ Suc j * g (Suc j)) + (\<Sum>j\<le>r. real (r choose Suc j) * t ^ Suc j * g (Suc j))"
    by (simp add: sum.distrib algebra_simps)
  have s3: "g 0 + (\<Sum>j\<le>r. real (r choose Suc j) * t ^ Suc j * g (Suc j)) = (\<Sum>j\<le>r. real (r choose j) * t ^ j * g j)"
  proof -
    have "(\<Sum>j\<le>Suc r. real (r choose j) * t ^ j * g j)
        = g 0 + (\<Sum>j\<le>r. real (r choose Suc j) * t ^ Suc j * g (Suc j))"
      using sum.atMost_Suc_shift[of "\<lambda>j. real (r choose j) * t ^ j * g j" r] by simp
    moreover have "(\<Sum>j\<le>Suc r. real (r choose j) * t ^ j * g j) = (\<Sum>j\<le>r. real (r choose j) * t ^ j * g j)"
      by simp
    ultimately show ?thesis by simp
  qed
  have s4: "(\<Sum>j\<le>r. real (r choose j) * t ^ Suc j * g (Suc j))
      = t * (\<Sum>j\<le>r. real (r choose j) * t ^ j * g (Suc j))"
    by (simp add: sum_distrib_left algebra_simps)
  show ?thesis using s1 s2 s3 s4 by simp
qed

lemma expand:
  "m + r = n \<Longrightarrow>
   f (\<lambda>i. if i < m then a i else x + t *\<^sub>R z) = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg m a j x z))"
proof (induction r arbitrary: m a)
  case 0
  then have "f (\<lambda>i. if i < m then a i else x + t *\<^sub>R z) = f (cfg m a 0 x z)"
    by (intro dep) (auto simp: cfg_def)
  then show ?case by simp
next
  case (Suc r)
  from Suc.prems have mn: "m < n" by simp
  let ?u = "\<lambda>i. if i < m then a i else x + t *\<^sub>R z"
  have u: "?u = (?u)(m := x + t *\<^sub>R z)" by (rule ext) simp
  have "f ?u = f ((?u)(m := x)) + t * f ((?u)(m := z))"
    by (subst u) (simp add: add[OF mn] hom[OF mn])
  moreover have "(?u)(m := x) = (\<lambda>i. if i < m + 1 then (a(m := x)) i else x + t *\<^sub>R z)"
    by (rule ext) auto
  moreover have "(?u)(m := z) = (\<lambda>i. if i < m + 1 then (a(m := z)) i else x + t *\<^sub>R z)"
    by (rule ext) auto
  ultimately have "f ?u = f (\<lambda>i. if i < m + 1 then (a(m := x)) i else x + t *\<^sub>R z)
      + t * f (\<lambda>i. if i < m + 1 then (a(m := z)) i else x + t *\<^sub>R z)" by simp
  also have "\<dots> = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := x)) j x z))
      + t * (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := z)) j x z))"
  proof -
    have h: "m + 1 + r = n" using Suc.prems by simp
    have i1: "f (\<lambda>i. if i < m + 1 then (a(m := x)) i else x + t *\<^sub>R z)
        = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := x)) j x z))"
      by (rule Suc.IH[OF h])
    have i2: "f (\<lambda>i. if i < m + 1 then (a(m := z)) i else x + t *\<^sub>R z)
        = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := z)) j x z))"
      by (rule Suc.IH[OF h])
    show ?thesis by (simp only: i1 i2)
  qed
  also have "\<dots> = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg m a j x z))
      + t * (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg m a (Suc j) x z))"
  proof -
    have A: "\<And>j. j \<le> r \<Longrightarrow> f (cfg (m + 1) (a(m := x)) j x z) = f (cfg m a j x z)"
      using move[of m _ a x z] Suc.prems by simp
    have B: "\<And>j. f (cfg (m + 1) (a(m := z)) j x z) = f (cfg m a (Suc j) x z)"
      by (rule arg_cong[where f = f]) (rule ext, auto simp: cfg_def)
    have S1: "(\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := x)) j x z))
        = (\<Sum>j\<le>r. real (r choose j) * t ^ j * f (cfg m a j x z))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {..r}"
      then have "j \<le> r" by simp
      from A[OF this] show "real (r choose j) * t ^ j * f (cfg (m + 1) (a(m := x)) j x z)
          = real (r choose j) * t ^ j * f (cfg m a j x z)" by simp
    qed
    show ?thesis by (simp only: S1 B)
  qed
  also have "\<dots> = (\<Sum>j\<le>Suc r. real (Suc r choose j) * t ^ j * f (cfg m a j x z))"
    by (rule binom_sum[symmetric])
  finally show ?case .
qed

theorem polar:
  assumes diag: "\<And>x. f (\<lambda>_. x) = 0"
  shows "f v = 0"
proof -
  have S: "\<And>m. m \<le> n \<Longrightarrow> \<forall>(a::nat \<Rightarrow> 'c) (x::'c). f (\<lambda>i. if i < m then a i else x) = 0"
  proof -
    fix m show "m \<le> n \<Longrightarrow> \<forall>(a::nat \<Rightarrow> 'c) (x::'c). f (\<lambda>i. if i < m then a i else x) = 0"
    proof (induction m)
      case 0
      show ?case using diag by simp
    next
      case (Suc m)
      then have mn: "m < n" by simp
      show ?case
      proof (intro allI)
        fix a :: "nat \<Rightarrow> 'c" and x :: 'c
        let ?r = "n - m"
        define z where "z = a m"
        have vanish: "\<And>t. (\<Sum>j\<le>?r. (real (?r choose j) * f (cfg m a j x z)) * t ^ j) = 0"
        proof -
          fix t
          have "0 = f (\<lambda>i. if i < m then a i else (x + t *\<^sub>R z))" using Suc.IH mn by simp
          also have "\<dots> = (\<Sum>j\<le>?r. real (?r choose j) * t ^ j * f (cfg m a j x z))"
            using expand[of m ?r a x t z] mn by simp
          finally show "(\<Sum>j\<le>?r. (real (?r choose j) * f (cfg m a j x z)) * t ^ j) = 0"
            by (simp add: mult.commute mult.left_commute)
        qed
        have r1: "1 \<le> ?r" using mn by simp
        from poly_coeff_zero[OF vanish r1]
        have "real (?r choose 1) * f (cfg m a 1 x z) = 0" .
        moreover have "real (?r choose 1) \<noteq> 0" using mn by simp
        ultimately have "f (cfg m a 1 x z) = 0" by simp
        moreover have "cfg m a 1 x z = (\<lambda>i. if i < Suc m then a i else x)"
          by (rule ext) (auto simp: cfg_def z_def less_Suc_eq)
        ultimately show "f (\<lambda>i. if i < Suc m then a i else x) = 0" by simp
      qed
    qed
  qed
  have "f (\<lambda>i. if i < n then v i else v 0) = 0" using S[of n] by simp
  moreover have "f (\<lambda>i. if i < n then v i else v 0) = f v" by (intro dep) simp
  ultimately show ?thesis by simp
qed

end

end
