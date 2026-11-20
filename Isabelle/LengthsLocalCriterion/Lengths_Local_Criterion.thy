(*  Title:      Lengths_Local_Criterion.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: the local criterion and its two consequences
   "Corollary bounded" and "Theorem sharp" (multiplicity four) of the paper "Rational sums-of-squares lengths of
   biquadratic forms and orthogonal dilations" (Carles Marín, in preparation), Section "One interior eigenvalue".

   PARTIAL formalization. The local criterion of the paper (Theorem finite) is taken as a named assumption of the
   locale lengths_local; it characterizes "excess at most h" and "defect at most e" by the existence of local signs
   satisfying conditions (1) and (2). From it, and from a few standard facts on the Hilbert symbol, squares in the
   local fields and the Hasse invariant (all named assumptions of the locale lengths_data), the file proves:
   (a) the corollary bounded: defect at most min(m, c_m) and excess at most min(m, c_m) + 3;
   (b) the theorem sharp for multiplicity m = 4: excess 7 holds if and only if the defect is 4 and some split
       place v has -D a square and Hasse invariant -1.
   There are no proof gaps and no quick-and-dirty mode. The number theory of Q_v (Hilbert symbol, Hasse invariant,
   Hasse-Minkowski, the theory of quadratic forms behind Theorem finite) is NOT formalized: it enters only through
   the named assumptions, each commented with the sentence of the paper that it replaces. The local data are abstract
   parameters of the locale.

   Findings of the formalization. (1) The paper states Theorem finite with "the least h"; the characterization of
   "excess at most h" that follows is "some h' <= h satisfies the conditions", and the proof of Theorem sharp needs
   the monotonicity R_v(t,D) contained in R_v(t+1,D), which the paper does not state: the case analysis of the
   paper treats h = 6 only, while h = 4 and h = 5 with d = 4 must also be excluded. (2) The step "w_v(q) = -1 at a
   split place with -D a square" tacitly needs that place to lie in S_d, for d = 4 and for d = 6, which is the fact
   that the Hasse invariant of q is trivial outside S_d; the paper does not state it.
*)
theory Lengths_Local_Criterion
  imports Main "HOL.Rat"
begin

section \<open>The constant c_m of the corollary\<close>

definition cm :: "nat \<Rightarrow> nat" where
  "cm n = (if odd n then 3 else 4)"

section \<open>The locale of abstract local data and the standard local facts\<close>

locale lengths_data =
  fixes sq :: "'p \<Rightarrow> rat \<Rightarrow> bool"          \<comment> \<open>sq v x: x is a square in Q_v\<close>
    and hil :: "'p \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int"  \<comment> \<open>hil v a b: the Hilbert symbol (a,b)_v\<close>
    and split :: "'p \<Rightarrow> bool"             \<comment> \<open>v splits in L = Q(sqrt(-delta))\<close>
    and D :: rat                             \<comment> \<open>the determinant of q, modulo squares\<close>
    and dl :: rat                            \<comment> \<open>delta = 1 - lambda^2\<close>
    and m :: nat                             \<comment> \<open>the multiplicity, dimension of q\<close>
    and wq :: "'p \<Rightarrow> int"                \<comment> \<open>w_v(q): the Hasse invariant of q at v\<close>
    and Sd :: "nat \<Rightarrow> 'p set"            \<comment> \<open>S_d: 2, the primes dividing delta, D_d and the entries of a diagonalization of q\<close>
  assumes delta_pos: "0 < dl"
    \<comment> \<open>Bookkeeping: delta = 1 - lambda^2 is positive (the paper takes lambda in (-1,1)).\<close>
    and D_ne0: "D \<noteq> 0"
    \<comment> \<open>Bookkeeping: q is nondegenerate, so det q is nonzero.\<close>
    and hilbert_values: "\<And>v a b. a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> hil v a b = 1 \<or> hil v a b = -1"
    \<comment> \<open>The Hilbert symbol takes the values +1 and -1 (definition of the symbol; used for the signs of the paper).\<close>
    and wq_values: "\<And>v. wq v = 1 \<or> wq v = -1"
    \<comment> \<open>The Hasse invariant w_v(q) = prod_{i<j} (a_i,a_j)_v is a product of Hilbert symbols, hence +1 or -1.\<close>
    and wq_one_outside: "\<And>d v. v \<notin> Sd d \<Longrightarrow> wq v = 1"
    \<comment> \<open>S_d contains the entries of a diagonalization of q, so outside S_d these entries are units and the Hasse
        invariant is trivial (used for the place v of Theorem sharp: w_v(q) = -1 forces v in S_d).\<close>
    and hil_sym: "\<And>v a b. a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> hil v a b = hil v b a"
    \<comment> \<open>Symmetry of the Hilbert symbol; used where the paper writes (-1,D)_v = (D,-1)_v ("w_v(p) = w_v(q)(-1,D)_v").\<close>
    and hil_self: "\<And>v a. a \<noteq> 0 \<Longrightarrow> hil v a a = hil v a (-1)"
    \<comment> \<open>(a,a)_v = (a,-1)_v; used where the paper writes w_v(b) = w_v(p)(D,D)_v = w_v(q).\<close>
    and hil_square_arg: "\<And>v a b c. a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> hil v a (b * c\<^sup>2) = hil v a b"
    \<comment> \<open>The symbol depends only on square classes; used for D_d = det q * delta^k with k even, equal to D modulo
        squares ("det p = D delta^4 = D").\<close>
    and hil_of_square: "\<And>v a b. a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> sq v a \<Longrightarrow> hil v a b = 1"
    \<comment> \<open>A square has trivial symbol with everything; used for the case d = 6, h = 6 ("p is isometric to I_6 ...").\<close>
    and sq_scale: "\<And>v x c. c \<noteq> 0 \<Longrightarrow> sq v (x * c\<^sup>2) = sq v x"
    \<comment> \<open>Being a square in Q_v depends only on the square class; used to compare -D_4 with -D.\<close>
    and sq_one: "\<And>v. sq v 1"
    \<comment> \<open>1 is a square in Q_v.\<close>
    and sq_mul: "\<And>v x y. sq v x \<Longrightarrow> sq v y \<Longrightarrow> sq v (x * y)"
    \<comment> \<open>A product of squares is a square.\<close>
    and split_sq: "\<And>v. split v \<Longrightarrow> sq v (-dl)"
    \<comment> \<open>v splits in L = Q(sqrt(-delta)) exactly when -delta is a square in Q_v ("at a split prime -delta is a
        square", in the proof of Theorem finite); only the implication is used.\<close>
begin

section \<open>The sets R_v(t,D), the dimension D_d, the sign of condition (2), and the local conditions\<close>

text \<open>R v t Dx: the Hasse invariants of the t-dimensional forms of determinant Dx over Q_v, exactly as in the
  paragraph "We use the following local facts".\<close>

definition R :: "'p \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> int set" where
  "R v t Dx = (if t = 0 then (if sq v Dx then {1} else {})
               else if t = 1 then {1}
               else if t = 2 then (if sq v (-Dx) then {1} else {1, -1})
               else {1, -1})"

text \<open>D_d = det q * delta^k with k = (m+d)/2.\<close>

definition Dd :: "nat \<Rightarrow> rat" where
  "Dd d = D * dl ^ ((m + d) div 2)"

text \<open>The sign of condition (2): w_v(q) (det q, D_d)_v (-1,-1)_v^{k(k-1)/2} with k = (m+d)/2.\<close>

definition sgn2 :: "nat \<Rightarrow> 'p \<Rightarrow> int" where
  "sgn2 d v = wq v * hil v D (Dd d) * (hil v (-1) (-1)) ^ (((m + d) div 2) * (((m + d) div 2) - 1) div 2)"

text \<open>The conditions (1) and (2) of Theorem finite for the pair (h,d), at every v of S_d; crit0 is the same
  without the condition on the dimension h-d.\<close>

definition crit :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "crit h d \<longleftrightarrow> (\<forall>v\<in>Sd d. \<exists>e. e \<in> R v d (Dd d) \<and> e * hil v (Dd d) (-1) \<in> R v (h - d) (Dd d)
                          \<and> (split v \<longrightarrow> e = sgn2 d v))"

definition crit0 :: "nat \<Rightarrow> bool" where
  "crit0 d \<longleftrightarrow> (\<forall>v\<in>Sd d. \<exists>e. e \<in> R v d (Dd d) \<and> (split v \<longrightarrow> e = sgn2 d v))"

section \<open>Elementary facts\<close>

lemma dl_ne0: "dl \<noteq> 0"
  using delta_pos by simp

lemma Dd_ne0: "Dd d \<noteq> 0"
  using D_ne0 dl_ne0 by (simp add: Dd_def)

lemma pm_mul:
  assumes "a = 1 \<or> a = (-1::int)" "b = 1 \<or> b = (-1::int)"
  shows "a * b = 1 \<or> a * b = -1"
  using assms by auto

lemma pm_pow:
  assumes "a = 1 \<or> a = (-1::int)"
  shows "a ^ n = 1 \<or> a ^ n = -1"
proof (cases "a = 1")
  case True then show ?thesis by simp
next
  case False
  then have "a = -1" using assms by simp
  then show ?thesis by (cases "even n") simp_all
qed

lemma hv_DD: "hil v D (Dd d) = 1 \<or> hil v D (Dd d) = -1"
  by (rule hilbert_values[OF D_ne0 Dd_ne0])

lemma hv_Dm1: "hil v D (-1) = 1 \<or> hil v D (-1) = -1"
  by (rule hilbert_values[OF D_ne0]) simp

lemma hv_Ddm1: "hil v (Dd d) (-1) = 1 \<or> hil v (Dd d) (-1) = -1"
  by (rule hilbert_values[OF Dd_ne0]) simp

lemma hv_mm: "hil v (-1) (-1) = 1 \<or> hil v (-1) (-1) = -1"
  by (rule hilbert_values) simp_all

lemma sgn2_pm: "sgn2 d v = 1 \<or> sgn2 d v = -1"
proof -
  have p: "hil v (-1) (-1) ^ (((m + d) div 2) * (((m + d) div 2) - 1) div 2) = 1
         \<or> hil v (-1) (-1) ^ (((m + d) div 2) * (((m + d) div 2) - 1) div 2) = -1"
    by (rule pm_pow[OF hv_mm])
  have q: "wq v * hil v D (Dd d) = 1 \<or> wq v * hil v D (Dd d) = -1"
    by (rule pm_mul[OF wq_values hv_DD])
  show ?thesis unfolding sgn2_def by (rule pm_mul[OF q p])
qed

section \<open>Facts on R_v(t,D)\<close>

lemma R_sub: "R v t Dx \<subseteq> {1, -1}"
  by (auto simp: R_def split: if_splits)

lemma R_zero: "R v 0 Dx \<subseteq> {1}"
  by (auto simp: R_def split: if_splits)

lemma R_ge3:
  assumes "3 \<le> t"
  shows "R v t Dx = {1, -1}"
proof -
  have "t \<noteq> 0" "t \<noteq> 1" "t \<noteq> 2" using assms by simp_all
  then show ?thesis by (simp add: R_def)
qed

lemma R_two_sq: "sq v (-Dx) \<Longrightarrow> R v 2 Dx = {1}"
  by (simp add: R_def)

lemma R_two_nsq: "\<not> sq v (-Dx) \<Longrightarrow> R v 2 Dx = {1, -1}"
  by (simp add: R_def)

lemma R_one:
  assumes "1 \<le> t"
  shows "1 \<in> R v t Dx"
proof (cases "t = 1")
  case True then show ?thesis by (simp add: R_def)
next
  case False
  show ?thesis
  proof (cases "t = 2")
    case True then show ?thesis by (simp add: R_def)
  next
    case False2: False
    have "3 \<le> t" using assms \<open>t \<noteq> 1\<close> False2 by simp
    then show ?thesis using R_ge3 by simp
  qed
qed

lemma R_mono:
  assumes "t \<le> t'"
  shows "R v t Dx \<subseteq> R v t' Dx"
proof -
  have c: "(t = 0 \<and> t' = 0) \<or> (t = 0 \<and> 1 \<le> t') \<or> t = 1 \<or> (t = 2 \<and> t' = 2) \<or> (t = 2 \<and> 3 \<le> t') \<or> 3 \<le> t"
    using assms by arith
  then show ?thesis
  proof (elim disjE)
    assume h: "t = 0 \<and> t' = 0"
    then show ?thesis by simp
  next
    assume h: "t = 0 \<and> 1 \<le> t'"
    have t0: "t = 0" using h by simp
    have "{1} \<subseteq> R v t' Dx" using R_one h by simp
    then show ?thesis unfolding t0 using R_zero by blast
  next
    assume h: "t = 1"
    have t1: "1 \<le> t'" using assms h by simp
    have "R v 1 Dx = {1}" by (simp add: R_def)
    moreover have "{1} \<subseteq> R v t' Dx" using R_one t1 by simp
    ultimately show ?thesis unfolding h by simp
  next
    assume h: "t = 2 \<and> t' = 2"
    then show ?thesis by simp
  next
    assume h: "t = 2 \<and> 3 \<le> t'"
    have "R v t' Dx = {1, -1}" using R_ge3 h by simp
    then show ?thesis using R_sub by blast
  next
    assume h: "3 \<le> t"
    have t3: "3 \<le> t'" using assms h by simp
    show ?thesis using R_ge3 h t3 by simp
  qed
qed

section \<open>Facts on the conditions (1) and (2)\<close>

lemma crit_crit0: "crit h d \<Longrightarrow> crit0 d"
  unfolding crit_def crit0_def by blast

lemma crit_mono:
  assumes "crit h d" "h \<le> k"
  shows "crit k d"
  unfolding crit_def
proof
  fix v assume v: "v \<in> Sd d"
  from assms(1) v obtain e where e1: "e \<in> R v d (Dd d)"
    and e2: "e * hil v (Dd d) (-1) \<in> R v (h - d) (Dd d)" and e3: "split v \<longrightarrow> e = sgn2 d v"
    unfolding crit_def by blast
  have "R v (h - d) (Dd d) \<subseteq> R v (k - d) (Dd d)" using assms(2) by (intro R_mono) simp
  with e2 have "e * hil v (Dd d) (-1) \<in> R v (k - d) (Dd d)" by blast
  then show "\<exists>e. e \<in> R v d (Dd d) \<and> e * hil v (Dd d) (-1) \<in> R v (k - d) (Dd d)
               \<and> (split v \<longrightarrow> e = sgn2 d v)"
    using e1 e3 by blast
qed

lemma crit0_crit3:
  assumes "crit0 d"
  shows "crit (d + 3) d"
  unfolding crit_def
proof
  fix v assume v: "v \<in> Sd d"
  from assms v obtain e where e1: "e \<in> R v d (Dd d)" and e3: "split v \<longrightarrow> e = sgn2 d v"
    unfolding crit0_def by blast
  have epm: "e = 1 \<or> e = -1" using e1 R_sub by blast
  have p: "e * hil v (Dd d) (-1) = 1 \<or> e * hil v (Dd d) (-1) = -1" by (rule pm_mul[OF epm hv_Ddm1])
  have "R v ((d + 3) - d) (Dd d) = {1, -1}" using R_ge3 by simp
  then have "e * hil v (Dd d) (-1) \<in> R v ((d + 3) - d) (Dd d)" using p by simp
  then show "\<exists>e. e \<in> R v d (Dd d) \<and> e * hil v (Dd d) (-1) \<in> R v ((d + 3) - d) (Dd d)
               \<and> (split v \<longrightarrow> e = sgn2 d v)"
    using e1 e3 by blast
qed

end

section \<open>The locale with Theorem finite as a named assumption\<close>

locale lengths_local = lengths_data +
  fixes exc_le :: "nat \<Rightarrow> bool"             \<comment> \<open>exc_le h: the excess l_Q(H) - n is at most h\<close>
    and def_le :: "nat \<Rightarrow> bool"             \<comment> \<open>def_le e: the defect d_Q(H) is at most e\<close>
  assumes thm_finite_exc:
    "\<And>h. exc_le h \<longleftrightarrow> (\<exists>h'. h' \<le> h \<and> h' \<le> m + 3 \<and> (\<exists>d. d mod 2 = m mod 2 \<and> d \<le> h' \<and> crit h' d))"
    \<comment> \<open>Theorem finite, first sentence: the excess is the least h <= m+3 for which some d with d = m mod 2 and
        0 <= d <= h satisfies, at every v of S_d, conditions (1) and (2). Hence the excess is at most h exactly when
        some h' <= h satisfies them.\<close>
    and thm_finite_def:
    "\<And>e. def_le e \<longleftrightarrow> (\<exists>d. d \<le> e \<and> d \<le> m \<and> d mod 2 = m mod 2 \<and> crit0 d)"
    \<comment> \<open>Theorem finite, second sentence: the defect is the least d <= m, d = m mod 2, for which the conditions hold
        without the condition on the dimension h-d.\<close>
    and thm_one_defect: "def_le m"
    \<comment> \<open>Proof of Corollary bounded: "T = H has defect m" (Theorem one: the defect form delta q of dimension m).\<close>
    and thm_one_excess: "exc_le (m + 3)"
    \<comment> \<open>Theorem one: "In particular l_Q(H) <= n + m + 3" (Lemma d3 applied to the defect form of T = H).\<close>
begin

lemma exc_intro:
  assumes "h \<le> m + 3" "d mod 2 = m mod 2" "d \<le> h" "crit h d"
  shows "exc_le h"
  unfolding thm_finite_exc using assms by blast

lemma exc_elim:
  assumes "exc_le h"
  obtains h' d where "h' \<le> h" "h' \<le> m + 3" "d mod 2 = m mod 2" "d \<le> h'" "crit h' d"
  using assms unfolding thm_finite_exc by blast

lemma exc_mono:
  assumes "exc_le h" "h \<le> k"
  shows "exc_le k"
proof -
  from assms(1) obtain h' d where "h' \<le> h" "h' \<le> m + 3" "d mod 2 = m mod 2" "d \<le> h'" "crit h' d"
    by (rule exc_elim)
  then show ?thesis using assms(2) unfolding thm_finite_exc by (intro exI[where x = h']) auto
qed

lemma def_intro:
  assumes "d \<le> m" "d mod 2 = m mod 2" "crit0 d"
  shows "def_le d"
  unfolding thm_finite_def using assms by blast

lemma def_elim:
  assumes "def_le e"
  obtains d where "d \<le> e" "d \<le> m" "d mod 2 = m mod 2" "crit0 d"
  using assms unfolding thm_finite_def by blast

lemma def_mono:
  assumes "def_le e" "e \<le> k"
  shows "def_le k"
proof -
  from assms(1) obtain d where "d \<le> e" "d \<le> m" "d mod 2 = m mod 2" "crit0 d" by (rule def_elim)
  then show ?thesis using assms(2) unfolding thm_finite_def by (intro exI[where x = d]) auto
qed

section \<open>Corollary bounded\<close>

theorem cor_bounded:
  "def_le (min m (cm m)) \<and> exc_le (min m (cm m) + 3)"
proof (cases "m \<le> cm m")
  case True
  then have mn: "min m (cm m) = m" by simp
  show ?thesis unfolding mn using thm_one_defect thm_one_excess by blast
next
  case False
  then have lt: "cm m < m" by simp
  have mn: "min m (cm m) = cm m" using lt by simp
  have par: "cm m mod 2 = m mod 2"
    by (cases "even m") (simp_all add: cm_def even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one)
  have ge3: "3 \<le> cm m" by (simp add: cm_def)
  have c0: "crit0 (cm m)"
    unfolding crit0_def
  proof
    fix v assume "v \<in> Sd (cm m)"
    have "sgn2 (cm m) v \<in> R v (cm m) (Dd (cm m))"
      using R_ge3[OF ge3] sgn2_pm by simp
    then show "\<exists>e. e \<in> R v (cm m) (Dd (cm m)) \<and> (split v \<longrightarrow> e = sgn2 (cm m) v)"
      by blast
  qed
  have defp: "def_le (cm m)" by (rule def_intro[OF _ par c0]) (use lt in simp)
  have excp: "exc_le (cm m + 3)"
    by (rule exc_intro[OF _ par _ crit0_crit3[OF c0]]) (use lt in simp_all)
  show ?thesis unfolding mn using defp excp by blast
qed

section \<open>Theorem sharp for multiplicity four\<close>

lemma Dd4:
  assumes m4: "m = 4"
  shows "Dd 4 = D * (dl\<^sup>2)\<^sup>2"
proof -
  have e1: "Dd 4 = D * dl ^ 4" unfolding Dd_def by (simp add: m4)
  have "D * dl ^ 4 = D * (dl\<^sup>2)\<^sup>2" by (simp add: power_mult)
  then show ?thesis using e1 by simp
qed

lemma sgn2_4:
  assumes m4: "m = 4"
  shows "sgn2 4 v = wq v * hil v D (-1)"
proof -
  have h1: "hil v D (Dd 4) = hil v D (-1)"
  proof -
    have "hil v D (D * (dl\<^sup>2)\<^sup>2) = hil v D D"
      by (rule hil_square_arg) (simp_all add: D_ne0 dl_ne0)
    also have "\<dots> = hil v D (-1)" by (rule hil_self[OF D_ne0])
    finally show ?thesis using Dd4[OF m4] by simp
  qed
  have pw: "hil v (-1) (-1) ^ 6 = 1" using hv_mm[where v = v] by auto
  have "sgn2 4 v = wq v * hil v D (Dd 4) * hil v (-1) (-1) ^ 6"
    unfolding sgn2_def by (simp add: m4)
  then show ?thesis using h1 pw by simp
qed

lemma hil_Dd4:
  assumes m4: "m = 4"
  shows "hil v (Dd 4) (-1) = hil v D (-1)"
proof -
  have "hil v (Dd 4) (-1) = hil v (-1) (Dd 4)" by (rule hil_sym[OF Dd_ne0]) simp
  also have "\<dots> = hil v (-1) (D * (dl\<^sup>2)\<^sup>2)" using Dd4[OF m4] by simp
  also have "\<dots> = hil v (-1) D" by (rule hil_square_arg) (simp_all add: D_ne0 dl_ne0)
  also have "\<dots> = hil v D (-1)" by (rule hil_sym) (simp_all add: D_ne0)
  finally show ?thesis .
qed

lemma sq_Dd4:
  assumes m4: "m = 4"
  shows "sq v (-Dd 4) = sq v (-D)"
proof -
  have "- Dd 4 = (-D) * (dl\<^sup>2)\<^sup>2" using Dd4[OF m4] by simp
  then show ?thesis using sq_scale[where c = "dl\<^sup>2" and x = "-D" and v = v] dl_ne0 by simp
qed

lemma sq_Dd6:
  assumes m4: "m = 4" and s: "split v" and sD: "sq v (-D)"
  shows "sq v (Dd 6)"
proof -
  have e1: "Dd 6 = D * dl ^ 5" unfolding Dd_def by (simp add: m4)
  have e2: "D * dl ^ 5 = ((-D) * (-dl)) * (dl\<^sup>2)\<^sup>2" by (simp add: power2_eq_square numeral_eq_Suc algebra_simps)
  have sq1: "sq v ((dl\<^sup>2)\<^sup>2)"
  proof -
    have "sq v (1 * (dl\<^sup>2)\<^sup>2) = sq v 1" by (rule sq_scale) (simp add: dl_ne0)
    then show ?thesis using sq_one by simp
  qed
  have "sq v ((-D) * (-dl))" by (rule sq_mul[OF sD split_sq[OF s]])
  then have "sq v (((-D) * (-dl)) * (dl\<^sup>2)\<^sup>2)" by (rule sq_mul) (rule sq1)
  then show ?thesis using e1 e2 by simp
qed

lemma Dd6_ne0: "Dd 6 \<noteq> 0" by (rule Dd_ne0)

text \<open>If no split place has -D a square and Hasse invariant -1, then (h,d) = (6,4) satisfies the conditions.\<close>

lemma crit_6_4:
  assumes m4: "m = 4" and nov: "\<And>v. split v \<Longrightarrow> sq v (-D) \<Longrightarrow> wq v \<noteq> -1"
  shows "crit 6 4"
  unfolding crit_def
proof
  fix v assume "v \<in> Sd 4"
  have r4: "R v 4 (Dd 4) = {1, -1}" by (rule R_ge3) simp
  have hh: "hil v D (-1) * hil v D (-1) = 1" using hv_Dm1[where v = v] by auto
  show "\<exists>e. e \<in> R v 4 (Dd 4) \<and> e * hil v (Dd 4) (-1) \<in> R v (6 - 4) (Dd 4) \<and> (split v \<longrightarrow> e = sgn2 4 v)"
  proof (cases "split v")
    case True
    have prod: "sgn2 4 v * hil v (Dd 4) (-1) = wq v"
    proof -
      have "sgn2 4 v * hil v (Dd 4) (-1) = wq v * (hil v D (-1) * hil v D (-1))"
        using sgn2_4[OF m4] hil_Dd4[OF m4] by (simp add: mult.assoc)
      then show ?thesis using hh by simp
    qed
    have in2: "wq v \<in> R v 2 (Dd 4)"
    proof (cases "sq v (-D)")
      case True2: True
      have "wq v \<noteq> -1" using nov True True2 by blast
      then have "wq v = 1" using wq_values by blast
      then show ?thesis using R_one by simp
    next
      case False2: False
      then have "\<not> sq v (-Dd 4)" using sq_Dd4[OF m4] by simp
      then show ?thesis using R_two_nsq wq_values by auto
    qed
    show ?thesis
      by (rule exI[where x = "sgn2 4 v"])
         (use True prod in2 sgn2_pm r4 in \<open>simp add: r4\<close>)
  next
    case False
    have e: "hil v (Dd 4) (-1) \<in> R v 4 (Dd 4)" using r4 hv_Ddm1[where v = v and d = 4] by simp
    have "hil v (Dd 4) (-1) * hil v (Dd 4) (-1) = 1" using hv_Ddm1[where v = v and d = 4] by auto
    then have "hil v (Dd 4) (-1) * hil v (Dd 4) (-1) \<in> R v (6 - 4) (Dd 4)" using R_one by simp
    then show ?thesis using e False by blast
  qed
qed

lemma not_exc6:
  assumes m4: "m = 4" and nd: "\<not> def_le 3"
    and v0: "split v0" "sq v0 (-D)" "wq v0 = -1"
  shows "\<not> exc_le 6"
proof
  assume ex: "exc_le 6"
  obtain h d where hh: "h \<le> 6" "h \<le> m + 3" "d mod 2 = m mod 2" "d \<le> h" "crit h d"
    using ex by (rule exc_elim)
  have dcases: "d = 0 \<or> d = 2 \<or> d = 4 \<or> d = 6" using hh m4 by arith
  have wne: "wq v0 \<noteq> 1" using v0(3) by simp
  show False
  using dcases
  proof (elim disjE)
    assume d: "d = 0"
    have c0: "crit0 d" using hh(5) by (rule crit_crit0)
    have "def_le d" by (rule def_intro[OF _ _ c0]) (use d m4 hh(3) in simp_all)
    then have "def_le 3" by (rule def_mono) (use d in simp)
    then show False using nd by blast
  next
    assume d: "d = 2"
    have c0: "crit0 d" using hh(5) by (rule crit_crit0)
    have "def_le d" by (rule def_intro[OF _ _ c0]) (use d m4 hh(3) in simp_all)
    then have "def_le 3" by (rule def_mono) (use d in simp)
    then show False using nd by blast
  next
    assume d: "d = 4"
    have c64: "crit 6 4" using crit_mono[where h = h and k = 6 and d = d] hh(5) hh(1) d by simp
    have v0S: "v0 \<in> Sd 4"
    proof (rule ccontr)
      assume "v0 \<notin> Sd 4"
      then show False using wq_one_outside wne by blast
    qed
    obtain e where e2: "e * hil v0 (Dd 4) (-1) \<in> R v0 (6 - 4) (Dd 4)" and e3: "split v0 \<longrightarrow> e = sgn2 4 v0"
      using c64 v0S unfolding crit_def by blast
    have sqn: "sq v0 (-Dd 4)" using sq_Dd4[OF m4] v0(2) by simp
    have r2: "R v0 (6 - 4) (Dd 4) = {1}" using R_two_sq[OF sqn] by simp
    have eq: "e = wq v0 * hil v0 D (-1)" using e3 v0(1) sgn2_4[OF m4] by simp
    have hh2: "hil v0 D (-1) * hil v0 D (-1) = 1" using hv_Dm1[where v = v0] by auto
    have "e * hil v0 (Dd 4) (-1) = wq v0 * (hil v0 D (-1) * hil v0 D (-1))"
      using eq hil_Dd4[OF m4] by (simp add: mult.assoc)
    then have "e * hil v0 (Dd 4) (-1) = -1" using hh2 v0(3) by simp
    then show False using e2 r2 by simp
  next
    assume d: "d = 6"
    have h6: "h = 6" using hh(1) hh(4) d by simp
    have v0S: "v0 \<in> Sd 6"
    proof (rule ccontr)
      assume "v0 \<notin> Sd 6"
      then show False using wq_one_outside wne by blast
    qed
    obtain e where e2: "e * hil v0 (Dd 6) (-1) \<in> R v0 (6 - 6) (Dd 6)" and e3: "split v0 \<longrightarrow> e = sgn2 6 v0"
      using hh(5) v0S d h6 unfolding crit_def by blast
    have sq6: "sq v0 (Dd 6)" by (rule sq_Dd6[OF m4 v0(1) v0(2)])
    have a1: "hil v0 D (Dd 6) = 1"
    proof -
      have "hil v0 D (Dd 6) = hil v0 (Dd 6) D" by (rule hil_sym[OF D_ne0 Dd_ne0])
      also have "\<dots> = 1" by (rule hil_of_square[OF Dd_ne0 D_ne0 sq6])
      finally show ?thesis .
    qed
    have a2: "hil v0 (Dd 6) (-1) = 1" by (rule hil_of_square[OF Dd_ne0 _ sq6]) simp
    have pw: "hil v0 (-1) (-1) ^ 10 = 1" using hv_mm[where v = v0] by auto
    have "sgn2 6 v0 = wq v0 * hil v0 D (Dd 6) * hil v0 (-1) (-1) ^ 10"
      unfolding sgn2_def by (simp add: m4)
    then have "sgn2 6 v0 = -1" using a1 pw v0(3) by simp
    then have "e = -1" using e3 v0(1) by simp
    then have "e * hil v0 (Dd 6) (-1) = -1" using a2 by simp
    then have "-1 \<in> R v0 0 (Dd 6)" using e2 by simp
    moreover have "R v0 0 (Dd 6) \<subseteq> {1}" by (rule R_zero)
    ultimately show False by auto
  qed
qed

theorem sharp:
  assumes m4: "m = 4"
  shows "(exc_le 7 \<and> \<not> exc_le 6)
         \<longleftrightarrow> (def_le 4 \<and> \<not> def_le 3 \<and> (\<exists>v. split v \<and> sq v (-D) \<and> wq v = -1))"
proof -
  have cm4: "min m (cm m) = 4" by (simp add: m4 cm_def)
  have cb: "def_le 4" "exc_le 7" using cor_bounded unfolding cm4 by simp_all
  show ?thesis
  proof
    assume H: "exc_le 7 \<and> \<not> exc_le 6"
    have n6: "\<not> exc_le 6" using H by blast
    have nd: "\<not> def_le 3"
    proof
      assume dl3: "def_le 3"
      obtain d where d: "d \<le> 3" "d \<le> m" "d mod 2 = m mod 2" "crit0 d" using dl3 by (rule def_elim)
      have "exc_le (d + 3)"
        by (rule exc_intro[OF _ d(3) _ crit0_crit3[OF d(4)]]) (use d m4 in simp_all)
      then have "exc_le 6" by (rule exc_mono) (use d in simp)
      then show False using n6 by blast
    qed
    have "\<exists>v. split v \<and> sq v (-D) \<and> wq v = -1"
    proof (rule ccontr)
      assume "\<not> (\<exists>v. split v \<and> sq v (-D) \<and> wq v = -1)"
      then have nov: "\<And>v. split v \<Longrightarrow> sq v (-D) \<Longrightarrow> wq v \<noteq> -1" by blast
      have "exc_le 6" by (rule exc_intro[OF _ _ _ crit_6_4[OF m4 nov]]) (use m4 in simp_all)
      then show False using n6 by blast
    qed
    then show "def_le 4 \<and> \<not> def_le 3 \<and> (\<exists>v. split v \<and> sq v (-D) \<and> wq v = -1)" using cb(1) nd by blast
  next
    assume H: "def_le 4 \<and> \<not> def_le 3 \<and> (\<exists>v. split v \<and> sq v (-D) \<and> wq v = -1)"
    then obtain v0 where v0: "split v0" "sq v0 (-D)" "wq v0 = -1" by blast
    have "\<not> exc_le 6" using not_exc6[OF m4 _ v0] H by blast
    then show "exc_le 7 \<and> \<not> exc_le 6" using cb(2) by blast
  qed
qed

end

end
