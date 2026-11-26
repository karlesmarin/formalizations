(*  Title:      Caballero_Nonint.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation), Theorem 7.10 (thm:nonint):
   the shift of two templates is never an integer.

   A template of level a is the vector (floor (u + h v)) for |h| <= a, with u, v in (0,1) (it is 0 at h = 0).
   If two templates e, e' have window sums over W_i = {i-a, ..., i} (0 <= i <= a) whose difference is one
   constant D, and e <> e', then a+1 does not divide D. Consequences, also proved here: two distinct templates
   with (N2) have S_-(e) and S_-(e') incongruent modulo a+1, and a class of templates whose window sums agree
   pairwise up to a constant has at most a+1 elements.

   The proof follows the paper: d_h = e_h - e'_h - k is periodic of period a+1 with zero window sums, its sign
   is the sign of an affine function of h, and an affine function cannot take the signs +,-,+ (or -,+,-).
*)
theory Caballero_Nonint
  imports Complex_Main
begin

section \<open>Definitions, as in the paper\<close>

text \<open>Templates of level a, as vectors on all of the integers, extended by 0 outside |h| <= a.\<close>
definition tvec :: "nat \<Rightarrow> (int \<Rightarrow> int) set" where
  "tvec a = {e. \<exists>u v :: real. 0 < u \<and> u < 1 \<and> 0 < v \<and> v < 1 \<and>
      (\<forall>h. e h = (if \<bar>h\<bar> \<le> int a then (floor (u + real_of_int h * v)) else 0))}"

text \<open>Window sum of e - e' over W_i = {i-a, ..., i}.\<close>
definition wsum :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "wsum a e e' i = (\<Sum>h = i - int a..i. e h - e' h)"

text \<open>The window sums of e - e' are all equal to the constant D.\<close>
definition const_wsum :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool" where
  "const_wsum a e e' D \<longleftrightarrow> (\<forall>i. 0 \<le> i \<and> i \<le> int a \<longrightarrow> wsum a e e' i = D)"

definition Sminus :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int" where
  "Sminus a e = (\<Sum>h = - int a..0. e h)"

text \<open>Condition (N2) of Theorem 7.8 (thm:allpos): every window sum equals S_-(e) - S_-(e').\<close>
definition N2 :: "nat \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool" where
  "N2 a e e' \<longleftrightarrow> const_wsum a e e' (Sminus a e - Sminus a e')"

section \<open>Elementary lemmas\<close>

lemma sum_snoc_int:
  fixes g :: "int \<Rightarrow> int"
  assumes "l \<le> u + 1"
  shows "sum g {l..u + 1} = sum g {l..u} + g (u + 1)"
proof -
  have "{l..u + 1} = insert (u + 1) {l..u}" using assms by auto
  then show ?thesis by simp
qed

lemma sum_cons_int:
  fixes g :: "int \<Rightarrow> int"
  assumes "l \<le> u"
  shows "sum g {l..u} = g l + sum g {l + 1..u}"
proof -
  have "{l..u} = insert l {l + 1..u}" using assms by auto
  then show ?thesis by simp
qed

lemma floor_gt_imp: "(floor (x :: real)) > (floor (y)) \<Longrightarrow> x > y"
  by (meson floor_mono not_less)

lemma affine_no_alt:
  fixes A B :: real and x y z :: int
  assumes "x < y" "y < z"
    and "0 < A + real_of_int x * B" "0 < A + real_of_int z * B"
  shows "0 < A + real_of_int y * B"
proof -
  let ?fx = "A + real_of_int x * B" and ?fz = "A + real_of_int z * B"
  have xy: "real_of_int x < real_of_int y" and yz: "real_of_int y < real_of_int z" using assms by simp_all
  have id: "(real_of_int z - real_of_int x) * (A + real_of_int y * B)
      = (real_of_int z - real_of_int y) * ?fx + (real_of_int y - real_of_int x) * ?fz"
    by (simp add: algebra_simps)
  have "0 < (real_of_int z - real_of_int y) * ?fx" using yz assms(3) by simp
  moreover have "0 < (real_of_int y - real_of_int x) * ?fz" using xy assms(4) by simp
  ultimately have "0 < (real_of_int z - real_of_int x) * (A + real_of_int y * B)" using id by linarith
  moreover have "0 < real_of_int z - real_of_int x" using xy yz by simp
  ultimately show ?thesis by (simp add: zero_less_mult_iff)
qed

lemma sum_zero_opposite:
  fixes d :: "int \<Rightarrow> int"
  assumes "finite A" "sum d A = 0" "x \<in> A" "0 < d x"
  shows "\<exists>y \<in> A. d y < 0"
proof (rule ccontr)
  assume "\<not> (\<exists>y \<in> A. d y < 0)"
  then have nn: "\<forall>y \<in> A - {x}. 0 \<le> d y" by auto
  have "d x \<le> sum d A" by (rule member_le_sum[OF assms(3) _ assms(1)]) (use nn in blast)
  with assms show False by simp
qed

section \<open>The core: periodicity and the sign argument\<close>

text \<open>Sign lemma. For d h = floor(u + h v) - floor(u' + h v') - k, a nonzero value has the sign of the
  affine function (u - u' - k) + h (v - v').\<close>
lemma sign_affine:
  fixes u v u' v' :: real and k h :: int
  shows "0 < floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k
           \<Longrightarrow> 0 < (u - u' - real_of_int k) + real_of_int h * (v - v')"
    and "floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k < 0
           \<Longrightarrow> (u - u' - real_of_int k) + real_of_int h * (v - v') < 0"
proof -
  have e: "floor (u' + real_of_int h * v') + k = floor (u' + real_of_int h * v' + real_of_int k)"
    by (rule floor_add_int)
  show "0 < floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k
           \<Longrightarrow> 0 < (u - u' - real_of_int k) + real_of_int h * (v - v')"
  proof -
    assume "0 < floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k"
    then have "floor (u' + real_of_int h * v' + real_of_int k) < floor (u + real_of_int h * v)"
      using e by linarith
    from floor_gt_imp[OF this] show ?thesis by (simp add: algebra_simps)
  qed
  show "floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k < 0
           \<Longrightarrow> (u - u' - real_of_int k) + real_of_int h * (v - v') < 0"
  proof -
    assume "floor (u + real_of_int h * v) - floor (u' + real_of_int h * v') - k < 0"
    then have "floor (u + real_of_int h * v) < floor (u' + real_of_int h * v' + real_of_int k)"
      using e by linarith
    from floor_gt_imp[OF this] show ?thesis by (simp add: algebra_simps)
  qed
qed

lemma nonint_core:
  fixes a :: nat and e e' :: "int \<Rightarrow> int" and u v u' v' :: real and k :: int
  assumes e: "\<And>h. e h = (if \<bar>h\<bar> \<le> int a then (floor (u + real_of_int h * v)) else 0)"
    and e': "\<And>h. e' h = (if \<bar>h\<bar> \<le> int a then (floor (u' + real_of_int h * v')) else 0)"
    and u: "0 < u" "u < 1" and u': "0 < u'" "u' < 1"
    and ws: "\<And>i. 0 \<le> i \<Longrightarrow> i \<le> int a \<Longrightarrow> (\<Sum>h = i - int a..i. e h - e' h) = k * (int a + 1)"
  shows "\<forall>h. e h = e' h"
proof -
  define A where "A = int a"
  define d where "d h = e h - e' h - k" for h
  have ws0: "\<And>i. 0 \<le> i \<Longrightarrow> i \<le> A \<Longrightarrow> (\<Sum>h = i - A..i. d h) = 0"
  proof -
    fix i assume i: "0 \<le> i" "i \<le> A"
    have "(\<Sum>h = i - A..i. d h) = (\<Sum>h = i - A..i. e h - e' h) - (\<Sum>h = i - A..i. k)"
      unfolding d_def by (simp add: sum_subtractf)
    also have "(\<Sum>h = i - A..i. k) = (A + 1) * k"
      using i by (simp add: A_def)
    finally show "(\<Sum>h = i - A..i. d h) = 0"
      using ws[of i] i by (simp add: A_def algebra_simps)
  qed
  have per: "\<And>h. - A \<le> h \<Longrightarrow> h \<le> - 1 \<Longrightarrow> d (h + (A + 1)) = d h"
  proof -
    fix h assume h: "- A \<le> h" "h \<le> - 1"
    define i where "i = h + A"
    have i: "0 \<le> i" "i \<le> A - 1" using h by (simp_all add: i_def)
    have w0: "(\<Sum>j = i - A..i. d j) = 0" using ws0[of i] i by simp
    have w1: "(\<Sum>j = (i + 1) - A..i + 1. d j) = 0" using ws0[of "i + 1"] i by simp
    have s1: "sum d {i - A..i + 1} = sum d {i - A..i} + d (i + 1)"
      using sum_snoc_int[of "i - A" i d] i by simp
    have s2: "sum d {i - A..i + 1} = d (i - A) + sum d {i - A + 1..i + 1}"
      using sum_cons_int[of "i - A" "i + 1" d] i by simp
    have "i - A + 1 = i + 1 - A" by simp
    with s1 s2 w0 w1 have "d (i + 1) = d (i - A)" by simp
    moreover have "i - A = h" "i + 1 = h + (A + 1)" by (simp_all add: i_def)
    ultimately show "d (h + (A + 1)) = d h" by simp
  qed
  have d_def_expl: "\<And>h. \<bar>h\<bar> \<le> A \<Longrightarrow> d h = (floor (u + real_of_int h * v)) - (floor (u' + real_of_int h * v')) - k"
    using e e' by (simp add: d_def A_def)
  have sgn_pos: "\<And>h. \<bar>h\<bar> \<le> A \<Longrightarrow> 0 < d h \<Longrightarrow> 0 < (u - u' - real_of_int k) + real_of_int h * (v - v')"
    using sign_affine(1)[where u = u and v = v and u' = u' and v' = v' and k = k] d_def_expl by simp
  have sgn_neg: "\<And>h. \<bar>h\<bar> \<le> A \<Longrightarrow> d h < 0 \<Longrightarrow> (u - u' - real_of_int k) + real_of_int h * (v - v') < 0"
    using sign_affine(2)[where u = u and v = v and u' = u' and v' = v' and k = k] d_def_expl by simp
  text \<open>No three indices p < q < p + (A+1) with d p, d (p+A+1) of one sign and d q of the other.\<close>
  have key: "\<And>p q. p < q \<Longrightarrow> - A \<le> p \<Longrightarrow> p \<le> - 1 \<Longrightarrow> q \<le> 0 \<Longrightarrow> 0 < d p \<Longrightarrow> d q < 0 \<Longrightarrow> False"
  proof -
    fix p q assume pq: "p < q" "- A \<le> p" "p \<le> - 1" "q \<le> 0" "0 < d p" "d q < 0"
    have dp: "d (p + (A + 1)) = d p" using per pq by simp
    have rng: "\<bar>p + (A + 1)\<bar> \<le> A" using pq by (simp add: abs_le_iff)
    have "0 < (u - u' - real_of_int k) + real_of_int (p + (A + 1)) * (v - v')"
      using sgn_pos[OF rng] dp pq by simp
    moreover have "0 < (u - u' - real_of_int k) + real_of_int p * (v - v')"
      using sgn_pos[of p] pq by (simp add: abs_le_iff)
    moreover have "(u - u' - real_of_int k) + real_of_int q * (v - v') < 0"
      using sgn_neg[of q] pq by (simp add: abs_le_iff)
    ultimately show False
      using affine_no_alt[of p q "p + (A + 1)" "u - u' - real_of_int k" "v - v'"] pq by simp
  qed
  have key2: "\<And>p q. p < q \<Longrightarrow> - A \<le> p \<Longrightarrow> p \<le> - 1 \<Longrightarrow> q \<le> 0 \<Longrightarrow> d p < 0 \<Longrightarrow> 0 < d q \<Longrightarrow> False"
  proof -
    fix p q assume pq: "p < q" "- A \<le> p" "p \<le> - 1" "q \<le> 0" "d p < 0" "0 < d q"
    have dp: "d (p + (A + 1)) = d p" using per pq by simp
    have rng: "\<bar>p + (A + 1)\<bar> \<le> A" using pq by (simp add: abs_le_iff)
    have "(u - u' - real_of_int k) + real_of_int (p + (A + 1)) * (v - v') < 0"
      using sgn_neg[OF rng] dp pq by simp
    moreover have "(u - u' - real_of_int k) + real_of_int p * (v - v') < 0"
      using sgn_neg[of p] pq by (simp add: abs_le_iff)
    moreover have "0 < (u - u' - real_of_int k) + real_of_int q * (v - v')"
      using sgn_pos[of q] pq by (simp add: abs_le_iff)
    ultimately show False
      using affine_no_alt[of p q "p + (A + 1)" "- (u - u' - real_of_int k)" "- (v - v')"] pq
      by (simp add: algebra_simps)
  qed
  text \<open>So d vanishes on [-A, 0].\<close>
  have zero_low: "\<And>x. - A \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> d x = 0"
  proof (rule ccontr)
    fix x assume x: "- A \<le> x" "x \<le> 0" "d x \<noteq> 0"
    have sum0: "(\<Sum>h = - A..0. d h) = 0" using ws0[of 0] by (simp add: A_def)
    have xin: "x \<in> {- A..0}" using x by simp
    obtain y where y: "y \<in> {- A..0}" "d x * d y < 0"
    proof (cases "0 < d x")
      case True
      from sum_zero_opposite[OF _ sum0 xin True] obtain y where "y \<in> {- A..0}" "d y < 0" by auto
      with True show ?thesis using that by (simp add: mult_pos_neg)
    next
      case False
      with x have neg: "d x < 0" by simp
      have "(\<Sum>h = - A..0. - d h) = 0" using sum0 by (simp add: sum_negf)
      from sum_zero_opposite[of "{- A..0}" "\<lambda>h. - d h" x, OF _ this xin] neg
      obtain y where "y \<in> {- A..0}" "0 < d y" by auto
      with neg show ?thesis using that by (simp add: mult_neg_pos)
    qed
    then have yy: "- A \<le> y" "y \<le> 0" and ne: "d y \<noteq> 0" "x \<noteq> y"
      using mult_less_0_iff by auto
    from y(2) have opp: "(0 < d x \<and> d y < 0) \<or> (d x < 0 \<and> 0 < d y)"
      by (auto simp: mult_less_0_iff)
    show False
    proof (cases "x < y")
      case True
      with opp x yy show False using key[of x y] key2[of x y] by auto
    next
      case False
      with ne have "y < x" by auto
      with opp x yy show False using key[of y x] key2[of y x] by auto
    qed
  qed
  have zero_high: "\<And>x. 0 < x \<Longrightarrow> x \<le> A \<Longrightarrow> d x = 0"
  proof -
    fix x assume x: "0 < x" "x \<le> A"
    have "d x = d (x - (A + 1) + (A + 1))" by simp
    also have "\<dots> = d (x - (A + 1))" using per[of "x - (A + 1)"] x by simp
    also have "\<dots> = 0" using zero_low[of "x - (A + 1)"] x by simp
    finally show "d x = 0" .
  qed
  have dz: "\<And>h. \<bar>h\<bar> \<le> A \<Longrightarrow> d h = 0"
  proof -
    fix h assume H: "\<bar>h\<bar> \<le> A"
    show "d h = 0"
    proof (cases "h \<le> 0")
      case True
      with H have "- A \<le> h" by (simp add: abs_le_iff)
      from zero_low[OF this True] show ?thesis .
    next
      case False
      with H have "0 < h" "h \<le> A" by (simp_all add: abs_le_iff)
      from zero_high[OF this] show ?thesis .
    qed
  qed
  have e0: "e 0 = 0" "e' 0 = 0" using e e' u u' by (simp_all add: A_def floor_eq_iff)
  have "k = 0" using dz[of 0] e0 by (simp add: d_def A_def)
  show ?thesis
  proof
    fix h
    show "e h = e' h"
    proof (cases "\<bar>h\<bar> \<le> A")
      case True
      with dz[of h] \<open>k = 0\<close> show ?thesis by (simp add: d_def)
    next
      case False
      then show ?thesis using e e' by (simp add: A_def)
    qed
  qed
qed

section \<open>Theorem 7.10\<close>

theorem nonint:
  assumes a: "1 \<le> a"
    and e: "e \<in> tvec a" and e': "e' \<in> tvec a" and ne: "e \<noteq> e'"
    and ws: "const_wsum a e e' D"
  shows "\<not> (int a + 1) dvd D"
proof
  assume "(int a + 1) dvd D"
  then obtain k where D: "D = (int a + 1) * k" by blast
  from e obtain u v where uv: "0 < u" "u < 1" "0 < v" "v < 1"
    and ev: "\<And>h. e h = (if \<bar>h\<bar> \<le> int a then (floor (u + real_of_int h * v)) else 0)"
    unfolding tvec_def by blast
  from e' obtain u' v' where uv': "0 < u'" "u' < 1" "0 < v'" "v' < 1"
    and ev': "\<And>h. e' h = (if \<bar>h\<bar> \<le> int a then (floor (u' + real_of_int h * v')) else 0)"
    unfolding tvec_def by blast
  have "\<And>i. 0 \<le> i \<Longrightarrow> i \<le> int a \<Longrightarrow> (\<Sum>h = i - int a..i. e h - e' h) = k * (int a + 1)"
    using ws D unfolding const_wsum_def wsum_def by (simp add: mult.commute)
  from nonint_core[OF ev ev' uv(1,2) uv'(1,2) this] ne show False by blast
qed

corollary nonint_N2:
  assumes "1 \<le> a" "e \<in> tvec a" "e' \<in> tvec a" "e \<noteq> e'" "N2 a e e'"
  shows "Sminus a e mod (int a + 1) \<noteq> Sminus a e' mod (int a + 1)"
proof
  assume "Sminus a e mod (int a + 1) = Sminus a e' mod (int a + 1)"
  then have "(int a + 1) dvd Sminus a e - Sminus a e'" by (simp add: mod_eq_dvd_iff)
  with nonint[OF assms(1-4)] assms(5) show False unfolding N2_def by blast
qed

text \<open>Window sums agreeing up to a constant: pairwise, on a set of templates.\<close>
corollary nonint_class_bound:
  assumes a: "1 \<le> a" and K: "K \<subseteq> tvec a"
    and cls: "\<And>e e'. e \<in> K \<Longrightarrow> e' \<in> K \<Longrightarrow> \<exists>D. const_wsum a e e' D"
  shows "finite K" and "card K \<le> a + 1"
proof -
  let ?f = "\<lambda>e. Sminus a e mod (int a + 1)"
  have inj: "inj_on ?f K"
  proof (rule inj_onI)
    fix e e' assume ee: "e \<in> K" "e' \<in> K" "?f e = ?f e'"
    show "e = e'"
    proof (rule ccontr)
      assume ne: "e \<noteq> e'"
      from cls[OF ee(1,2)] obtain D where D: "const_wsum a e e' D" by blast
      have "wsum a e e' 0 = Sminus a e - Sminus a e'"
        unfolding wsum_def Sminus_def by (simp add: sum_subtractf)
      with D have "D = Sminus a e - Sminus a e'" unfolding const_wsum_def by force
      moreover from ee(3) have "(int a + 1) dvd Sminus a e - Sminus a e'"
        by (simp add: mod_eq_dvd_iff)
      ultimately show False using nonint[OF a _ _ ne D] ee K by blast
    qed
  qed
  have img: "?f ` K \<subseteq> {0..int a}"
  proof (rule image_subsetI)
    fix e
    have pos: "0 < int a + 1" by simp
    have "0 \<le> Sminus a e mod (int a + 1)" by (rule pos_mod_sign[OF pos])
    moreover have "Sminus a e mod (int a + 1) < int a + 1" by (rule pos_mod_bound[OF pos])
    ultimately show "?f e \<in> {0..int a}" unfolding atLeastAtMost_iff by linarith
  qed
  have fin: "finite (?f ` K)" using finite_subset[OF img] by simp
  show "finite K" by (rule finite_imageD[OF fin inj])
  have "card K = card (?f ` K)" using inj by (simp add: card_image)
  also have "\<dots> \<le> card {0..int a}" using img by (intro card_mono) simp_all
  also have "\<dots> = a + 1" by simp
  finally show "card K \<le> a + 1" .
qed

section \<open>Non-vacuity: a = 2\<close>

text \<open>For a = 2 there are two distinct templates with constant window sums (D = -1, and 3 does not divide
  it): (-1,-1,0,0,0) from (u,v) = (5/56, 7/33) and (-1,0,0,0,1) from (u,v) = (8/21, 25/66), as vectors on
  h = -2..2 (the paper counts 6 such pairs for a = 2).\<close>
definition ex_e :: "int \<Rightarrow> int" where "ex_e h = (if h = -2 \<or> h = -1 then -1 else 0)"
definition ex_e' :: "int \<Rightarrow> int" where "ex_e' h = (if h = -2 then -1 else if h = 2 then 1 else 0)"

lemma floor_val: assumes "real_of_int n \<le> x" "x < real_of_int n + 1" shows "floor x = n"
  using assms by (simp add: floor_eq_iff)

lemma ex_e_tvec: "ex_e \<in> tvec 2"
proof -
  have key: "\<forall>h. ex_e h = (if \<bar>h\<bar> \<le> int 2 then floor ((5/56 :: real) + real_of_int h * (7/33)) else 0)"
  proof
    fix h :: int
    show "ex_e h = (if \<bar>h\<bar> \<le> int 2 then floor ((5/56 :: real) + real_of_int h * (7/33)) else 0)"
    proof (cases "\<bar>h\<bar> \<le> 2")
      case True
      then have "h = -2 \<or> h = -1 \<or> h = 0 \<or> h = 1 \<or> h = 2" by (auto simp: abs_le_iff)
      then show ?thesis
      proof (elim disjE)
        assume h: "h = -2"
        have "floor ((5/56 :: real) + real_of_int h * (7/33)) = -1"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e_def)
      next
        assume h: "h = -1"
        have "floor ((5/56 :: real) + real_of_int h * (7/33)) = -1"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e_def)
      next
        assume h: "h = 0"
        have "floor ((5/56 :: real) + real_of_int h * (7/33)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e_def)
      next
        assume h: "h = 1"
        have "floor ((5/56 :: real) + real_of_int h * (7/33)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e_def)
      next
        assume h: "h = 2"
        have "floor ((5/56 :: real) + real_of_int h * (7/33)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e_def)
      qed
    next
      case False
      then show ?thesis by (auto simp: ex_e_def abs_le_iff)
    qed
  qed
  show ?thesis
    unfolding tvec_def
    by (rule CollectI, rule exI[of _ "5/56 :: real"], rule exI[of _ "7/33 :: real"], simp add: key)
qed

lemma ex_e'_tvec: "ex_e' \<in> tvec 2"
proof -
  have key: "\<forall>h. ex_e' h = (if \<bar>h\<bar> \<le> int 2 then floor ((8/21 :: real) + real_of_int h * (25/66)) else 0)"
  proof
    fix h :: int
    show "ex_e' h = (if \<bar>h\<bar> \<le> int 2 then floor ((8/21 :: real) + real_of_int h * (25/66)) else 0)"
    proof (cases "\<bar>h\<bar> \<le> 2")
      case True
      then have "h = -2 \<or> h = -1 \<or> h = 0 \<or> h = 1 \<or> h = 2" by (auto simp: abs_le_iff)
      then show ?thesis
      proof (elim disjE)
        assume h: "h = -2"
        have "floor ((8/21 :: real) + real_of_int h * (25/66)) = -1"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e'_def)
      next
        assume h: "h = -1"
        have "floor ((8/21 :: real) + real_of_int h * (25/66)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e'_def)
      next
        assume h: "h = 0"
        have "floor ((8/21 :: real) + real_of_int h * (25/66)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e'_def)
      next
        assume h: "h = 1"
        have "floor ((8/21 :: real) + real_of_int h * (25/66)) = 0"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e'_def)
      next
        assume h: "h = 2"
        have "floor ((8/21 :: real) + real_of_int h * (25/66)) = 1"
          by (rule floor_val) (simp_all add: h)
        then show ?thesis using h by (simp add: ex_e'_def)
      qed
    next
      case False
      then show ?thesis by (auto simp: ex_e'_def abs_le_iff)
    qed
  qed
  show ?thesis
    unfolding tvec_def
    by (rule CollectI, rule exI[of _ "8/21 :: real"], rule exI[of _ "25/66 :: real"], simp add: key)
qed

lemma ex_const_wsum: "const_wsum 2 ex_e ex_e' (-1)"
  unfolding const_wsum_def wsum_def
proof (intro allI impI)
  fix i :: int assume "0 \<le> i \<and> i \<le> int 2"
  then have "i = 0 \<or> i = 1 \<or> i = 2" by auto
  then show "(\<Sum>h = i - int 2..i. ex_e h - ex_e' h) = -1"
  proof (elim disjE)
    assume "i = 0"
    then have "{i - int 2..i} = {-2, -1, 0}" by auto
    then show ?thesis by (simp add: ex_e_def ex_e'_def)
  next
    assume "i = 1"
    then have "{i - int 2..i} = {-1, 0, 1}" by auto
    then show ?thesis by (simp add: ex_e_def ex_e'_def)
  next
    assume "i = 2"
    then have "{i - int 2..i} = {0, 1, 2}" by auto
    then show ?thesis by (simp add: ex_e_def ex_e'_def)
  qed
qed

lemma example_nonvacuous:
  "ex_e \<in> tvec 2 \<and> ex_e' \<in> tvec 2 \<and> ex_e \<noteq> ex_e' \<and> const_wsum 2 ex_e ex_e' (-1)"
proof -
  have "ex_e \<noteq> ex_e'"
  proof
    assume "ex_e = ex_e'"
    then have "ex_e (-1) = ex_e' (-1)" by simp
    then show False by (simp add: ex_e_def ex_e'_def)
  qed
  with ex_e_tvec ex_e'_tvec ex_const_wsum show ?thesis by blast
qed

end
