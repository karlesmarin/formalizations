(*  Title:      BSR_m4_Pieces.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Algebraic pieces of the paper "Boundary inertia and sums of squares of biquadratic forms" (C. Marín, 2026, in
   preparation), in the representation of BSR44_Pieces: a multiplier on A (x) B, A = R^m, B = R^4, is stored by
   its values on basis tensors, H a b c d = H(e_a (x) e_b, e_c (x) e_d); a tensor h is a function h a b.

   (1) support_triples_m4: the support triples (a,b,r) for 5 <= m <= 16 and the six that survive for every m >= 5.
   (2) regular_point_m4: Lemma "Uniform regular tuples": a Hankel multiplier annihilating the tuple S_m is zero.
   (3) cross_product_identity: [d]x G + G^T [d]x = [((tr G) I - G) d]x.
   (4) isotropic_C4: span{(1,i,0,0),(0,0,1,i)} is a totally isotropic plane of C^4.
   Not formalized: Sylvester inertia, the dimension bound for isotropic subspaces of C^n. *)
theory BSR_m4_Pieces
  imports Complex_Main
begin

section \<open>(1) Support triples\<close>

text \<open>Triples (a,b,r) with 1 <= a <= m, 1 <= b <= 4, max(a,b)+1 <= r <= (a-1)(b-1) and r <= m+1.\<close>

definition triples :: "nat \<Rightarrow> (nat \<times> nat \<times> nat) set" where
  "triples m = {(a,b,r). 1 \<le> a \<and> a \<le> m \<and> 1 \<le> b \<and> b \<le> 4 \<and> a + 1 \<le> r \<and> b + 1 \<le> r \<and> r \<le> (a - 1) * (b - 1) \<and> r \<le> m + 1}"

definition triples_list :: "nat \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "triples_list m = filter (\<lambda>(a,b,r). a + 1 \<le> r \<and> b + 1 \<le> r \<and> r \<le> (a - 1) * (b - 1) \<and> r \<le> m + 1)
      (List.product [1..<m+1] (List.product [1..<5] [0..<m+2]))"

lemma triples_set: "triples m = set (triples_list m)"
  unfolding triples_def triples_list_def by (auto simp: set_upt)

lemma triples_5: "triples 5 = {(3,3,4),(3,4,5),(3,4,6),(4,3,5),(4,3,6),(4,4,5),(4,4,6),(5,3,6),(5,4,6)}"
  unfolding triples_set by eval

lemma triples_6: "triples 6 =
  {(3,3,4),(3,4,5),(3,4,6),(4,3,5),(4,3,6),(4,4,5),(4,4,6),(4,4,7),(5,3,6),(5,3,7),(5,4,6),(5,4,7),(6,3,7),(6,4,7)}"
  unfolding triples_set by eval

text \<open>The cardinalities for m = 5..16 (the lists are the filtered sets above; checked by code evaluation, as in session 239).\<close>
lemma triples_card:
  "card (triples 5) = 9" "card (triples 6) = 14" "card (triples 7) = 21" "card (triples 8) = 29"
  "card (triples 9) = 38" "card (triples 10) = 48" "card (triples 11) = 60" "card (triples 12) = 72"
  "card (triples 13) = 86" "card (triples 14) = 101" "card (triples 15) = 117" "card (triples 16) = 134"
  unfolding triples_set by eval+

text \<open>After excluding a <= m-2 (Lemma "isotropic row") and b <= 2 (Section on small effective supports), only six
  triples remain, for every m >= 5 and by a direct argument.\<close>

theorem support_triples_m4:
  fixes m a b r :: nat
  assumes m: "5 \<le> m" and "(a,b,r) \<in> triples m" and "m \<le> a + 1" and "3 \<le> b"
  shows "(a,b,r) \<in> {(m,4,m+1), (m-1,4,m), (m-1,4,m+1), (m,3,m+1), (m-1,3,m+1), (m-1,3,m)}"
proof -
  have h: "1 \<le> a" "a \<le> m" "b \<le> 4" "a + 1 \<le> r" "b + 1 \<le> r" "r \<le> (a - 1) * (b - 1)" "r \<le> m + 1"
    using assms(2) unfolding triples_def by auto
  have a: "a = m \<or> a = m - 1" using h(2) assms(3) m by arith
  have b: "b = 3 \<or> b = 4" using h(3) assms(4) by arith
  show ?thesis using a b h m
  proof (elim disjE)
    assume "a = m" "b = 3"
    then have "r \<le> 2 * (m - 1)" "r \<ge> m + 1" "r \<le> m + 1" using h by auto
    then show ?thesis using \<open>a = m\<close> \<open>b = 3\<close> by auto
  next
    assume "a = m" "b = 4"
    then show ?thesis using h m by auto
  next
    assume "a = m - 1" "b = 3"
    then show ?thesis using h m by auto
  next
    assume "a = m - 1" "b = 4"
    then show ?thesis using h m by auto
  qed
qed

section \<open>(2) Uniform regular tuples\<close>

text \<open>Basis tensors, the pairing of a tensor with the multiplier, and the annihilation condition.
  \<open>av M H h c d\<close> is the value H(h, e_c (x) e_d) on M rows.\<close>

definition ev :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "ev i j a b = (if a = i \<and> b = j then 1 else 0)"

definition av :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "av M H h c d = (\<Sum>a<M. \<Sum>b<4. h a b * H a b c d)"

lemma sum4: "(\<Sum>b<(4::nat). f b) = f 0 + f 1 + f 2 + f 3"
  by (simp add: eval_nat_numeral lessThan_Suc add_ac)

lemma sum_unit:
  fixes f :: "nat \<Rightarrow> real"
  assumes "i < M"
  shows "(\<Sum>a<M. (if a = i then 1 else 0) * f a) = f i"
proof -
  have "(\<Sum>a<M. (if a = i then 1 else 0) * f a) = (\<Sum>a<M. if a = i then f a else 0)"
    by (intro sum.cong) auto
  also have "\<dots> = f i" using assms by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma av_add: "av M H (\<lambda>a b. f a b + g a b) c d = av M H f c d + av M H g c d"
  unfolding av_def by (simp add: algebra_simps sum.distrib)

lemma av_ev:
  assumes "i < M" "j < 4"
  shows "av M H (ev i j) c d = H i j c d"
proof -
  have "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" using assms(2) by auto
  then show ?thesis using assms(1)
    by (elim disjE) (simp_all add: av_def ev_def sum4 sum_unit)
qed

lemma av_restrict:
  assumes "\<And>b. h m b = 0"
  shows "av (Suc m) H h c d = av m H h c d"
  unfolding av_def using assms by simp

text \<open>Copy of BSR44_Pieces.regular_point_symmetric (public repository), n x n block.\<close>

lemma regular_point_symmetric:
  fixes H :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" and n :: nat
  assumes sym: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d = H c d a b"
    and hankel: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d = H a d c b"
    and van: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d + H b a c d = 0"
    and idx: "a < n" "b < n" "c < n" "d < n"
  shows "H a b c d = 0"
proof -
  have anti2: "H p q r s = - H p q s r" if "p < n" "q < n" "r < n" "s < n" for p q r s
  proof -
    have "H p q r s = H r s p q" using sym that by blast
    also have "\<dots> = - H s r p q" using van[of r s p q] that by linarith
    also have "H s r p q = H p q s r" using sym that by blast
    finally show ?thesis .
  qed
  have "H a b c d = H a d c b" using hankel idx by blast
  also have "\<dots> = - H a d b c" using anti2 idx by blast
  also have "H a d b c = H a c b d" using hankel idx by blast
  also have "H a c b d = - H a c d b" using anti2 idx by blast
  also have "H a c d b = H a b d c" using hankel idx by blast
  also have "H a b d c = - H a b c d" using anti2 idx by blast
  finally show ?thesis by simp
qed

text \<open>The tuple. Base S_5: x_i y_i, x_i y_j + x_j y_i (i < j <= 3), x_4 y_j, with h*_5 = x_0 y_0. Rows 5+n:
  S_{m+1} = (S_m - {h*_m}) + {h*_m + z y_3, z y_0, z y_1, z y_2}, h*_{m+1} = z y_0, z = x_m.
  Index n stands for m = 5 + n.\<close>

definition base5 :: "(nat \<Rightarrow> nat \<Rightarrow> real) set" where
  "base5 = {ev i i | i. i \<le> 3} \<union> {(\<lambda>a b. ev i j a b + ev j i a b) | i j. i < j \<and> j \<le> 3} \<union> {ev 4 j | j. j \<le> 3}"

lemma base5_diag: "i \<le> 3 \<Longrightarrow> ev i i \<in> base5" unfolding base5_def by blast
lemma base5_sym: "i < j \<Longrightarrow> j \<le> 3 \<Longrightarrow> (\<lambda>a b. ev i j a b + ev j i a b) \<in> base5" unfolding base5_def by blast
lemma base5_row: "j \<le> 3 \<Longrightarrow> ev 4 j \<in> base5" unfolding base5_def by blast

primrec hstar :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)" where
  "hstar 0 = ev 0 0"
| "hstar (Suc n) = ev (5 + n) 0"

primrec S :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) set" where
  "S 0 = base5"
| "S (Suc n) = (S n - {hstar n}) \<union>
      {(\<lambda>a b. hstar n a b + ev (5 + n) 3 a b), ev (5 + n) 0, ev (5 + n) 1, ev (5 + n) 2}"

text \<open>The two invariants of the proof: h*_m has zero y_3 coefficient, and the y_3 coefficients span all old rows
  (here: each row r < m is the y_3 column of one element), plus support in the rows < m.\<close>

lemma invariants:
  "hstar n \<in> S n \<and> (\<forall>h \<in> S n. \<forall>a \<ge> 5 + n. \<forall>b. h a b = 0) \<and> (\<forall>a. hstar n a 3 = 0)
   \<and> (\<forall>r < 5 + n. \<exists>h \<in> S n. \<forall>a. h a 3 = (if a = r then 1 else 0))"
proof (induction n)
  case 0
  have h0: "hstar 0 \<in> S 0" using base5_diag[of 0] by simp
  have h1: "\<forall>h \<in> S 0. \<forall>a \<ge> 5 + 0. \<forall>b. h a b = 0"
  proof (intro ballI allI impI)
    fix h :: "nat \<Rightarrow> nat \<Rightarrow> real" and a b :: nat assume "h \<in> S 0" "a \<ge> 5 + 0"
    then have h: "(\<exists>i. i \<le> 3 \<and> h = ev i i) \<or> (\<exists>i j. i < j \<and> j \<le> 3 \<and> h = (\<lambda>a b. ev i j a b + ev j i a b))
        \<or> (\<exists>j. j \<le> 3 \<and> h = ev 4 j)" unfolding S.simps base5_def mem_Collect_eq Un_iff by blast
    show "h a b = 0" using h \<open>a \<ge> 5 + 0\<close> by (auto simp: ev_def)
  qed
  have h2: "\<forall>a. hstar 0 a 3 = 0" by (simp add: ev_def)
  have h3: "\<forall>r < 5 + 0. \<exists>h \<in> S 0. \<forall>a. h a 3 = (if a = r then 1 else 0)"
  proof (intro allI impI)
    fix r :: nat assume "r < 5 + 0"
    then have "r < 3 \<or> r = 3 \<or> r = 4" by auto
    then show "\<exists>h \<in> S 0. \<forall>a. h a 3 = (if a = r then 1 else 0)"
    proof (elim disjE)
      assume r: "r < 3"
      have "(\<lambda>a b. ev r 3 a b + ev 3 r a b) \<in> S 0" using base5_sym[of r 3] r by simp
      then have memr: "(\<lambda>a b. ev r 3 a b + ev 3 r a b) \<in> S 0" .
      show ?thesis
        by (rule bexI[of _ "\<lambda>a b. ev r 3 a b + ev 3 r a b"]) (use r memr in \<open>simp_all add: ev_def\<close>)
    next
      assume "r = 3"
      then show ?thesis using base5_diag[of 3] by (auto intro!: bexI[of _ "ev 3 3"] simp: ev_def)
    next
      assume "r = 4"
      then show ?thesis using base5_row[of 3] by (auto intro!: bexI[of _ "ev 4 3"] simp: ev_def)
    qed
  qed
  from h0 h1 h2 h3 show ?case by blast
next
  case (Suc n)
  then obtain i0 i1 i2 i3 where i0: "hstar n \<in> S n" and i1: "\<forall>h \<in> S n. \<forall>a \<ge> 5 + n. \<forall>b. h a b = 0"
    and i2: "\<forall>a. hstar n a 3 = 0" and i3: "\<forall>r < 5 + n. \<exists>h \<in> S n. \<forall>a. h a 3 = (if a = r then 1 else 0)"
    by blast
  have n0: "(\<lambda>a b. hstar n a b + ev (5 + n) 3 a b) \<in> S (Suc n)" by simp
  have n1: "ev (5 + n) 0 \<in> S (Suc n)" by simp
  have c1: "\<forall>h \<in> S (Suc n). \<forall>a \<ge> 5 + Suc n. \<forall>b. h a b = 0"
  proof (intro ballI allI impI)
    fix h a b assume h: "h \<in> S (Suc n)" and a: "a \<ge> 5 + Suc n"
    from h have "h \<in> S n \<or> h = (\<lambda>a b. hstar n a b + ev (5 + n) 3 a b) \<or> h = ev (5 + n) 0 \<or> h = ev (5 + n) 1 \<or> h = ev (5 + n) 2"
      by auto
    then show "h a b = 0"
    proof (elim disjE)
      assume "h \<in> S n" then show ?thesis using i1 a by simp
    next
      assume "h = (\<lambda>a b. hstar n a b + ev (5 + n) 3 a b)"
      then show ?thesis using i1 i0 a by (simp add: ev_def)
    qed (use a in \<open>simp_all add: ev_def\<close>)
  qed
  have c3: "\<forall>r < 5 + Suc n. \<exists>h \<in> S (Suc n). \<forall>a. h a 3 = (if a = r then 1 else 0)"
  proof (intro allI impI)
    fix r assume r: "r < 5 + Suc n"
    show "\<exists>h \<in> S (Suc n). \<forall>a. h a 3 = (if a = r then 1 else 0)"
    proof (cases "r < 5 + n")
      case True
      then obtain h where h: "h \<in> S n" "\<forall>a. h a 3 = (if a = r then 1 else 0)" using i3 by blast
      have "h \<noteq> hstar n" using h(2)[THEN spec, of r] i2 by auto
      then have "h \<in> S (Suc n)" using h(1) by simp
      then show ?thesis using h(2) by blast
    next
      case False
      then have "r = 5 + n" using r by simp
      then show ?thesis using n0 i2 by (auto intro!: exI[of _ "\<lambda>a b. hstar n a b + ev (5 + n) 3 a b"] simp: ev_def)
    qed
  qed
  have c0: "hstar (Suc n) \<in> S (Suc n)" using n1 by simp
  have c2: "\<forall>a. hstar (Suc n) a 3 = 0" by (simp add: ev_def)
  show ?case using c0 c1 c2 c3 by blast
qed

text \<open>The inductive step, abstracted over the old tuple T with its distinguished element hs.\<close>

lemma regular_step:
  fixes H :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" and m :: nat and T :: "(nat \<Rightarrow> nat \<Rightarrow> real) set" and hs
  assumes sym: "\<And>a b c d. a < Suc m \<Longrightarrow> b < 4 \<Longrightarrow> c < Suc m \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H c d a b"
    and hankel: "\<And>a b c d. a < Suc m \<Longrightarrow> b < 4 \<Longrightarrow> c < Suc m \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H a d c b"
    and supp: "\<forall>h \<in> T. \<forall>a \<ge> m. \<forall>b. h a b = 0" and hsT: "hs \<in> T" and hs3: "\<forall>a. hs a 3 = 0"
    and span: "\<forall>r < m. \<exists>h \<in> T. \<forall>a. h a 3 = (if a = r then 1 else 0)"
    and ann: "\<forall>h \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}.
                \<forall>c < Suc m. \<forall>d < 4. av (Suc m) H h c d = 0"
    and IH: "(\<forall>h \<in> T. \<forall>c < m. \<forall>d < 4. av m H h c d = 0) \<Longrightarrow> (\<forall>a < m. \<forall>b < 4. \<forall>c < m. \<forall>d < 4. H a b c d = 0)"
  shows "\<forall>a < Suc m. \<forall>b < 4. \<forall>c < Suc m. \<forall>d < 4. H a b c d = 0"
proof -
  have z: "H m j c d = 0" if "j < 3" "c < Suc m" "d < 4" for j c d
  proof -
    have "j = 0 \<or> j = 1 \<or> j = 2" using that(1) by arith
    then have "ev m j \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}"
      by (elim disjE) auto
    from ann[rule_format, OF this that(2) that(3)] av_ev[of m "Suc m" j H c d] that show ?thesis by simp
  qed
  have b3: "H a b m 3 = 0" if "a < Suc m" "b < 3" for a b
  proof -
    have "H a b m 3 = H a 3 m b" using hankel[of a b m 3] that by simp
    also have "\<dots> = H m b a 3" using sym[of a 3 m b] that by simp
    also have "\<dots> = 0" using z that by simp
    finally show ?thesis .
  qed
  have k: "H r 3 m 3 = 0" if rm: "r < m" for r
  proof -
    obtain h where h: "h \<in> T" "\<forall>a. h a 3 = (if a = r then 1 else 0)" using span[rule_format, OF rm] by blast
    have "h \<noteq> hs" using h(2)[THEN spec, of r] hs3 by auto
    then have hm: "h \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}" using h by auto
    have "av (Suc m) H h m 3 = (\<Sum>a<Suc m. if a = r then H a 3 m 3 else 0)"
      unfolding av_def
    proof (intro sum.cong refl)
      fix a assume a: "a \<in> {..<Suc m}"
      have "(\<Sum>b<4. h a b * H a b m 3) = h a 3 * H a 3 m 3" using a b3 by (simp add: sum4)
      then show "(\<Sum>b<4. h a b * H a b m 3) = (if a = r then H a 3 m 3 else 0)" using h(2) by simp
    qed
    also have "\<dots> = H r 3 m 3" using rm by (simp add: sum.delta)
    finally have "av (Suc m) H h m 3 = H r 3 m 3" .
    moreover have "av (Suc m) H h m 3 = 0" using ann hm by auto
    ultimately show ?thesis by simp
  qed
  have R3c: "H m 3 c d = 0" if "c < m" "d < 4" for c d
  proof (cases "d < 3")
    case True
    have "H m 3 c d = H m d c 3" using hankel[of m 3 c d] that by simp
    also have "\<dots> = 0" using z True that by simp
    finally show ?thesis .
  next
    case False
    then have "d = 3" using that by simp
    have "H m 3 c 3 = H c 3 m 3" using sym[of m 3 c 3] that by simp
    then show ?thesis using k that \<open>d = 3\<close> by simp
  qed
  have gam: "H m 3 m 3 = 0"
  proof -
    have mem: "(\<lambda>a b. hs a b + ev m 3 a b) \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}" by simp
    have "av (Suc m) H (\<lambda>a b. hs a b + ev m 3 a b) m 3 = 0" using ann mem by auto
    moreover have "av (Suc m) H (\<lambda>a b. hs a b + ev m 3 a b) m 3 = av (Suc m) H hs m 3 + H m 3 m 3"
      by (simp add: av_add av_ev)
    moreover have "av (Suc m) H hs m 3 = 0"
    proof -
      have "\<forall>a < Suc m. (\<Sum>b<4. hs a b * H a b m 3) = 0" using b3 hs3 by (simp add: sum4)
      then show ?thesis unfolding av_def by simp
    qed
    ultimately show ?thesis by simp
  qed
  have Rm: "H m b c d = 0" if "b < 4" "c < Suc m" "d < 4" for b c d
  proof (cases "b < 3")
    case True then show ?thesis using z that by simp
  next
    case False
    then have b: "b = 3" using that by simp
    show ?thesis
    proof (cases "c < m")
      case True then show ?thesis using R3c that b by simp
    next
      case False
      then have c: "c = m" using that by simp
      show ?thesis
      proof (cases "d < 3")
        case True
        have "H m 3 m d = H m d m 3" using hankel[of m 3 m d] that by simp
        then show ?thesis using z True c b by simp
      next
        case False
        then have "d = 3" using that by simp
        then show ?thesis using gam b c by simp
      qed
    qed
  qed
  have old: "\<forall>h \<in> T. \<forall>c < m. \<forall>d < 4. av m H h c d = 0"
  proof (intro ballI allI impI)
    fix h :: "nat \<Rightarrow> nat \<Rightarrow> real" and c d :: nat assume h: "h \<in> T" and c: "c < m" and d: "d < 4"
    show "av m H h c d = 0"
    proof (cases "h = hs")
      case True
      have mem: "(\<lambda>a b. hs a b + ev m 3 a b) \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}" by simp
      have "av (Suc m) H (\<lambda>a b. hs a b + ev m 3 a b) c d = 0" using ann mem c d by auto
      then have "av (Suc m) H hs c d + H m 3 c d = 0" by (simp add: av_add av_ev)
      then have "av (Suc m) H hs c d = 0" using R3c c d by simp
      moreover have "av (Suc m) H hs c d = av m H hs c d" using av_restrict[of hs m H c d] supp hsT by blast
      ultimately show ?thesis using True by simp
    next
      case False
      then have "h \<in> (T - {hs}) \<union> {(\<lambda>a b. hs a b + ev m 3 a b), ev m 0, ev m 1, ev m 2}" using h by auto
      then have "av (Suc m) H h c d = 0" using ann c d by auto
      moreover have "av (Suc m) H h c d = av m H h c d" using av_restrict[of h m H c d] supp h by blast
      ultimately show ?thesis by simp
    qed
  qed
  have z_old: "\<forall>a < m. \<forall>b < 4. \<forall>c < m. \<forall>d < 4. H a b c d = 0" using IH old by blast
  show ?thesis
  proof (intro allI impI)
    fix a b c d :: nat assume a: "a < Suc m" and b: "b < 4" and c: "c < Suc m" and d: "d < 4"
    show "H a b c d = 0"
    proof (cases "a < m")
      case True
      show ?thesis
      proof (cases "c < m")
        case True with \<open>a < m\<close> z_old b d show ?thesis by blast
      next
        case False
        then have "H a b c d = H c d a b" using sym a b c d by simp
        moreover have "c = m" using False c by simp
        ultimately show ?thesis using Rm[of d a b] a b d by simp
      qed
    next
      case False
      then have "a = m" using a by simp
      then show ?thesis using Rm b c d by simp
    qed
  qed
qed

text \<open>Lemma ``Uniform regular tuples'': a symmetric Hankel multiplier on m x 4 (m = 5 + n) annihilating S_m is zero.\<close>

theorem regular_point_m4:
  fixes H :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" and n :: nat
  assumes sym: "\<And>a b c d. a < 5 + n \<Longrightarrow> b < 4 \<Longrightarrow> c < 5 + n \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H c d a b"
    and hankel: "\<And>a b c d. a < 5 + n \<Longrightarrow> b < 4 \<Longrightarrow> c < 5 + n \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H a d c b"
    and ann: "\<forall>h \<in> S n. \<forall>c < 5 + n. \<forall>d < 4. av (5 + n) H h c d = 0"
  shows "\<forall>a < 5 + n. \<forall>b < 4. \<forall>c < 5 + n. \<forall>d < 4. H a b c d = 0"
  using sym hankel ann
proof (induction n)
  case 0
  note sym = "0.prems"(1) and hankel = "0.prems"(2) and ann = "0.prems"(3)
  have e1: "H 4 j c d = 0" if "j < 4" "c < 5" "d < 4" for j c d
  proof -
    have "ev 4 j \<in> S 0" using base5_row[of j] that by simp
    from ann[rule_format, OF this] that show ?thesis by (simp add: av_ev)
  qed
  have e2: "H i i c d = 0" if "i < 4" "c < 5" "d < 4" for i c d
  proof -
    have "ev i i \<in> S 0" using base5_diag[of i] that by simp
    from ann[rule_format, OF this] that show ?thesis by (simp add: av_ev)
  qed
  have e3: "H i j c d + H j i c d = 0" if "i < j" "j < 4" "c < 5" "d < 4" for i j c d
  proof -
    have "(\<lambda>a b. ev i j a b + ev j i a b) \<in> S 0" using base5_sym[of i j] that by simp
    from ann[rule_format, OF this] that show ?thesis by (simp add: av_add av_ev)
  qed
  have van: "H a b c d + H b a c d = 0" if "a < 4" "b < 4" "c < 5" "d < 4" for a b c d
  proof (cases a b rule: linorder_cases)
    case less then show ?thesis using e3 that by blast
  next
    case equal then show ?thesis using e2 that by simp
  next
    case greater then show ?thesis using e3[of b a c d] that by simp
  qed
  have blk: "H a b c d = 0" if "a < 4" "b < 4" "c < 4" "d < 4" for a b c d
    using regular_point_symmetric[of 4 H a b c d] sym hankel van that by simp
  show ?case
  proof (intro allI impI)
    fix a b c d :: nat assume "a < 5 + 0" "b < 4" "c < 5 + 0" "d < 4"
    then have a: "a < 5" and c: "c < 5" and b: "b < 4" and d: "d < 4" by simp_all
    show "H a b c d = 0"
    proof (cases "a < 4")
      case True
      show ?thesis
      proof (cases "c < 4")
        case True with \<open>a < 4\<close> blk b d show ?thesis by blast
      next
        case False
        then have "c = 4" using c by simp
        have "H a b c d = H c d a b" using sym a b c d by simp
        then show ?thesis using e1 \<open>c = 4\<close> \<open>a < 4\<close> b d by simp
      qed
    next
      case False
      then have "a = 4" using a by simp
      then show ?thesis using e1 b c d by simp
    qed
  qed
next
  case (Suc n)
  note inv = invariants[of n]
  have M: "5 + Suc n = Suc (5 + n)" by simp
  have step: "\<forall>a < Suc (5 + n). \<forall>b < 4. \<forall>c < Suc (5 + n). \<forall>d < 4. H a b c d = 0"
  proof (rule regular_step[where T = "S n" and hs = "hstar n"])
    show "\<And>a b c d. a < Suc (5 + n) \<Longrightarrow> b < 4 \<Longrightarrow> c < Suc (5 + n) \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H c d a b"
      using Suc.prems(1) M by simp
    show "\<And>a b c d. a < Suc (5 + n) \<Longrightarrow> b < 4 \<Longrightarrow> c < Suc (5 + n) \<Longrightarrow> d < 4 \<Longrightarrow> H a b c d = H a d c b"
      using Suc.prems(2) M by simp
    show "\<forall>h \<in> S n. \<forall>a \<ge> 5 + n. \<forall>b. h a b = 0" using inv by blast
    show "hstar n \<in> S n" using inv by blast
    show "\<forall>a. hstar n a 3 = 0" using inv by blast
    show "\<forall>r < 5 + n. \<exists>h \<in> S n. \<forall>a. h a 3 = (if a = r then 1 else 0)" using inv by blast
    show "\<forall>h \<in> (S n - {hstar n}) \<union> {(\<lambda>a b. hstar n a b + ev (5 + n) 3 a b), ev (5 + n) 0, ev (5 + n) 1, ev (5 + n) 2}.
            \<forall>c < Suc (5 + n). \<forall>d < 4. av (Suc (5 + n)) H h c d = 0"
      using Suc.prems(3) M by simp
    show "(\<forall>h \<in> S n. \<forall>c < 5 + n. \<forall>d < 4. av (5 + n) H h c d = 0) \<Longrightarrow> \<forall>a < 5 + n. \<forall>b < 4. \<forall>c < 5 + n. \<forall>d < 4. H a b c d = 0"
    proof -
      assume ann': "\<forall>h \<in> S n. \<forall>c < 5 + n. \<forall>d < 4. av (5 + n) H h c d = 0"
      have "\<forall>a < 5 + n. \<forall>b < 4. \<forall>c < 5 + n. \<forall>d < 4. H a b c d = 0"
        by (rule Suc.IH) (use Suc.prems(1,2) ann' in \<open>auto\<close>)
      then show ?thesis .
    qed
  qed
  show ?case using step M by simp
qed

section \<open>(3) The cross-product identity\<close>

text \<open>[d]x v = d x v. Matrices are functions on index pairs 0,1,2; the sum over k < 3 is the matrix product.\<close>

definition crossm :: "(nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "crossm d i j = (if i = 0 \<and> j = 1 then - d 2 else if i = 0 \<and> j = 2 then d 1
     else if i = 1 \<and> j = 0 then d 2 else if i = 1 \<and> j = 2 then - d 0
     else if i = 2 \<and> j = 0 then - d 1 else if i = 2 \<and> j = 1 then d 0 else 0)"

definition trace3 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> 'a" where
  "trace3 G = G 0 0 + G 1 1 + G 2 2"

text \<open>The vector ((tr G) I - G) d.\<close>
definition trmul :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "trmul G d i = trace3 G * d i - (G i 0 * d 0 + G i 1 * d 1 + G i 2 * d 2)"

lemma sum3: "(\<Sum>k<(3::nat). f k) = f 0 + f 1 + f 2"
  by (simp add: eval_nat_numeral lessThan_Suc add_ac)

theorem cross_product_identity:
  fixes G :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring" and d :: "nat \<Rightarrow> 'a"
  assumes "i < 3" "j < 3"
  shows "(\<Sum>k<3. crossm d i k * G k j) + (\<Sum>k<3. G k i * crossm d k j) = crossm (trmul G d) i j"
proof -
  have "i = 0 \<or> i = 1 \<or> i = 2" "j = 0 \<or> j = 1 \<or> j = 2" using assms by auto
  then show ?thesis
    by (elim disjE) (simp_all add: sum3 crossm_def trmul_def trace3_def algebra_simps)
qed

text \<open>The statement holds for the real and the complex field alike (both are comm_ring instances).\<close>
corollary cross_product_identity_real:
  fixes G :: "nat \<Rightarrow> nat \<Rightarrow> real" and d :: "nat \<Rightarrow> real"
  assumes "i < 3" "j < 3"
  shows "(\<Sum>k<3. crossm d i k * G k j) + (\<Sum>k<3. G k i * crossm d k j) = crossm (trmul G d) i j"
  by (rule cross_product_identity[OF assms])

corollary cross_product_identity_complex:
  fixes G :: "nat \<Rightarrow> nat \<Rightarrow> complex" and d :: "nat \<Rightarrow> complex"
  assumes "i < 3" "j < 3"
  shows "(\<Sum>k<3. crossm d i k * G k j) + (\<Sum>k<3. G k i * crossm d k j) = crossm (trmul G d) i j"
  by (rule cross_product_identity[OF assms])

section \<open>(4) A totally isotropic plane of C^4\<close>

text \<open>Standard symmetric bilinear form on C^4 (no conjugation).\<close>
definition bf4 :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex" where
  "bf4 u v = (\<Sum>k<4. u k * v k)"

definition v1 :: "nat \<Rightarrow> complex" where "v1 k = (if k = 0 then 1 else if k = 1 then \<i> else 0)"
definition v2 :: "nat \<Rightarrow> complex" where "v2 k = (if k = 2 then 1 else if k = 3 then \<i> else 0)"

lemma isotropic_C4:
  "bf4 (\<lambda>k. s * v1 k + t * v2 k) (\<lambda>k. u * v1 k + w * v2 k) = 0"
  by (simp add: bf4_def sum4 v1_def v2_def algebra_simps)

lemma isotropic_C4_independent:
  assumes "\<forall>k. s * v1 k + t * v2 k = 0"
  shows "s = 0 \<and> t = 0"
proof -
  have "s * v1 0 + t * v2 0 = 0" "s * v1 2 + t * v2 2 = 0" using assms by blast+
  then show ?thesis by (simp add: v1_def v2_def)
qed

end
