(*  Title:      Caballero_Families.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation): Theorem F (the five families
   F_1, ..., F_5 for a = 3, "next to the upper clipping"), on top of Caballero_Twonum / Caballero_Setting.

   For every family and every admissible (b, i, eps) the two vectors P and Q are
     - realisable (vectors of points of the open quadrant with no Lambda + h theta an integer, |h| <= 3: the
       affine witnesses of Table "witF"),
     - distinct, and
     - have the same Z: an involution phi of the grid {0..3} x {0..b} with H_Q(phi p) = H_P(p) (swaps of
       blocks of points between two rows), so that Z(P) = Z(Q) as multisets.
*)
theory Caballero_Families
  imports Caballero_Twonum
begin

section \<open>Realisability through an affine witness\<close>

definition realis :: "int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool" where
  "realis b c \<longleftrightarrow> (\<exists>Lam th :: real. 0 < Lam \<and> 0 < th \<and>
     (\<forall>h. -3 \<le> h \<and> h \<le> 3 \<longrightarrow> Lam + real_of_int h * th \<notin> \<int> \<and> c h = cpt b Lam th h))"

text \<open>Witness (Lambda, theta) = (nn/q, tt/q); then Lambda + h theta = (nn + h tt)/q, whose floor is the integer
  quotient and which is an integer iff q divides the numerator.\<close>
lemma realis_rat:
  assumes q: "0 < q" and nn: "0 < nn" and tt: "0 < tt"
    and fr: "\<And>h. h \<in> {-3, -2, -1, 0, 1, 2, 3} \<Longrightarrow> \<not> q dvd (nn + h * tt)"
    and cv: "\<And>h. h \<in> {-3, -2, -1, 0, 1, 2, 3} \<Longrightarrow> c h = clipb b ((nn + h * tt) div q)"
  shows "realis b c"
proof -
  have qr0: "0 < real_of_int q" using q by simp
  have p1: "0 < real_of_int nn / real_of_int q" using nn qr0 by simp
  have p2: "0 < real_of_int tt / real_of_int q" using tt qr0 by simp
  have p3: "\<And>h. -3 \<le> h \<and> h \<le> 3 \<Longrightarrow>
      real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q) \<notin> \<int>
      \<and> c h = cpt b (real_of_int nn / real_of_int q) (real_of_int tt / real_of_int q) h"
  proof -
  fix h :: int assume h: "-3 \<le> h \<and> h \<le> 3"
  have qr: "real_of_int q \<noteq> 0" using q by simp
  have hm: "h \<in> {-3, -2, -1, 0, 1, 2, 3}" using h by (simp; arith)
  have eq: "real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q)
          = real_of_int (nn + h * tt) / real_of_int q"
    using qr by (simp add: field_simps)
  show "real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q) \<notin> \<int>
        \<and> c h = cpt b (real_of_int nn / real_of_int q) (real_of_int tt / real_of_int q) h"
  proof (rule conjI)
    show "real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q) \<notin> \<int>"
    proof
      assume "real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q) \<in> \<int>"
      then obtain m where "real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q) = real_of_int m"
        unfolding Ints_def by auto
      then have "real_of_int (nn + h * tt) / real_of_int q = real_of_int m" using eq by simp
      then have "real_of_int (nn + h * tt) = real_of_int m * real_of_int q"
        by (simp only: nonzero_divide_eq_eq[OF qr])
      then have "nn + h * tt = m * q" by (metis of_int_eq_iff of_int_mult)
      then have "q dvd nn + h * tt" by simp
      then show False using fr[OF hm] by simp
    qed
    have fl: "\<lfloor>real_of_int nn / real_of_int q + real_of_int h * (real_of_int tt / real_of_int q)\<rfloor>
              = (nn + h * tt) div q"
    proof -
      have "\<lfloor>real_of_int (nn + h * tt) / real_of_int q\<rfloor> = (nn + h * tt) div q"
        by (rule floor_divide_of_int_eq)
      then show ?thesis by (simp only: eq)
    qed
    show "c h = cpt b (real_of_int nn / real_of_int q) (real_of_int tt / real_of_int q) h"
      unfolding cpt_def using fl cv[OF hm] by simp
  qed
  qed
  show ?thesis unfolding realis_def
    by (rule exI[of _ "real_of_int nn / real_of_int q"], rule exI[of _ "real_of_int tt / real_of_int q"])
       (use p1 p2 p3 in blast)
qed

section \<open>A permutation of the grid gives equal Z\<close>

lemma Zms_perm:
  fixes phi :: "int \<times> int \<Rightarrow> int \<times> int"
  assumes mem: "\<And>p. p \<in> {0..3} \<times> {0..b} \<Longrightarrow> phi p \<in> {0..3} \<times> {0..b}"
    and inv: "\<And>p. p \<in> {0..3} \<times> {0..b} \<Longrightarrow> phi (phi p) = p"
    and HH: "\<And>p. p \<in> {0..3} \<times> {0..b} \<Longrightarrow> Hval 3 b Q (fst (phi p)) (snd (phi p)) = Hval 3 b P (fst p) (snd p)"
  shows "Zms 3 b P = Zms 3 b Q"
proof -
  let ?S = "{0..3} \<times> {0..b}"
  have bij: "bij_betw phi ?S ?S"
  proof (rule bij_betw_byWitness[where f' = phi])
    show "\<forall>a\<in>?S. phi (phi a) = a" using inv by blast
    show "\<forall>a\<in>?S. phi (phi a) = a" using inv by blast
    show "phi ` ?S \<subseteq> ?S" using mem by blast
    show "phi ` ?S \<subseteq> ?S" using mem by blast
  qed
  let ?g = "\<lambda>p::int \<times> int. Hval 3 b Q (fst p) (snd p)"
  have "Zms 3 b P = image_mset (\<lambda>p. Hval 3 b P (fst p) (snd p)) (mset_set ?S)" by (simp add: Zms_def)
  also have "\<dots> = image_mset (\<lambda>p. ?g (phi p)) (mset_set ?S)"
    by (rule image_mset_cong) (use HH in auto)
  also have "\<dots> = image_mset ?g (image_mset phi (mset_set ?S))" by (simp add: image_mset.compositionality o_def)
  also have "\<dots> = image_mset ?g (mset_set (phi ` ?S))"
    using image_mset_mset_set[OF bij_betw_imp_inj_on[OF bij]] by simp
  also have "phi ` ?S = ?S" using bij by (simp add: bij_betw_def)
  also have "image_mset ?g (mset_set ?S) = Zms 3 b Q" by (simp add: Zms_def)
  finally show ?thesis .
qed

lemma Hval3:
  "Hval 3 b c r j = fcl b (c r + j) + fcl b (c (r - 1) + j) + fcl b (c (r - 2) + j) + fcl b (c (r - 3) + j)"
proof -
  have "{0..3::int} = {0, 1, 2, 3}" by auto
  then show ?thesis by (simp add: Hval_def algebra_simps)
qed

lemma fcl_alt: "0 \<le> b \<Longrightarrow> fcl b v = (if v \<le> -1 then 0 else if b \<le> v then b + 1 else v + 1)"
  unfolding fcl_def by (auto simp: min_def max_def)

section \<open>F1\<close>

text \<open>Paper II, Theorem~\ref{thm:F}, line F1: P=(x,y,z,B^4), Q=(x+1,y,z-1,B^4); x=b-3-3i, y=b-2-2i+eps, z=b-i; x>=-1.  vF1 b i e s is P for s = 0 and Q for s = 1.\<close>

definition vF1 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "vF1 b i e s h = (if h = -3 then b - 3 - 3 * i + s else if h = -2 then b - 2 - 2 * i + e else if h = -1 then b - i - s else b)"

definition phiF1 :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "phiF1 i p = (case p of (r, j) \<Rightarrow>
     if r = 0 \<and> i + 1 \<le> j \<and> j \<le> i + 1 + i + 1 - 1 then (1, j - (i + 1) + 0)
     else if r = 1 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + i + 1)
     else if r = 0 \<and> 2 * i + 2 \<le> j \<and> j \<le> 2 * i + 2 + i + 1 - 1 then (2, j - (2 * i + 2) + 0)
     else if r = 2 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + 2 * i + 2)
     else (r, j))"

lemma F1_H:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 3 - 3 * i" and e0: "0 \<le> e" and e1: "e \<le> 1" and r: "0 \<le> r" "r \<le> 3" and j: "0 \<le> j" "j \<le> b"
  shows "Hval 3 b (vF1 b i e 1) (fst (phiF1 i (r, j))) (snd (phiF1 i (r, j))) = Hval 3 b (vF1 b i e 0) r j"

proof -
  have b0: "0 \<le> b" using i x e0 e1 by arith
  consider (c0) "r = 0" | (c1) "r = 1" | (c2) "r = 2" | (c3) "r = 3" using r by arith
  then show ?thesis
  proof cases
    case c0
    show ?thesis
      using i x e0 e1 j
      by (simp add: c0 phiF1_def Hval3 vF1_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c1
    show ?thesis
      using i x e0 e1 j
      by (simp add: c1 phiF1_def Hval3 vF1_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c2
    show ?thesis
      using i x e0 e1 j
      by (simp add: c2 phiF1_def Hval3 vF1_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c3
    show ?thesis
      using i x e0 e1 j
      by (simp add: c3 phiF1_def Hval3 vF1_def fcl_alt[OF b0] split: if_splits; arith?)
  qed
qed

lemma F1_mem:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 3 - 3 * i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF1 i p \<in> {0..3} \<times> {0..b}"
  using p i x by (cases p) (auto simp: phiF1_def split: if_splits; arith?)

lemma F1_inv:
  assumes i: "0 \<le> i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF1 i (phiF1 i p) = p"
  using p i by (cases p) (auto simp: phiF1_def split: if_splits; arith?)

theorem thm_F1:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 3 - 3 * i" and e: "e = 0 \<or> e = 1"
  shows "realis b (vF1 b i e 0)" "realis b (vF1 b i e 1)" "vF1 b i e 0 (-3) \<noteq> vF1 b i e 1 (-3)"
    "Zms 3 b (vF1 b i e 0) = Zms 3 b (vF1 b i e 1)"
proof -
  have e0: "0 \<le> e" and e1: "e \<le> 1" using e by auto
  show "realis b (vF1 b i e 0)"
  proof (cases "e = 0")
    case True
    show ?thesis
    apply (insert i x True)
    apply (rule realis_rat[where q = 4 and nn = "4 * b + 7" and tt = "4 * i + 6"])
    apply (auto simp: vF1_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  next
    case False
    then have eq1: "e = 1" using e by simp
    show ?thesis
    apply (insert i x eq1)
    apply (rule realis_rat[where q = 4 and nn = "4 * b + 9" and tt = "4 * i + 6"])
    apply (auto simp: vF1_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  qed
  show "realis b (vF1 b i e 1)"
  proof (cases "e = 0")
    case True
    show ?thesis
    apply (insert i x True)
    apply (rule realis_rat[where q = 6 and nn = "6 * b + 1" and tt = "6 * i + 4"])
    apply (auto simp: vF1_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  next
    case False
    then have eq1: "e = 1" using e by simp
    show ?thesis
    apply (insert i x eq1)
    apply (rule realis_rat[where q = 4 and nn = "4 * b + 1" and tt = "4 * i + 2"])
    apply (auto simp: vF1_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  qed
  show "vF1 b i e 0 (-3) \<noteq> vF1 b i e 1 (-3)" by (simp add: vF1_def)
  show "Zms 3 b (vF1 b i e 0) = Zms 3 b (vF1 b i e 1)"
    by (rule Zms_perm[where phi = "phiF1 i"]) (use i x e0 e1 F1_mem F1_inv F1_H in auto)
qed

section \<open>F2\<close>

text \<open>Paper II, line F2: P=(x,y,z,w,B^3), Q=(x+1,y,z,w-1,B^3); x=b-4-4i, y=b-3-3i+eps, z=b-2-2i+eps, w=b-i; x>=-1.  vF2 b i e s is P for s = 0 and Q for s = 1.\<close>

definition vF2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "vF2 b i e s h = (if h = -3 then b - 4 - 4 * i + s else if h = -2 then b - 3 - 3 * i + e else if h = -1 then b - 2 - 2 * i + e else if h = 0 then b - i - s else b)"

definition phiF2 :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "phiF2 i p = (case p of (r, j) \<Rightarrow>
     if r = 0 \<and> i + 1 \<le> j \<and> j \<le> i + 1 + i + 1 - 1 then (1, j - (i + 1) + 0)
     else if r = 1 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + i + 1)
     else if r = 0 \<and> 2 * i + 2 \<le> j \<and> j \<le> 2 * i + 2 + i + 1 - 1 then (2, j - (2 * i + 2) + 0)
     else if r = 2 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + 2 * i + 2)
     else if r = 0 \<and> 3 * i + 3 \<le> j \<and> j \<le> 3 * i + 3 + i + 1 - 1 then (3, j - (3 * i + 3) + 0)
     else if r = 3 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + 3 * i + 3)
     else (r, j))"

lemma F2_H:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i" and e0: "0 \<le> e" and e1: "e \<le> 1" and r: "0 \<le> r" "r \<le> 3" and j: "0 \<le> j" "j \<le> b"
  shows "Hval 3 b (vF2 b i e 1) (fst (phiF2 i (r, j))) (snd (phiF2 i (r, j))) = Hval 3 b (vF2 b i e 0) r j"

proof -
  have b0: "0 \<le> b" using i x e0 e1 by arith
  consider (c0) "r = 0" | (c1) "r = 1" | (c2) "r = 2" | (c3) "r = 3" using r by arith
  then show ?thesis
  proof cases
    case c0
    show ?thesis
      using i x e0 e1 j
      by (simp add: c0 phiF2_def Hval3 vF2_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c1
    show ?thesis
      using i x e0 e1 j
      by (simp add: c1 phiF2_def Hval3 vF2_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c2
    show ?thesis
      using i x e0 e1 j
      by (simp add: c2 phiF2_def Hval3 vF2_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c3
    show ?thesis
      using i x e0 e1 j
      by (simp add: c3 phiF2_def Hval3 vF2_def fcl_alt[OF b0] split: if_splits; arith?)
  qed
qed

lemma F2_mem:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF2 i p \<in> {0..3} \<times> {0..b}"
  using p i x by (cases p) (auto simp: phiF2_def split: if_splits; arith?)

lemma F2_inv:
  assumes i: "0 \<le> i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF2 i (phiF2 i p) = p"
  using p i by (cases p) (auto simp: phiF2_def split: if_splits; arith?)

theorem thm_F2:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i" and e: "e = 0 \<or> e = 1"
  shows "realis b (vF2 b i e 0)" "realis b (vF2 b i e 1)" "vF2 b i e 0 (-3) \<noteq> vF2 b i e 1 (-3)"
    "Zms 3 b (vF2 b i e 0) = Zms 3 b (vF2 b i e 1)"
proof -
  have e0: "0 \<le> e" and e1: "e \<le> 1" using e by auto
  show "realis b (vF2 b i e 0)"
  proof (cases "e = 0")
    case True
    show ?thesis
    apply (insert i x True)
    apply (rule realis_rat[where q = 6 and nn = "6 * b - 6 * i + 1" and tt = "6 * i + 8"])
    apply (auto simp: vF2_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  next
    case False
    then have eq1: "e = 1" using e by simp
    show ?thesis
    apply (insert i x eq1)
    apply (rule realis_rat[where q = 6 and nn = "6 * b - 6 * i + 5" and tt = "6 * i + 8"])
    apply (auto simp: vF2_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  qed
  show "realis b (vF2 b i e 1)"
  proof (cases "e = 0")
    case True
    show ?thesis
    apply (insert i x True)
    apply (rule realis_rat[where q = 8 and nn = "8 * b - 8 * i - 5" and tt = "8 * i + 6"])
    apply (auto simp: vF2_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  next
    case False
    then have eq1: "e = 1" using e by simp
    show ?thesis
    apply (insert i x eq1)
    apply (rule realis_rat[where q = 6 and nn = "6 * b - 6 * i - 1" and tt = "6 * i + 4"])
    apply (auto simp: vF2_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  qed
  show "vF2 b i e 0 (-3) \<noteq> vF2 b i e 1 (-3)" by (simp add: vF2_def)
  show "Zms 3 b (vF2 b i e 0) = Zms 3 b (vF2 b i e 1)"
    by (rule Zms_perm[where phi = "phiF2 i"]) (use i x e0 e1 F2_mem F2_inv F2_H in auto)
qed

section \<open>F3\<close>

text \<open>Paper II, line F3: P=(x,y,B^5), Q=(x+1,y-1,B^5); x=b-6-2i, y=b-2-i; x>=-1.  vF3 b i s is P for s = 0 and Q for s = 1.\<close>

definition vF3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "vF3 b i s h = (if h = -3 then b - 6 - 2 * i + s else if h = -2 then b - 2 - i - s else b)"

definition phiF3 :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "phiF3 i p = (case p of (r, j) \<Rightarrow>
     if r = 0 \<and> i + 3 \<le> j \<and> j \<le> i + 3 + i + 3 - 1 then (1, j - (i + 3) + 0)
     else if r = 1 \<and> 0 \<le> j \<and> j \<le> 0 + i + 3 - 1 then (0, j - (0) + i + 3)
     else (r, j))"

lemma F3_H:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 2 * i" and r: "0 \<le> r" "r \<le> 3" and j: "0 \<le> j" "j \<le> b"
  shows "Hval 3 b (vF3 b i 1) (fst (phiF3 i (r, j))) (snd (phiF3 i (r, j))) = Hval 3 b (vF3 b i 0) r j"

proof -
  have b0: "0 \<le> b" using i x by arith
  consider (c0) "r = 0" | (c1) "r = 1" | (c2) "r = 2" | (c3) "r = 3" using r by arith
  then show ?thesis
  proof cases
    case c0
    show ?thesis
      using i x j
      by (simp add: c0 phiF3_def Hval3 vF3_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c1
    show ?thesis
      using i x j
      by (simp add: c1 phiF3_def Hval3 vF3_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c2
    show ?thesis
      using i x j
      by (simp add: c2 phiF3_def Hval3 vF3_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c3
    show ?thesis
      using i x j
      by (simp add: c3 phiF3_def Hval3 vF3_def fcl_alt[OF b0] split: if_splits; arith?)
  qed
qed

lemma F3_mem:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 2 * i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF3 i p \<in> {0..3} \<times> {0..b}"
  using p i x by (cases p) (auto simp: phiF3_def split: if_splits; arith?)

lemma F3_inv:
  assumes i: "0 \<le> i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF3 i (phiF3 i p) = p"
  using p i by (cases p) (auto simp: phiF3_def split: if_splits; arith?)

theorem thm_F3:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 2 * i"
  shows "realis b (vF3 b i 0)" "realis b (vF3 b i 1)" "vF3 b i 0 (-3) \<noteq> vF3 b i 1 (-3)"
    "Zms 3 b (vF3 b i 0) = Zms 3 b (vF3 b i 1)"
proof -
  show "realis b (vF3 b i 0)"
  apply (insert i x)
  apply (rule realis_rat[where q = 2 and nn = "2 * b + 2 * i + 13" and tt = "2 * i + 8"])
  apply (auto simp: vF3_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "realis b (vF3 b i 1)"
  apply (insert i x)
  apply (rule realis_rat[where q = 4 and nn = "4 * b + 4 * i + 11" and tt = "4 * i + 10"])
  apply (auto simp: vF3_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "vF3 b i 0 (-3) \<noteq> vF3 b i 1 (-3)" by (simp add: vF3_def)
  show "Zms 3 b (vF3 b i 0) = Zms 3 b (vF3 b i 1)"
    by (rule Zms_perm[where phi = "phiF3 i"]) (use i x F3_mem F3_inv F3_H in auto)
qed

section \<open>F4\<close>

text \<open>Paper II, line F4: P=(x,y,z,w,B^3), Q=(x+1,y+1,z-1,w-1,B^3); x=b-4-4i, y=b-3-3i, z=b-1-2i, w=b-i; x>=-1.  vF4 b i s is P for s = 0 and Q for s = 1.\<close>

definition vF4 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "vF4 b i s h = (if h = -3 then b - 4 - 4 * i + s else if h = -2 then b - 3 - 3 * i + s else if h = -1 then b - 1 - 2 * i - s else if h = 0 then b - i - s else b)"

definition phiF4 :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "phiF4 i p = (case p of (r, j) \<Rightarrow>
     if r = 0 \<and> i + 1 \<le> j \<and> j \<le> i + 1 + i + 1 - 1 then (1, j - (i + 1) + 0)
     else if r = 1 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + i + 1)
     else if r = 0 \<and> 2 * i + 2 \<le> j \<and> j \<le> 2 * i + 2 + i + 1 - 1 then (2, j - (2 * i + 2) + 0)
     else if r = 2 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + 2 * i + 2)
     else if r = 0 \<and> 3 * i + 3 \<le> j \<and> j \<le> 3 * i + 3 + i + 1 - 1 then (3, j - (3 * i + 3) + 0)
     else if r = 3 \<and> 0 \<le> j \<and> j \<le> 0 + i + 1 - 1 then (0, j - (0) + 3 * i + 3)
     else if r = 1 \<and> 2 * i + 2 \<le> j \<and> j \<le> 2 * i + 2 + i + 1 - 1 then (2, j - (2 * i + 2) + i + 1)
     else if r = 2 \<and> i + 1 \<le> j \<and> j \<le> i + 1 + i + 1 - 1 then (1, j - (i + 1) + 2 * i + 2)
     else (r, j))"

lemma F4_H:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i" and r: "0 \<le> r" "r \<le> 3" and j: "0 \<le> j" "j \<le> b"
  shows "Hval 3 b (vF4 b i 1) (fst (phiF4 i (r, j))) (snd (phiF4 i (r, j))) = Hval 3 b (vF4 b i 0) r j"

proof -
  have b0: "0 \<le> b" using i x by arith
  consider (c0) "r = 0" | (c1) "r = 1" | (c2) "r = 2" | (c3) "r = 3" using r by arith
  then show ?thesis
  proof cases
    case c0
    show ?thesis
      using i x j
      by (simp add: c0 phiF4_def Hval3 vF4_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c1
    show ?thesis
      using i x j
      by (simp add: c1 phiF4_def Hval3 vF4_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c2
    show ?thesis
      using i x j
      by (simp add: c2 phiF4_def Hval3 vF4_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c3
    show ?thesis
      using i x j
      by (simp add: c3 phiF4_def Hval3 vF4_def fcl_alt[OF b0] split: if_splits; arith?)
  qed
qed

lemma F4_mem:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF4 i p \<in> {0..3} \<times> {0..b}"
  using p i x by (cases p) (auto simp: phiF4_def split: if_splits; arith?)

lemma F4_inv:
  assumes i: "0 \<le> i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF4 i (phiF4 i p) = p"
  using p i by (cases p) (auto simp: phiF4_def split: if_splits; arith?)

theorem thm_F4:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 4 - 4 * i"
  shows "realis b (vF4 b i 0)" "realis b (vF4 b i 1)" "vF4 b i 0 (-3) \<noteq> vF4 b i 1 (-3)"
    "Zms 3 b (vF4 b i 0) = Zms 3 b (vF4 b i 1)"
proof -
  show "realis b (vF4 b i 0)"
  apply (insert i x)
  apply (rule realis_rat[where q = 4 and nn = "4 * b - 4 * i + 3" and tt = "4 * i + 6"])
  apply (auto simp: vF4_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "realis b (vF4 b i 1)"
  apply (insert i x)
  apply (rule realis_rat[where q = 6 and nn = "6 * b - 6 * i - 3" and tt = "6 * i + 4"])
  apply (auto simp: vF4_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "vF4 b i 0 (-3) \<noteq> vF4 b i 1 (-3)" by (simp add: vF4_def)
  show "Zms 3 b (vF4 b i 0) = Zms 3 b (vF4 b i 1)"
    by (rule Zms_perm[where phi = "phiF4 i"]) (use i x F4_mem F4_inv F4_H in auto)
qed

section \<open>F5\<close>

text \<open>Paper II, line F5: P=(x,y,z,w,v,B^2), Q=(x,y+1,z,w-1,v,B^2); x=b-7-5i, y=b-6-4i, z=b-4-3i, w=b-2-2i, v=b-1-i; y>=-1.  vF5 b i s is P for s = 0 and Q for s = 1.\<close>

definition vF5 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "vF5 b i s h = (if h = -3 then b - 7 - 5 * i else if h = -2 then b - 6 - 4 * i + s else if h = -1 then b - 4 - 3 * i else if h = 0 then b - 2 - 2 * i - s else if h = 1 then b - 1 - i else b)"

definition phiF5 :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "phiF5 i p = (case p of (r, j) \<Rightarrow>
     if r = 0 \<and> 2 * i + 3 \<le> j \<and> j \<le> 2 * i + 3 + 2 * i + 3 - 1 then (2, j - (2 * i + 3) + 0)
     else if r = 2 \<and> 0 \<le> j \<and> j \<le> 0 + 2 * i + 3 - 1 then (0, j - (0) + 2 * i + 3)
     else if r = 1 \<and> 2 * i + 3 \<le> j \<and> j \<le> 2 * i + 3 + 2 * i + 3 - 1 then (3, j - (2 * i + 3) + 0)
     else if r = 3 \<and> 0 \<le> j \<and> j \<le> 0 + 2 * i + 3 - 1 then (1, j - (0) + 2 * i + 3)
     else (r, j))"

lemma F5_H:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 4 * i" and r: "0 \<le> r" "r \<le> 3" and j: "0 \<le> j" "j \<le> b"
  shows "Hval 3 b (vF5 b i 1) (fst (phiF5 i (r, j))) (snd (phiF5 i (r, j))) = Hval 3 b (vF5 b i 0) r j"

proof -
  have b0: "0 \<le> b" using i x by arith
  consider (c0) "r = 0" | (c1) "r = 1" | (c2) "r = 2" | (c3) "r = 3" using r by arith
  then show ?thesis
  proof cases
    case c0
    show ?thesis
      using i x j
      by (simp add: c0 phiF5_def Hval3 vF5_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c1
    show ?thesis
      using i x j
      by (simp add: c1 phiF5_def Hval3 vF5_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c2
    show ?thesis
      using i x j
      by (simp add: c2 phiF5_def Hval3 vF5_def fcl_alt[OF b0] split: if_splits; arith?)
  next
    case c3
    show ?thesis
      using i x j
      by (simp add: c3 phiF5_def Hval3 vF5_def fcl_alt[OF b0] split: if_splits; arith?)
  qed
qed

lemma F5_mem:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 4 * i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF5 i p \<in> {0..3} \<times> {0..b}"
  using p i x by (cases p) (auto simp: phiF5_def split: if_splits; arith?)

lemma F5_inv:
  assumes i: "0 \<le> i" and p: "p \<in> {0..3} \<times> {0..b}"
  shows "phiF5 i (phiF5 i p) = p"
  using p i by (cases p) (auto simp: phiF5_def split: if_splits; arith?)

theorem thm_F5:
  assumes i: "0 \<le> i" and x: "-1 \<le> b - 6 - 4 * i"
  shows "realis b (vF5 b i 0)" "realis b (vF5 b i 1)" "vF5 b i 0 (-2) \<noteq> vF5 b i 1 (-2)"
    "Zms 3 b (vF5 b i 0) = Zms 3 b (vF5 b i 1)"
proof -
  show "realis b (vF5 b i 0)"
  apply (insert i x)
  apply (rule realis_rat[where q = 6 and nn = "6 * b - 12 * i - 11" and tt = "6 * i + 10"])
  apply (auto simp: vF5_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "realis b (vF5 b i 1)"
  apply (insert i x)
  apply (rule realis_rat[where q = 6 and nn = "6 * b - 12 * i - 13" and tt = "6 * i + 8"])
  apply (auto simp: vF5_def clipb_def min_def max_def split: if_splits)
  apply ((presburger)+)?
  done
  show "vF5 b i 0 (-2) \<noteq> vF5 b i 1 (-2)" by (simp add: vF5_def)
  show "Zms 3 b (vF5 b i 0) = Zms 3 b (vF5 b i 1)"
    by (rule Zms_perm[where phi = "phiF5 i"]) (use i x F5_mem F5_inv F5_H in auto)
qed

section \<open>S1: the family of denominator five (realisability and distinctness)\<close>

text \<open>Paper II, Theorem S1 (the family S_1): for m in {2,3}, rho in {0,1} and n >= 1 with x = b-4n+rho >= -1,
  s = 5b+4-5n+rho and y = b+1-m, the vectors c = (x, y, B^5) and G = G_{m/5}(s) = (clip floor((s+mh)/5))_h
  are distinct and realisable.  Only this part (the paragraph "Witnesses" of the proof) is formalised here:
  the words Z(c), Z(G) and their equality are NOT.\<close>

definition cS :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "cS b n rho m h = (if h = -3 then b - 4 * n + rho else if h = -2 then b + 1 - m else b)"

definition gS :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "gS b s m h = clipb b ((s + m * h) div 5)"

theorem thm_S1_witnesses:
  assumes m: "m = 2 \<or> m = 3" and rho: "rho = 0 \<or> rho = 1" and n: "1 \<le> n" and x: "-1 \<le> b - 4 * n + rho"
  shows "realis b (cS b n rho m)" "realis b (gS b (5 * b + 4 - 5 * n + rho) m)"
    "cS b n rho m (-1) \<noteq> gS b (5 * b + 4 - 5 * n + rho) m (-1)"
proof -
  show "realis b (cS b n rho m)"
    apply (insert m rho n x)
    apply (rule realis_rat[where q = 4 and nn = "12 * (b + 1 - m) - 8 * (b - 4 * n + rho) + 7"
                             and tt = "4 * ((b + 1 - m) - (b - 4 * n + rho)) + 2"])
    apply (auto simp: cS_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  show "realis b (gS b (5 * b + 4 - 5 * n + rho) m)"
    apply (insert m rho n x)
    apply (rule realis_rat[where q = 10 and nn = "2 * (5 * b + 4 - 5 * n + rho) + 1" and tt = "2 * m"])
    apply (auto simp: gS_def clipb_def min_def max_def split: if_splits)
    apply ((presburger)+)?
    done
  show "cS b n rho m (-1) \<noteq> gS b (5 * b + 4 - 5 * n + rho) m (-1)"
    using m rho n x by (auto simp: cS_def gS_def clipb_def min_def max_def split: if_splits; presburger?)
qed


end
