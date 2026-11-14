(*  Title:      Unitarity_Second_Order.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD
*)

theory Unitarity_Second_Order
  imports "HOL-Analysis.Analysis"
begin

text \<open>From "Exact limits for writing a quantum memory" (C. Marin, draft, November 2026), proof of the
  proposition on slow noise: the unitarity step.  If a perturbation @{text "V(\<epsilon>) = I - i\<epsilon>X\<^sub>1 - \<epsilon>\<^sup>2X\<^sub>2 + O(\<epsilon>^3)"}
  of the identity is unitary, then @{text "X\<^sub>1"} is Hermitian and @{text "X\<^sub>2 + X\<^sub>2\<^sup>H = X\<^sub>1\<^sup>2"}; the
  @{text "aa"} entry gives @{text "2 Re (X\<^sub>2)\<^sub>aa = |(X\<^sub>1)\<^sub>ba|\<^sup>2 + ((X\<^sub>1)\<^sub>aa)\<^sup>2"}, and then the squared
  modulus of the transferred amplitude is @{text "1 - \<epsilon>\<^sup>2 |(X\<^sub>1)\<^sub>ba|\<^sup>2 + O(\<epsilon>^3)"}.

  Representation: a @{text "2 \<times> 2"} complex matrix is a datatype with four complex entries
  (@{text "a11, a12, a21, a22"}); rows and columns are indexed by @{typ bool} (@{const True} is the
  first, @{const False} the second), so that sums over an index are sums over @{const UNIV}.
  The remainder @{text "R(\<epsilon>)"} is any function of the real @{text "\<epsilon>"} with all four entries bounded
  by @{text K} for @{text "\<bar>\<epsilon>\<bar> \<le> \<delta>"}.\<close>

section \<open>A. Two-by-two complex matrices\<close>

datatype cm = CM (a11: complex) (a12: complex) (a21: complex) (a22: complex)

fun ent :: "cm \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> complex" where
  "ent M True True = a11 M"
| "ent M True False = a12 M"
| "ent M False True = a21 M"
| "ent M False False = a22 M"

definition cmul :: "cm \<Rightarrow> cm \<Rightarrow> cm" where
  "cmul M N = CM (a11 M * a11 N + a12 M * a21 N) (a11 M * a12 N + a12 M * a22 N)
                 (a21 M * a11 N + a22 M * a21 N) (a21 M * a12 N + a22 M * a22 N)"

definition cadj :: "cm \<Rightarrow> cm" where
  "cadj M = CM (cnj (a11 M)) (cnj (a21 M)) (cnj (a12 M)) (cnj (a22 M))"

definition cadd :: "cm \<Rightarrow> cm \<Rightarrow> cm" where
  "cadd M N = CM (a11 M + a11 N) (a12 M + a12 N) (a21 M + a21 N) (a22 M + a22 N)"

definition cscal :: "complex \<Rightarrow> cm \<Rightarrow> cm" where
  "cscal c M = CM (c * a11 M) (c * a12 M) (c * a21 M) (c * a22 M)"

definition cone :: cm where
  "cone = CM 1 0 0 1"

text \<open>The perturbation @{text "I - i\<epsilon>X\<^sub>1 - \<epsilon>\<^sup>2X\<^sub>2 + \<epsilon>^3R"} for a real @{text "\<epsilon>"}.\<close>

definition cV :: "cm \<Rightarrow> cm \<Rightarrow> cm \<Rightarrow> real \<Rightarrow> cm" where
  "cV X1 X2 R e = cadd (cadd cone (cscal (- \<i> * of_real e) X1))
                       (cadd (cscal (- (of_real e)\<^sup>2) X2) (cscal ((of_real e)^3) R))"

definition cm_bd :: "real \<Rightarrow> cm \<Rightarrow> bool" where
  "cm_bd K M \<longleftrightarrow> norm (a11 M) \<le> K \<and> norm (a12 M) \<le> K \<and> norm (a21 M) \<le> K \<and> norm (a22 M) \<le> K"

lemma cm_bd_ent: "norm (ent M l m) \<le> K" if "cm_bd K M"
  using that by (cases l; cases m; simp add: cm_bd_def)

lemma sum_bool: "(\<Sum>l\<in>(UNIV :: bool set). f l) = f True + f False"
  by (simp add: UNIV_bool add.commute)

lemma ent_cmul: "ent (cmul M N) j k = (\<Sum>l\<in>(UNIV :: bool set) .ent M j l * ent N l k)"
  by (cases j; cases k; simp add: cmul_def sum_bool)

lemma ent_cadj: "ent (cadj M) j k = cnj (ent M k j)"
  by (cases j; cases k; simp add: cadj_def)

lemma ent_cone: "ent cone j k = (if j = k then 1 else 0)"
  by (cases j; cases k; simp add: cone_def)

lemma ent_cadd: "ent (cadd M N) j k = ent M j k + ent N j k"
  by (cases j; cases k; simp add: cadd_def)

lemma ent_V:
  "ent (cV X1 X2 R e) l j = (if l = j then 1 else 0) + of_real e * (- \<i> * ent X1 l j)
     + (of_real e)\<^sup>2 * (- ent X2 l j) + (of_real e)^3 * ent R l j"
  by (cases l; cases j; simp add: cV_def cadd_def cscal_def cone_def)

lemma cm_ext: "cm1 = cm2" if "\<And>j k. ent cm1 j k = ent cm2 j k"
  using that[of True True] that[of True False] that[of False True] that[of False False]
  by (cases cm1; cases cm2; simp)

section \<open>B. Two scalar tools\<close>

lemma small_zero:
  fixes c :: complex and \<delta> B :: real
  assumes "\<delta> > 0" and "\<And>e. 0 < e \<Longrightarrow> e \<le> \<delta> \<Longrightarrow> norm c \<le> e * B"
  shows "c = 0"
proof (rule ccontr)
  assume "c \<noteq> 0"
  then have n: "0 < norm c" by simp
  define B' where "B' = max B 0 + 1"
  have B'pos: "0 < B'" unfolding B'_def by simp
  have BB: "B \<le> B'" unfolding B'_def by simp
  define e where "e = min \<delta> (norm c / (2 * B'))"
  have e0: "0 < e" unfolding e_def using assms(1) n B'pos by simp
  have e1: "e \<le> \<delta>" unfolding e_def by simp
  have e2: "e \<le> norm c / (2 * B')" unfolding e_def by simp
  have "norm c \<le> e * B" using assms(2) e0 e1 by blast
  also have "\<dots> \<le> e * B'" using BB e0 by (intro mult_left_mono) auto
  also have "\<dots> \<le> norm c / (2 * B') * B'" using e2 B'pos by (intro mult_right_mono) auto
  also have "\<dots> = norm c / 2" using B'pos by simp
  finally show False using n by linarith
qed

definition bdd :: "real \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "bdd \<delta> f \<longleftrightarrow> (\<exists>M \<ge> 0. \<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (f e) \<le> M)"

lemma bdd_const: "bdd \<delta> (\<lambda>_. c)"
  unfolding bdd_def by (intro exI[of _ "norm c"]) auto

lemma bdd_eps: "bdd \<delta> (\<lambda>e. of_real e)" if "0 \<le> \<delta>"
  unfolding bdd_def using that by (intro exI[of _ \<delta>]) auto

lemma bdd_ex:
  assumes "bdd \<delta> f"
  shows "\<exists>M. 0 \<le> M \<and> (\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (f e) \<le> M)"
  using assms unfolding bdd_def by blast

lemma bdd_add:
  assumes bf: "bdd \<delta> f" and bg: "bdd \<delta> g"
  shows "bdd \<delta> (\<lambda>e. f e + g e)"
proof -
  obtain M1 where M1: "0 \<le> M1" and M1b: "\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (f e) \<le> M1"
    using bdd_ex[OF bf] by blast
  obtain M2 where M2: "0 \<le> M2" and M2b: "\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (g e) \<le> M2"
    using bdd_ex[OF bg] by blast
  have "norm (f e + g e) \<le> M1 + M2" if e: "\<bar>e\<bar> \<le> \<delta>" for e
  proof -
    have "norm (f e) \<le> M1" "norm (g e) \<le> M2" using M1b M2b e by blast+
    then show ?thesis using norm_triangle_ineq[of "f e" "g e"] by linarith
  qed
  then show ?thesis unfolding bdd_def using M1 M2 by (intro exI[of _ "M1 + M2"]) auto
qed

lemma bdd_mult:
  assumes bf: "bdd \<delta> f" and bg: "bdd \<delta> g"
  shows "bdd \<delta> (\<lambda>e. f e * g e)"
proof -
  obtain M1 where M1: "0 \<le> M1" and M1b: "\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (f e) \<le> M1"
    using bdd_ex[OF bf] by blast
  obtain M2 where M2: "0 \<le> M2" and M2b: "\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (g e) \<le> M2"
    using bdd_ex[OF bg] by blast
  have "norm (f e * g e) \<le> M1 * M2" if e: "\<bar>e\<bar> \<le> \<delta>" for e
  proof -
    have "norm (f e) \<le> M1" "norm (g e) \<le> M2" using M1b M2b e by blast+
    then show ?thesis unfolding norm_mult using M1 M2 by (intro mult_mono) auto
  qed
  then show ?thesis unfolding bdd_def using M1 M2 by (intro exI[of _ "M1 * M2"]) auto
qed

lemma bdd_cnj: "bdd \<delta> (\<lambda>e. cnj (f e))" if "bdd \<delta> f"
  using that unfolding bdd_def by simp

lemma bdd_entry:
  assumes "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow> norm (f e) \<le> K"
  shows "bdd \<delta> f"
proof -
  have "norm (f e) \<le> max K 0" if "\<bar>e\<bar> \<le> \<delta>" for e using assms[OF that] by simp
  then show ?thesis unfolding bdd_def by (intro exI[of _ "max K 0"]) auto
qed

lemma bdd_sum_bool: "bdd \<delta> (\<lambda>e. \<Sum>l\<in>(UNIV :: bool set). f l e)" if "\<And>l. bdd \<delta> (f l)"
  unfolding sum_bool by (intro bdd_add that)

section \<open>C. Expansion of a column product\<close>

lemma prod_expand:
  fixes e :: real and c0 c1 c2 c3 w0 w1 w2 w3 :: complex
  shows "cnj (c0 + of_real e * c1 + (of_real e)\<^sup>2 * c2 + (of_real e)^3 * c3)
           * (w0 + of_real e * w1 + (of_real e)\<^sup>2 * w2 + (of_real e)^3 * w3)
         = cnj c0 * w0 + of_real e * ((cnj c0 * w1 + cnj c1 * w0)
             + of_real e * ((cnj c0 * w2 + cnj c1 * w1 + cnj c2 * w0)
               + of_real e * ((cnj c0 * w3 + cnj c1 * w2 + cnj c2 * w1 + cnj c3 * w0)
                 + of_real e * ((cnj c1 * w3 + cnj c2 * w2 + cnj c3 * w1)
                   + of_real e * ((cnj c2 * w3 + cnj c3 * w2) + of_real e * (cnj c3 * w3))))))"
  by (simp add: algebra_simps power2_eq_square power3_eq_cube)

text \<open>If the product of two columns, summed over the rows, is constant for all small @{text "\<epsilon>"},
  the coefficients of @{text "\<epsilon>"} and @{text "\<epsilon>\<^sup>2"} vanish, provided the third-order parts are bounded.\<close>

lemma column_expansion:
  fixes Pa Pb Pc Qa Qb Qc :: "bool \<Rightarrow> complex" and Pd Qd :: "bool \<Rightarrow> real \<Rightarrow> complex" and t :: complex
    and \<delta> :: real
  assumes d: "\<delta> > 0" and bP: "\<And>l. bdd \<delta> (Pd l)" and bQ: "\<And>l. bdd \<delta> (Qd l)"
    and h: "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow>
      (\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l + of_real e * Pb l + (of_real e)\<^sup>2 * Pc l + (of_real e)^3 * Pd l e)
          * (Qa l + of_real e * Qb l + (of_real e)\<^sup>2 * Qc l + (of_real e)^3 * Qd l e)) = t"
  shows "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qa l) = t"
    and "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qb l + cnj (Pb l) * Qa l) = 0"
    and "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qc l + cnj (Pb l) * Qb l + cnj (Pc l) * Qa l) = 0"
proof -
  define A0 where "A0 = (\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qa l)"
  define A1 where "A1 = (\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qb l + cnj (Pb l) * Qa l)"
  define A2 where "A2 = (\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qc l + cnj (Pb l) * Qb l + cnj (Pc l) * Qa l)"
  define g where "g l e = (cnj (Pa l) * Qd l e + cnj (Pb l) * Qc l + cnj (Pc l) * Qb l
        + cnj (Pd l e) * Qa l)
      + of_real e * ((cnj (Pb l) * Qd l e + cnj (Pc l) * Qc l + cnj (Pd l e) * Qb l)
      + of_real e * ((cnj (Pc l) * Qd l e + cnj (Pd l e) * Qc l)
      + of_real e * (cnj (Pd l e) * Qd l e)))" for l e
  define G where "G e = (\<Sum>l\<in>(UNIV :: bool set) .g l e)" for e
  have d0: "0 \<le> \<delta>" using d by simp
  have bg: "bdd \<delta> (g l)" for l
    unfolding g_def
    by (intro bdd_add bdd_mult bdd_const bdd_eps bdd_cnj bP bQ d0)
  have bG: "bdd \<delta> G" unfolding G_def by (intro bdd_sum_bool bg)
  obtain M where M0: "0 \<le> M" and Mb: "\<forall>e. \<bar>e\<bar> \<le> \<delta> \<longrightarrow> norm (G e) \<le> M"
    using bdd_ex[OF bG] by blast
  have M: "norm (G e) \<le> M" if "\<bar>e\<bar> \<le> \<delta>" for e using Mb that by blast
  have exp: "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l + of_real e * Pb l + (of_real e)\<^sup>2 * Pc l + (of_real e)^3 * Pd l e)
          * (Qa l + of_real e * Qb l + (of_real e)\<^sup>2 * Qc l + (of_real e)^3 * Qd l e))
      = A0 + of_real e * (A1 + of_real e * (A2 + of_real e * G e))" for e
    unfolding A0_def A1_def A2_def G_def g_def prod_expand
    by (simp add: sum.distrib sum_distrib_left[symmetric])
  have eq: "A0 + of_real e * (A1 + of_real e * (A2 + of_real e * G e)) = t" if "\<bar>e\<bar> \<le> \<delta>" for e
    using h[OF that] exp by simp
  have A0t: "A0 = t" using eq[of 0] d0 by simp
  have step1: "A1 + of_real e * (A2 + of_real e * G e) = 0" if "0 < e" "e \<le> \<delta>" for e
  proof -
    have "of_real e * (A1 + of_real e * (A2 + of_real e * G e)) = 0"
      using eq[of e] that A0t by simp
    then show ?thesis using that(1) by simp
  qed
  have bd1: "norm A1 \<le> e * (norm A2 + \<delta> * M)" if e: "0 < e" "e \<le> \<delta>" for e
  proof -
    have "A1 = - (of_real e * (A2 + of_real e * G e))" using step1[OF e] by (simp add: eq_neg_iff_add_eq_0)
    then have "norm A1 = e * norm (A2 + of_real e * G e)" using e(1) by (simp add: norm_mult)
    also have "\<dots> \<le> e * (norm A2 + e * M)"
    proof (intro mult_left_mono)
      have "norm (A2 + of_real e * G e) \<le> norm A2 + norm (of_real e * G e)" by (rule norm_triangle_ineq)
      moreover have "norm (of_real e * G e) \<le> e * M"
        using M[of e] e by (simp add: norm_mult mult_left_mono)
      ultimately show "norm (A2 + of_real e * G e) \<le> norm A2 + e * M" by linarith
    qed (use e in auto)
    also have "\<dots> \<le> e * (norm A2 + \<delta> * M)"
      using e M0 by (intro mult_left_mono) (auto simp: mult_right_mono)
    finally show ?thesis .
  qed
  have A1z: "A1 = 0" by (rule small_zero[OF d bd1])
  have bd2: "norm A2 \<le> e * M" if e: "0 < e" "e \<le> \<delta>" for e
  proof -
    have "A2 + of_real e * G e = 0" using step1[OF e] A1z e(1) by simp
    then have "A2 = - (of_real e * G e)" by (simp add: eq_neg_iff_add_eq_0)
    then have "norm A2 = e * norm (G e)" using e(1) by (simp add: norm_mult)
    also have "\<dots> \<le> e * M" using M[of e] e by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  have A2z: "A2 = 0" by (rule small_zero[OF d bd2])
  show "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qa l) = t" using A0t unfolding A0_def .
  show "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qb l + cnj (Pb l) * Qa l) = 0" using A1z unfolding A1_def .
  show "(\<Sum>l\<in>(UNIV :: bool set) .cnj (Pa l) * Qc l + cnj (Pb l) * Qb l + cnj (Pc l) * Qa l) = 0" using A2z unfolding A2_def .
qed

section \<open>D. (U1) The coefficients of a unitary perturbation\<close>

text \<open>Entry-by-entry consequences of unitarity for all @{text "|\<epsilon>| \<le> \<delta>"}.\<close>

lemma unitary_entries:
  fixes X1 X2 :: cm and R :: "real \<Rightarrow> cm" and \<delta> K :: real
  assumes d: "\<delta> > 0" and rb: "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow> cm_bd K (R e)"
    and un: "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow> cmul (cadj (cV X1 X2 (R e) e)) (cV X1 X2 (R e) e) = cone"
  shows "\<i> * (cnj (ent X1 k j) - ent X1 j k) = 0"
    and "ent X2 j k + cnj (ent X2 k j) = (\<Sum>l\<in>(UNIV :: bool set) .cnj (ent X1 l j) * ent X1 l k)"
proof -
  have bR: "bdd \<delta> (\<lambda>e. ent (R e) l m)" for l m
    by (rule bdd_entry[of \<delta> _ K]) (use rb cm_bd_ent in blast)
  have hyp: "(\<Sum>l\<in>(UNIV :: bool set) .cnj ((if l = j then 1 else 0) + of_real e * (- \<i> * ent X1 l j)
                 + (of_real e)\<^sup>2 * (- ent X2 l j) + (of_real e)^3 * ent (R e) l j)
          * ((if l = k then 1 else 0) + of_real e * (- \<i> * ent X1 l k) + (of_real e)\<^sup>2 * (- ent X2 l k)
                 + (of_real e)^3 * ent (R e) l k)) = (if j = k then 1 else 0)"
    if e: "\<bar>e\<bar> \<le> \<delta>" for e
  proof -
    have "ent (cmul (cadj (cV X1 X2 (R e) e)) (cV X1 X2 (R e) e)) j k = ent cone j k"
      using un[OF e] by simp
    then show ?thesis by (simp add: ent_cmul ent_cadj ent_cone ent_V)
  qed
  note ce = column_expansion[where \<delta> = \<delta> and Pa = "\<lambda>l. if l = j then (1::complex) else 0"
      and Pb = "\<lambda>l. - \<i> * ent X1 l j" and Pc = "\<lambda>l. - ent X2 l j" and Pd = "\<lambda>l e. ent (R e) l j"
      and Qa = "\<lambda>l. if l = k then (1::complex) else 0" and Qb = "\<lambda>l. - \<i> * ent X1 l k"
      and Qc = "\<lambda>l. - ent X2 l k" and Qd = "\<lambda>l e. ent (R e) l k" and t = "if j = k then 1 else 0",
      OF d bR bR hyp]
  have c1: "(\<Sum>l\<in>(UNIV :: bool set) .cnj (if l = j then (1::complex) else 0) * (- \<i> * ent X1 l k)
                + cnj (- \<i> * ent X1 l j) * (if l = k then 1 else 0)) = 0"
    using ce(2) by simp
  have c2: "(\<Sum>l\<in>(UNIV :: bool set) .cnj (if l = j then (1::complex) else 0) * (- ent X2 l k)
                + cnj (- \<i> * ent X1 l j) * (- \<i> * ent X1 l k)
                + cnj (- ent X2 l j) * (if l = k then 1 else 0)) = 0"
    using ce(3) by simp
  show "\<i> * (cnj (ent X1 k j) - ent X1 j k) = 0"
    using c1 by (cases j; cases k; simp add: sum_bool algebra_simps)
  show "ent X2 j k + cnj (ent X2 k j) = (\<Sum>l\<in>(UNIV :: bool set) .cnj (ent X1 l j) * ent X1 l k)"
    using c2 by (cases j; cases k; simp add: sum_bool algebra_simps)
qed

theorem unitary_coefficients:
  fixes X1 X2 :: cm and R :: "real \<Rightarrow> cm" and \<delta> K :: real
  assumes "\<delta> > 0" and "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow> cm_bd K (R e)"
    and "\<And>e. \<bar>e\<bar> \<le> \<delta> \<Longrightarrow> cmul (cadj (cV X1 X2 (R e) e)) (cV X1 X2 (R e) e) = cone"
  shows "cadj X1 = X1"
    and "cadd X2 (cadj X2) = cmul X1 X1"
proof -
  have herm: "cnj (ent X1 k j) = ent X1 j k" for j k
    using unitary_entries(1)[OF assms] by simp
  show "cadj X1 = X1" by (rule cm_ext) (simp add: ent_cadj herm)
  show "cadd X2 (cadj X2) = cmul X1 X1"
  proof (rule cm_ext)
    show "ent (cadd X2 (cadj X2)) j k = ent (cmul X1 X1) j k" for j k
      using unitary_entries(2)[OF assms, of j k] by (simp add: ent_cadd ent_cadj ent_cmul herm)
  qed
qed

section \<open>E. (U2) The @{text "aa"} entry\<close>

theorem unitarity_aa:
  fixes X1 X2 :: cm
  assumes "cadj X1 = X1" and "cadd X2 (cadj X2) = cmul X1 X1"
  shows "Im (a11 X1) = 0"
    and "2 * Re (a11 X2) = (norm (a21 X1))\<^sup>2 + (Re (a11 X1))\<^sup>2"
proof -
  have h11: "cnj (a11 X1) = a11 X1"
    using arg_cong[OF assms(1), of a11] by (simp add: cadj_def)
  have h12: "cnj (a21 X1) = a12 X1"
    using arg_cong[OF assms(1), of a12] by (simp add: cadj_def)
  have e11: "a11 X2 + cnj (a11 X2) = a11 X1 * a11 X1 + a12 X1 * a21 X1"
    using arg_cong[OF assms(2), of a11] by (simp add: cadd_def cadj_def cmul_def)
  have im0: "Im (a11 X1) = 0"
    using arg_cong[OF h11, of Im] by simp
  then show "Im (a11 X1) = 0" .
  have e11': "a11 X2 + cnj (a11 X2) = a11 X1 * a11 X1 + cnj (a21 X1) * a21 X1"
    using e11 h12 by simp
  have step: "2 * Re (a11 X2) = Re (a11 X1) * Re (a11 X1)
      + (Re (a21 X1) * Re (a21 X1) + Im (a21 X1) * Im (a21 X1))"
    using arg_cong[OF e11', of Re] im0 by simp
  show "2 * Re (a11 X2) = (norm (a21 X1))\<^sup>2 + (Re (a11 X1))\<^sup>2"
    using step cmod_power2[of "a21 X1"] unfolding power2_eq_square by linarith
qed

section \<open>F. (U3) The modulus of the transferred amplitude\<close>

lemma modulus_expansion:
  fixes e a :: real and q :: complex
  shows "(norm (1 - \<i> * of_real e * of_real a - (of_real e)\<^sup>2 * q))\<^sup>2
    = 1 - 2 * e\<^sup>2 * Re q + e\<^sup>2 * a\<^sup>2 + e^3 * (2 * a * Im q + e * (norm q)\<^sup>2)"
  unfolding cmod_power2 by (simp add: power2_eq_square power3_eq_cube algebra_simps)

text \<open>Same, with the unitarity identity of (U2) inserted: with @{text "t = 1 - i\<epsilon>a - \<epsilon>\<^sup>2q"},
  @{text "a = (X\<^sub>1)\<^sub>aa"} and @{text "q = (X\<^sub>2)\<^sub>aa"}, @{text "|t|\<^sup>2 = 1 - \<epsilon>\<^sup>2|(X\<^sub>1)\<^sub>ba|\<^sup>2 + O(\<epsilon>^3)"}
  with the explicit third-order term.\<close>

theorem transfer_modulus:
  fixes X1 X2 :: cm and e :: real
  assumes "cadj X1 = X1" and "cadd X2 (cadj X2) = cmul X1 X1"
  shows "(norm (1 - \<i> * of_real e * a11 X1 - (of_real e)\<^sup>2 * a11 X2))\<^sup>2
    = 1 - e\<^sup>2 * (norm (a21 X1))\<^sup>2
      + e^3 * (2 * Re (a11 X1) * Im (a11 X2) + e * (norm (a11 X2))\<^sup>2)"
proof -
  have im0: "a11 X1 = of_real (Re (a11 X1))"
    using unitarity_aa(1)[OF assms] by (simp add: complex_eq_iff)
  have u2: "2 * Re (a11 X2) = (norm (a21 X1))\<^sup>2 + (Re (a11 X1))\<^sup>2"
    using unitarity_aa(2)[OF assms] .
  have "(norm (1 - \<i> * of_real e * a11 X1 - (of_real e)\<^sup>2 * a11 X2))\<^sup>2
      = 1 - 2 * e\<^sup>2 * Re (a11 X2) + e\<^sup>2 * (Re (a11 X1))\<^sup>2
        + e^3 * (2 * Re (a11 X1) * Im (a11 X2) + e * (norm (a11 X2))\<^sup>2)"
    using modulus_expansion[of e "Re (a11 X1)" "a11 X2"] unfolding im0[symmetric] .
  also have "\<dots> = 1 - e\<^sup>2 * (norm (a21 X1))\<^sup>2
      + e^3 * (2 * Re (a11 X1) * Im (a11 X2) + e * (norm (a11 X2))\<^sup>2)"
  proof -
    have r: "Re (a11 X2) = ((norm (a21 X1))\<^sup>2 + (Re (a11 X1))\<^sup>2) / 2" using u2 by simp
    show ?thesis by (simp add: r algebra_simps)
  qed
  finally show ?thesis .
qed

text \<open>Link with @{text "second_order_algebra"} of @{text "Slow_Noise_Second_Order"}: its hypothesis
  @{text "1 - 2w + f\<^sup>2 = 1 - e\<^sup>2z\<^sup>2"}, with @{text "w = Re (\<Xi>\<^sub>2)\<^sub>aa"}, @{text "f = \<xi>\<^sub>qA + \<xi>\<^sub>mB = (X\<^sub>1)\<^sub>aa"} and
  @{text "e z = |(X\<^sub>1)\<^sub>ba|"} (@{text "e = \<xi>\<^sub>q - \<xi>\<^sub>m"}, @{text "z = |\<zeta>|"}), is exactly what unitarity delivers.\<close>

corollary unitarity_hypothesis_of_second_order_algebra:
  fixes X1 X2 :: cm and e z :: real
  assumes "cadj X1 = X1" and "cadd X2 (cadj X2) = cmul X1 X1" and "norm (a21 X1) = \<bar>e\<bar> * z"
  shows "1 - 2 * Re (a11 X2) + (Re (a11 X1))\<^sup>2 = 1 - e\<^sup>2 * z\<^sup>2"
proof -
  have "(norm (a21 X1))\<^sup>2 = e\<^sup>2 * z\<^sup>2" using assms(3) by (simp add: power_mult_distrib)
  then show ?thesis using unitarity_aa(2)[OF assms(1,2)] by linarith
qed

end
