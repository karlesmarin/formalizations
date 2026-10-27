(*  Title:      Interlacing.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Interlacing

    Products of real linear factors and the cone of polynomials that interlace a given one.
*)

theory Interlacing
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Combinatorics.Permutations"
begin

section \<open>Products of real linear factors\<close>

definition lin_prod :: "real list \<Rightarrow> real poly" where
  "lin_prod rs = (\<Prod>r\<leftarrow>rs. [:-r, 1:])"

lemma lin_prod_Nil [simp]: "lin_prod [] = 1"
  by (simp add: lin_prod_def)

lemma lin_prod_Cons [simp]: "lin_prod (r # rs) = [:-r, 1:] * lin_prod rs"
  by (simp add: lin_prod_def)

lemma lin_prod_ne_0: "lin_prod rs \<noteq> 0"
proof (induction rs)
  case Nil then show ?case by simp
next
  case (Cons r rs)
  have h: "[:-r, 1:] \<noteq> (0::real poly)" by simp
  show ?case
    by (subst lin_prod_Cons, subst mult_eq_0_iff, use h Cons in blast)
qed

lemma degree_lin_prod [simp]: "degree (lin_prod rs) = length rs"
proof (induction rs)
  case Nil then show ?case by simp
next
  case (Cons r rs)
  have h: "[:-r, 1:] \<noteq> (0::real poly)" by simp
  have d: "degree [:-r, 1:] = (1::nat)" by simp
  have "degree ([:-r, 1:] * lin_prod rs) = degree [:-r, 1:] + degree (lin_prod rs)"
    by (rule degree_mult_eq[OF h lin_prod_ne_0])
  then show ?case using d Cons.IH by (subst lin_prod_Cons) simp
qed

lemma lead_coeff_lin_prod [simp]: "lead_coeff (lin_prod rs) = 1"
proof (induction rs)
  case Nil then show ?case by simp
next
  case (Cons r rs)
  have d: "lead_coeff [:-r, 1:] = (1::real)" by simp
  have "lead_coeff ([:-r, 1:] * lin_prod rs) = lead_coeff [:-r, 1:] * lead_coeff (lin_prod rs)"
    by (rule lead_coeff_mult)
  then show ?case using d Cons.IH by (subst lin_prod_Cons) simp
qed

lemma poly_lin_prod: "poly (lin_prod rs) x = (\<Prod>r\<leftarrow>rs. x - r)"
proof (induction rs)
  case Nil then show ?case by simp
next
  case (Cons r rs)
  have p: "poly [:-r, 1:] x = x - r" by simp
  show ?case
    by (subst lin_prod_Cons, simp only: poly_mult p Cons.IH, simp)
qed

lemma lin_prod_mset: "lin_prod rs = prod_mset (image_mset (\<lambda>r. [:-r, 1:]) (mset rs))"
  by (simp add: lin_prod_def prod_mset_prod_list[symmetric] mset_map)

lemma lin_prod_perm: "mset rs = mset ts \<Longrightarrow> lin_prod rs = lin_prod ts"
  by (simp add: lin_prod_mset)

lemma poly_lin_prod_zero: "poly (lin_prod ts) r = 0 \<Longrightarrow> r \<in> set ts"
proof (induction ts)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have p: "poly [:-t, 1:] r = r - t" by simp
  have "poly [:-t, 1:] r * poly (lin_prod ts) r = 0"
    using Cons.prems by (subst (asm) lin_prod_Cons) (simp only: poly_mult)
  then have "r - t = 0 \<or> poly (lin_prod ts) r = 0" using p by simp
  then show ?case using Cons.IH by auto
qed

lemma mset_eq_of_lin_prod_eq: "lin_prod rs = lin_prod ts \<Longrightarrow> mset rs = mset ts"
proof (induction rs arbitrary: ts)
  case Nil
  then have "length ts = 0" using degree_lin_prod[of ts] by simp
  then show ?case by simp
next
  case (Cons r rs)
  have "poly (lin_prod ts) r = poly (lin_prod (r # rs)) r" using Cons.prems by simp
  also have "\<dots> = 0" by simp
  finally have "r \<in> set ts" by (rule poly_lin_prod_zero)
  then have ts: "mset ts = add_mset r (mset (remove1 r ts))"
    by (simp add: mset_remove1 insert_DiffM)
  have "lin_prod ts = lin_prod (r # remove1 r ts)"
    by (rule lin_prod_perm, rule trans[OF ts]) simp
  then have "[:-r, 1:] * lin_prod rs = [:-r, 1:] * lin_prod (remove1 r ts)"
    using Cons.prems by simp
  then have "lin_prod rs = lin_prod (remove1 r ts)"
    by (rule mult_left_cancel[THEN iffD1, rotated]) simp
  then have "mset rs = mset (remove1 r ts)" by (rule Cons.IH)
  then show ?case by (subst ts) simp
qed

section \<open>The cone of interlacing polynomials\<close>

text \<open>\<open>q\<close> lies in the cone of the root list \<open>rs\<close> if it is a non-negative combination of the products
  obtained from \<open>lin_prod rs\<close> by leaving out one factor.\<close>

definition omit :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "omit i xs = take i xs @ drop (Suc i) xs"

definition in_cone :: "real poly \<Rightarrow> real list \<Rightarrow> bool" where
  "in_cone q rs \<longleftrightarrow> (\<exists>c. (\<forall>i<length rs. 0 \<le> c i) \<and>
     q = (\<Sum>i<length rs. smult (c i) (lin_prod (omit i rs))))"

lemma in_cone_zero: "in_cone 0 rs"
  unfolding in_cone_def by (rule exI[of _ "\<lambda>_. 0"]) simp

lemma in_cone_add: "in_cone p rs \<Longrightarrow> in_cone q rs \<Longrightarrow> in_cone (p + q) rs"
  unfolding in_cone_def
proof (elim exE conjE)
  fix c d
  assume c: "\<forall>i<length rs. 0 \<le> c i" and p: "p = (\<Sum>i<length rs. smult (c i) (lin_prod (omit i rs)))"
    and d: "\<forall>i<length rs. 0 \<le> d i" and q: "q = (\<Sum>i<length rs. smult (d i) (lin_prod (omit i rs)))"
  show "\<exists>e. (\<forall>i<length rs. 0 \<le> e i) \<and>
      p + q = (\<Sum>i<length rs. smult (e i) (lin_prod (omit i rs)))"
    by (rule exI[of _ "\<lambda>i. c i + d i"])
      (use c d in \<open>simp add: p q sum.distrib smult_add_left\<close>)
qed

lemma in_cone_sum: "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> in_cone (f a) rs) \<Longrightarrow> in_cone (\<Sum>a\<in>A. f a) rs"
proof (induction A rule: finite_induct)
  case empty then show ?case by (simp add: in_cone_zero)
next
  case (insert a A)
  then show ?case by (simp add: in_cone_add)
qed

lemma mset_omit: "i < length xs \<Longrightarrow> mset (omit i xs) = mset xs - {#xs ! i#}"
proof -
  assume i: "i < length xs"
  have "mset xs = mset (take i xs) + mset (drop i xs)"
    by (metis append_take_drop_id mset_append)
  moreover have "drop i xs = xs ! i # drop (Suc i) xs"
    using i by (simp add: Cons_nth_drop_Suc)
  ultimately have "mset xs = mset (take i xs) + (mset (drop (Suc i) xs) + {#xs ! i#})"
    by simp
  then show ?thesis by (simp add: omit_def add_ac)
qed

lemma in_cone_perm: "mset rs = mset ts \<Longrightarrow> in_cone q rs \<Longrightarrow> in_cone q ts"
  unfolding in_cone_def
proof (elim exE conjE)
  fix c
  assume m: "mset rs = mset ts"
    and c: "\<forall>i<length rs. 0 \<le> c i" and q: "q = (\<Sum>i<length rs. smult (c i) (lin_prod (omit i rs)))"
  have len: "length ts = length rs" using m by (metis size_mset)
  obtain f where f: "f permutes {..<length rs}" and ts: "permute_list f rs = ts"
    by (rule mset_eq_permutation[OF m[symmetric]])
  have bij: "bij_betw f {..<length rs} {..<length rs}" using f by (rule permutes_imp_bij)
  have key: "\<And>i. i < length rs \<Longrightarrow> lin_prod (omit i ts) = lin_prod (omit (f i) rs)"
  proof -
    fix i assume i: "i < length rs"
    have fi: "f i < length rs" using bij i by (auto simp: bij_betw_def)
    have tsi: "ts ! i = rs ! f i" unfolding ts[symmetric] by (rule permute_list_nth[OF f i])
    have "mset (omit i ts) = mset ts - {#ts ! i#}"
      by (rule mset_omit) (simp add: len i)
    also have "\<dots> = mset rs - {#rs ! f i#}" using m tsi by simp
    also have "\<dots> = mset (omit (f i) rs)" using mset_omit[OF fi] by simp
    finally show "lin_prod (omit i ts) = lin_prod (omit (f i) rs)" by (rule lin_prod_perm)
  qed
  have "(\<Sum>i<length rs. smult (c (f i)) (lin_prod (omit (f i) rs)))
      = (\<Sum>j<length rs. smult (c j) (lin_prod (omit j rs)))"
    by (rule sum.reindex_bij_betw[OF bij, of "\<lambda>j. smult (c j) (lin_prod (omit j rs))"])
  moreover have "(\<Sum>i<length rs. smult (c (f i)) (lin_prod (omit (f i) rs)))
      = (\<Sum>i<length rs. smult (c (f i)) (lin_prod (omit i ts)))"
    by (rule sum.cong) (simp_all add: key)
  ultimately have "q = (\<Sum>i<length ts. smult (c (f i)) (lin_prod (omit i ts)))"
    using q len by simp
  moreover have "\<forall>i<length ts. 0 \<le> c (f i)"
  proof (intro allI impI)
    fix i assume "i < length ts"
    then have i: "i < length rs" using len by simp
    have "f i < length rs" using bij i by (auto simp: bij_betw_def)
    then show "0 \<le> c (f i)" using c by blast
  qed
  ultimately show "\<exists>c. (\<forall>i<length ts. 0 \<le> c i) \<and>
      q = (\<Sum>i<length ts. smult (c i) (lin_prod (omit i ts)))"
    by (intro exI[of _ "\<lambda>i. c (f i)"]) blast
qed

end
