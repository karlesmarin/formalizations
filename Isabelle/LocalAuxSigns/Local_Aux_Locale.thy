(*  Title:      Local_Aux_Locale.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: Lemma "aux" (extension of local signs with product 1)
   of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal dilations" (Carles Marín,
   in preparation), Section "One interior eigenvalue".

   PARTIAL formalization. The lemma is proved inside the locale local_quadratic_data. The ONLY unproved facts are the
   named assumptions of the locale (hilbert_values, unit_outside_S, hilbert_reciprocity, chebotarev_inert) plus the
   bookkeeping hypotheses finite_S, delta_pos, D_pos; no proof gaps and no quick-and-dirty mode. The number theory
   (Hilbert symbols, Hilbert reciprocity, Chebotarev density) is NOT formalized: it enters only through those
   assumptions. The local data (squares in Q_v, Hilbert symbol, inertness in L = Q(sqrt(-delta))) are abstract
   parameters of the locale.

   Finding of the formalization: for d = 0 or r = 0 the set R_v(0,D) = {1} requires D to be a square in Q_v at EVERY
   v, also outside S, where "D is a unit" does not give it. The lemma therefore carries the hypothesis dim0
   (D is a square in Q_v for v outside S when d = 0 or r = 0); the paper's statement does not make it explicit.
*)
theory Local_Aux_Locale
  imports Main "HOL.Rat"
begin

section \<open>The locale: abstract local data and the four named facts\<close>

locale local_quadratic_data =
  fixes sq :: "'p \<Rightarrow> rat \<Rightarrow> bool"          \<comment> \<open>sq v x: x is a square in Q_v\<close>
    and hil :: "'p \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int"  \<comment> \<open>hil v a b: the Hilbert symbol (a,b)_v\<close>
    and dl :: rat                            \<comment> \<open>delta, with L = Q(sqrt(-delta))\<close>
    and D :: rat
    and inert :: "'p \<Rightarrow> bool"             \<comment> \<open>v is inert in L\<close>
    and S :: "'p set"                        \<comment> \<open>the finite set of primes of the lemma\<close>
  assumes finite_S: "finite S"
    and delta_pos: "0 < dl"
    and D_pos: "0 < D"
    \<comment> \<open>Hilbert symbols take the values +1, -1 (definition of the Hilbert symbol).\<close>
    and hilbert_values: "\<And>v a b. hil v a b = 1 \<or> hil v a b = -1"
    \<comment> \<open>D is a unit and v is odd outside S, so (D,-1)_v = 1 (standard computation of the symbol of two units).\<close>
    and unit_outside_S: "\<And>v. v \<notin> S \<Longrightarrow> hil v D (-1) = 1"
    \<comment> \<open>Hilbert reciprocity: prod_v (D,-1)_v = 1, with finite support.\<close>
    and hilbert_reciprocity:
      "finite {v. hil v D (-1) \<noteq> 1} \<and> (\<Prod>v\<in>{v. hil v D (-1) \<noteq> 1}. hil v D (-1)) = 1"
    \<comment> \<open>Chebotarev density theorem: a prime outside S inert in L and in Q(sqrt(-D)) (or only in L if the fields
        coincide) exists; there -D is not a square and (D,-1)_v = 1.\<close>
    and chebotarev_inert:
      "\<exists>v1. v1 \<notin> S \<and> inert v1 \<and> \<not> sq v1 (-D) \<and> hil v1 D (-1) = 1"
begin

section \<open>The sets R_v(t,D) of the paper\<close>

definition R :: "'p \<Rightarrow> nat \<Rightarrow> int set" where
  "R v t = (if t = 0 then (if sq v D then {1} else {})
            else if t = 1 then {1}
            else if t = 2 then (if sq v (-D) then {1} else {1, -1})
            else {1, -1})"

text \<open>Both local conditions at v for the sign e.\<close>
definition ok :: "'p \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "ok v d r e \<longleftrightarrow> e \<in> R v d \<and> e * hil v D (-1) \<in> R v r"

lemma R_sub: "R v t \<subseteq> {1, -1}"
  by (auto simp: R_def split: if_splits)

lemma R_le1: "t \<le> 1 \<Longrightarrow> R v t \<subseteq> {1}"
  by (auto simp: R_def)

lemma R_one: "(1 \<le> t \<or> sq v D) \<Longrightarrow> 1 \<in> R v t"
  by (auto simp: R_def)

lemma R_ge2: "2 \<le> t \<Longrightarrow> \<not> sq v (-D) \<Longrightarrow> R v t = {1, -1}"
  by (auto simp: R_def)

lemma prod_pm:
  assumes "finite A" "\<forall>a\<in>A. f a = 1 \<or> f a = (-1::int)"
  shows "prod f A = 1 \<or> prod f A = -1"
  using assms by (induction A rule: finite_induct) auto

section \<open>Lemma aux\<close>

lemma aux:
  fixes d r :: nat and eps :: "'p \<Rightarrow> int"
  assumes loc: "\<forall>v\<in>S. ok v d r (eps v)"
    and dim0: "(d = 0 \<or> r = 0) \<longrightarrow> (\<forall>v. v \<notin> S \<longrightarrow> sq v D)"
  shows "\<exists>e. (\<forall>v\<in>S. e v = eps v)
       \<and> (\<forall>v. v \<notin> S \<longrightarrow> e v \<noteq> 1 \<longrightarrow> inert v \<and> (\<forall>w. w \<notin> S \<longrightarrow> e w \<noteq> 1 \<longrightarrow> w = v))
       \<and> (\<forall>v. ok v d r (e v))
       \<and> finite {v. e v \<noteq> 1} \<and> (\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1"
proof -
  have fS: "finite S" by (rule finite_S)
  have eps_pm: "\<forall>v\<in>S. eps v = 1 \<or> eps v = -1"
    using loc R_sub unfolding ok_def by blast
  define e0 where "e0 v = (if v \<in> S then eps v else 1)" for v
  have e0S: "\<And>v. v \<in> S \<Longrightarrow> e0 v = eps v" by (simp add: e0_def)
  have e0out: "\<And>v. v \<notin> S \<Longrightarrow> e0 v = 1" by (simp add: e0_def)
  have ok_out: "\<And>v. v \<notin> S \<Longrightarrow> ok v d r 1"
  proof -
    fix v assume v: "v \<notin> S"
    have h: "hil v D (-1) = 1" by (rule unit_outside_S[OF v])
    have s: "d = 0 \<or> r = 0 \<longrightarrow> sq v D" using dim0 v by blast
    have "1 \<in> R v d" using R_one s by (cases "d = 0") auto
    moreover have "1 * hil v D (-1) \<in> R v r" using h R_one s by (cases "r = 0") auto
    ultimately show "ok v d r 1" by (simp add: ok_def)
  qed
  have ok0: "\<And>v. ok v d r (e0 v)"
    using loc ok_out by (auto simp: e0_def)
  have supp0: "{v. e0 v \<noteq> 1} \<subseteq> S" using e0out by auto
  have fin0: "finite {v. e0 v \<noteq> 1}" using supp0 fS finite_subset by blast
  have prod0: "(\<Prod>v\<in>{v. e0 v \<noteq> 1}. e0 v) = (\<Prod>v\<in>S. eps v)"
  proof -
    have "prod e0 S = prod e0 {v. e0 v \<noteq> 1}"
      by (rule prod.mono_neutral_right[OF fS supp0]) auto
    moreover have "prod e0 S = prod eps S" by (rule prod.cong) (auto simp: e0S)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Cases d <= 1 and r <= 1 (including dimension 0): the product over S is already 1.\<close>
  have P1: "d \<le> 1 \<or> r \<le> 1 \<Longrightarrow> (\<Prod>v\<in>S. eps v) = 1"
  proof (elim disjE)
    assume d1: "d \<le> 1"
    have "\<forall>v\<in>S. eps v = 1"
      using loc R_le1[OF d1] unfolding ok_def by blast
    then show ?thesis by simp
  next
    assume r1: "r \<le> 1"
    have eq: "\<forall>v\<in>S. eps v = hil v D (-1)"
    proof
      fix v assume v: "v \<in> S"
      from loc v have c: "eps v * hil v D (-1) \<in> R v r" unfolding ok_def by blast
      then have c1: "eps v * hil v D (-1) = 1" using R_le1[OF r1] by blast
      from eps_pm v have e: "eps v = 1 \<or> eps v = -1" by blast
      from hilbert_values[of v D "-1"] have h: "hil v D (-1) = 1 \<or> hil v D (-1) = -1" .
      show "eps v = hil v D (-1)" using c1 e h by auto
    qed
    have suppH: "{v. hil v D (-1) \<noteq> 1} \<subseteq> S" using unit_outside_S by auto
    have "(\<Prod>v\<in>S. hil v D (-1)) = (\<Prod>v\<in>{v. hil v D (-1) \<noteq> 1}. hil v D (-1))"
      by (rule prod.mono_neutral_right[OF fS suppH]) auto
    also have "\<dots> = 1" using hilbert_reciprocity by blast
    finally have "(\<Prod>v\<in>S. hil v D (-1)) = 1" .
    moreover have "prod eps S = prod (\<lambda>v. hil v D (-1)) S"
      by (rule prod.cong[OF refl]) (use eq in auto)
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (cases "(\<Prod>v\<in>S. eps v) = 1")
    case True
    show ?thesis
      by (rule exI[of _ e0]) (use True ok0 fin0 prod0 e0S e0out in auto)
  next
    case False
    have Pm: "(\<Prod>v\<in>S. eps v) = -1" using prod_pm[OF fS eps_pm] False by blast
    have d2: "2 \<le> d"
    proof (rule ccontr)
      assume "\<not> 2 \<le> d" then have "d \<le> 1" by simp
      then show False using P1 False by blast
    qed
    have r2: "2 \<le> r"
    proof (rule ccontr)
      assume "\<not> 2 \<le> r" then have "r \<le> 1" by simp
      then show False using P1 False by blast
    qed
    obtain v1 where v1S: "v1 \<notin> S" and v1i: "inert v1" and v1n: "\<not> sq v1 (-D)"
      and v1h: "hil v1 D (-1) = 1" using chebotarev_inert by blast
    define e where "e = e0(v1 := -1)"
    have eS: "\<And>v. v \<in> S \<Longrightarrow> e v = eps v" using v1S by (auto simp: e_def e0S)
    have eout: "\<And>v. v \<notin> S \<Longrightarrow> v \<noteq> v1 \<Longrightarrow> e v = 1" by (simp add: e_def e0out)
    have ev1: "e v1 = -1" by (simp add: e_def)
    have okv1: "ok v1 d r (-1)"
      using R_ge2[OF d2 v1n] R_ge2[OF r2 v1n] v1h by (simp add: ok_def)
    have oke: "\<And>v. ok v d r (e v)"
    proof -
      fix v show "ok v d r (e v)"
      proof (cases "v = v1")
        case True then show ?thesis using okv1 ev1 by simp
      next
        case False then show ?thesis using ok0 by (simp add: e_def)
      qed
    qed
    have suppe: "{v. e v \<noteq> 1} \<subseteq> insert v1 S" using eout by auto
    have fine: "finite {v. e v \<noteq> 1}" using suppe fS finite_subset by blast
    have "prod e (insert v1 S) = prod e {v. e v \<noteq> 1}"
      by (rule prod.mono_neutral_right[OF _ suppe]) (use fS in auto)
    moreover have "prod e (insert v1 S) = e v1 * prod e S"
      using v1S fS by simp
    moreover have "prod e S = prod eps S" by (rule prod.cong) (auto simp: eS)
    ultimately have pe: "(\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1" using ev1 Pm by simp
    have only: "\<And>v. v \<notin> S \<Longrightarrow> e v \<noteq> 1 \<Longrightarrow> v = v1" using eout by blast
    have inr: "\<forall>v. v \<notin> S \<longrightarrow> e v \<noteq> 1 \<longrightarrow> inert v \<and> (\<forall>w. w \<notin> S \<longrightarrow> e w \<noteq> 1 \<longrightarrow> w = v)"
    proof (intro allI impI conjI)
      fix v assume v: "v \<notin> S" "e v \<noteq> 1"
      then have "v = v1" using only by blast
      then show "inert v" using v1i by simp
      fix w assume "w \<notin> S" "e w \<noteq> 1"
      then show "w = v" using only v \<open>v = v1\<close> by blast
    qed
    show ?thesis
      by (rule exI[of _ e]) (use eS oke fine pe inr in blast)
  qed
qed

end

end
