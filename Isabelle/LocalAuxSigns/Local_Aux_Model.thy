(*  Title:      Local_Aux_Model.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Non-vacuity of the locale local_quadratic_data of Local_Aux_Locale: two concrete models satisfy all its
   assumptions, and the lemma aux is instantiated in each of them.

   Model 1 is degenerate on purpose (trivial Hilbert symbol); model 2 has a nontrivial symbol (value -1 at two
   places, so that reciprocity is a real product). Neither model is the real Hilbert symbol of Q: the locale does
   not force that (see the comments below).
*)
theory Local_Aux_Model
  imports Local_Aux_Locale
begin

section \<open>Model 1: trivial symbol\<close>

text \<open>Primes are naturals; S = {2}; D = 1; delta = 1; sq v x iff x >= 0 (so -1 is a nonsquare everywhere);
  inert v iff v = 3; the Hilbert symbol is constantly 1.\<close>

interpretation m1: local_quadratic_data
  "\<lambda>(v::nat) (x::rat). 0 \<le> x" "\<lambda>(v::nat) (a::rat) (b::rat). (1::int)" 1 1 "\<lambda>v. v = 3" "{2::nat}"
proof unfold_locales
  show "finite {2::nat}" by simp
  show "(0::rat) < 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). (1::int) = 1 \<or> (1::int) = -1" by simp
  show "\<And>v::nat. v \<notin> {2} \<Longrightarrow> (1::int) = 1" by simp
  show "finite {v::nat. (1::int) \<noteq> 1} \<and> (\<Prod>v\<in>{v::nat. (1::int) \<noteq> 1}. (1::int)) = 1" by simp
  show "\<exists>v1::nat. v1 \<notin> {2} \<and> v1 = 3 \<and> \<not> (0::rat) \<le> - 1 \<and> (1::int) = 1" by simp
qed

text \<open>The lemma aux in model 1 with d = r = 2 and the sign -1 at v = 2 (product -1 over S): the extension
  needs one extra inert place, the one provided by the Chebotarev assumption.\<close>

lemma model1_aux_consequence:
  "\<exists>e::nat \<Rightarrow> int. e 2 = -1
     \<and> (\<forall>v. v \<notin> {2} \<longrightarrow> e v \<noteq> 1 \<longrightarrow> v = 3)
     \<and> (\<forall>v. m1.ok v 2 2 (e v))
     \<and> finite {v. e v \<noteq> 1} \<and> (\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1"
proof -
  have loc: "\<forall>v\<in>{2::nat}. m1.ok v 2 2 ((\<lambda>_. -1) v)"
    by (auto simp: m1.ok_def m1.R_def)
  have dim0: "(2 = (0::nat) \<or> 2 = (0::nat)) \<longrightarrow> (\<forall>v::nat. v \<notin> {2} \<longrightarrow> (0::rat) \<le> 1)" by simp
  from m1.aux[of 2 2 "\<lambda>_. -1", OF loc dim0]
  obtain e where e: "\<forall>v\<in>{2}. e v = -1"
    "\<forall>v. v \<notin> {2} \<longrightarrow> e v \<noteq> 1 \<longrightarrow> v = 3 \<and> (\<forall>w. w \<notin> {2} \<longrightarrow> e w \<noteq> 1 \<longrightarrow> w = v)"
    "\<forall>v. m1.ok v 2 2 (e v)" "finite {v. e v \<noteq> 1}" "(\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1"
    by blast
  show ?thesis
    by (rule exI[of _ e]) (use e in auto)
qed

section \<open>Model 2: nontrivial symbol, D = 2\<close>

text \<open>S = {2,3}; D = 2; delta = 1; sq v x iff x >= 0; inert v iff v = 5; the symbol (a,b)_v is -1 exactly when
  v in {2,3}, a = 2, b = -1, and 1 otherwise. Reciprocity: (-1)*(-1) = 1 over {2,3}; outside S the symbol is 1.\<close>

definition hil2 :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int" where
  "hil2 v a b = (if (v = 2 \<or> v = 3) \<and> a = 2 \<and> b = -1 then -1 else 1)"

lemma hil2_set: "{v. hil2 v 2 (-1) \<noteq> 1} = {2, 3}"
  by (auto simp: hil2_def)

interpretation m2: local_quadratic_data
  "\<lambda>(v::nat) (x::rat). 0 \<le> x" hil2 1 2 "\<lambda>v. v = 5" "{2::nat, 3}"
proof unfold_locales
  show "finite {2::nat, 3}" by simp
  show "(0::rat) < 1" by simp
  show "(0::rat) < 2" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). hil2 v a b = 1 \<or> hil2 v a b = -1" by (simp add: hil2_def)
  show "\<And>v::nat. v \<notin> {2, 3} \<Longrightarrow> hil2 v 2 (-1) = 1" by (simp add: hil2_def)
  show "finite {v. hil2 v 2 (-1) \<noteq> 1} \<and> (\<Prod>v\<in>{v. hil2 v 2 (-1) \<noteq> 1}. hil2 v 2 (-1)) = 1"
  proof -
    have "(\<Prod>v\<in>{2::nat, 3}. hil2 v 2 (-1)) = 1" by (simp add: hil2_def)
    then show ?thesis by (simp add: hil2_set)
  qed
  show "\<exists>v1::nat. v1 \<notin> {2, 3} \<and> v1 = 5 \<and> \<not> (0::rat) \<le> - 2 \<and> hil2 v1 2 (-1) = 1"
    by (simp add: hil2_def)
qed

text \<open>The lemma aux in model 2 with d = r = 2 and eps = (-1 at 2, +1 at 3): the product over S is -1, so the
  extension needs the inert place 5. Local condition at 2: e = -1 in R(2,2) = {1,-1} and
  e * hil2 2 2 (-1) = (-1)(-1) = 1 in R; at 3: 1 and -1 are both in {1,-1}.\<close>

lemma model2_aux_consequence:
  "\<exists>e::nat \<Rightarrow> int. e 2 = -1 \<and> e 3 = 1
     \<and> (\<forall>v. v \<notin> {2, 3} \<longrightarrow> e v \<noteq> 1 \<longrightarrow> v = 5)
     \<and> (\<forall>v. m2.ok v 2 2 (e v))
     \<and> finite {v. e v \<noteq> 1} \<and> (\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1"
proof -
  define eps :: "nat \<Rightarrow> int" where "eps v = (if v = 2 then -1 else 1)" for v
  have loc: "\<forall>v\<in>{2::nat, 3}. m2.ok v 2 2 (eps v)"
    by (auto simp: m2.ok_def m2.R_def eps_def hil2_def)
  have dim0: "(2 = (0::nat) \<or> 2 = (0::nat)) \<longrightarrow> (\<forall>v::nat. v \<notin> {2, 3} \<longrightarrow> (0::rat) \<le> 2)" by simp
  from m2.aux[of 2 2 eps, OF loc dim0]
  obtain e where e: "\<forall>v\<in>{2, 3}. e v = eps v"
    "\<forall>v. v \<notin> {2, 3} \<longrightarrow> e v \<noteq> 1 \<longrightarrow> v = 5 \<and> (\<forall>w. w \<notin> {2, 3} \<longrightarrow> e w \<noteq> 1 \<longrightarrow> w = v)"
    "\<forall>v. m2.ok v 2 2 (e v)" "finite {v. e v \<noteq> 1}" "(\<Prod>v\<in>{v. e v \<noteq> 1}. e v) = 1"
    by blast
  show ?thesis
    by (rule exI[of _ e]) (use e in \<open>auto simp: eps_def\<close>)
qed

text \<open>Remark on what the models show. The locale constrains hil only through: values in {1,-1}; value 1 at
  (D,-1) outside S; the reciprocity product at (D,-1); and one place with value 1 at (D,-1). It does not tie hil
  to sq, nor to a bilinear symbol, nor says anything on hil at other arguments (model 1 takes it constantly 1,
  model 2 is not bimultiplicative on all arguments either). So the locale is satisfiable, but it does not
  characterize the real Hilbert symbol; the paper's use only needs those four properties of (D,-1)_v.\<close>

end
