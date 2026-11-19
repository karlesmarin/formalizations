(* Title: Logarithmic scores, power profiles and sharp softmax witnesses
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Log_Scores
  imports TAF_Sharp_Binary TAF_Sensitivity
begin

definition finite_power_profile where
  "finite_power_profile S d g i=d i powr (-g)/(\<Sum>j\<in>S. d j powr (-g))"

lemma power_exponential_bridge:
  fixes d g :: real
  assumes "0<d"
  shows "d powr (-g)=exp (-g*ln d)"
  using assms by (simp add: powr_def mult.commute)

lemma logarithmic_softmax_power:
  assumes pos: "\<And>i. i\<in>S \<Longrightarrow> 0<d i" and i: "i\<in>S"
  shows "finite_softmax S (\<lambda>i. b-g*ln (d i)) i=finite_power_profile S d g i"
proof -
  have shift: "finite_softmax S (\<lambda>i. b-g*ln (d i))=finite_softmax S (\<lambda>i. -g*ln (d i))"
    using softmax_shift[where s="\<lambda>i. -g*ln (d i)" and c=b and S=S]
    by (simp add: add.commute)
  have denom: "(\<Sum>j\<in>S. d j powr (-g))=(\<Sum>j\<in>S. exp (-g*ln (d j)))"
    by (rule sum.cong[OF refl]; rule power_exponential_bridge[OF pos])
  show ?thesis by (simp only: shift finite_softmax_def finite_power_profile_def denom
      power_exponential_bridge[OF pos[OF i]])
qed

context finite_exp_family
begin

lemma positive_power_mixture_partition:
  assumes d: "0<d"
  shows "(\<Sum>i\<in>S. a i*(d powr (-E i)))=mom 0 (ln d)"
  by (simp add: mom_def power_exponential_bridge[OF d] mult.commute)

end

lemma logarithmic_score_stability:
  assumes fin: "finite S" and ne: "S\<noteq>{}"
    and pos: "\<And>i. i\<in>S \<Longrightarrow> 0<d i"
    and lo: "\<And>i. i\<in>S \<Longrightarrow> l\<le>r i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> r i\<le>u"
  shows "tv_distance S (finite_power_profile S d g)
      (finite_softmax S (\<lambda>i. b-g*ln (d i)+r i))\<le>tanh ((u-l)/4)"
proof -
  have bound: "tv_distance S (finite_softmax S (\<lambda>i. b-g*ln (d i)))
      (finite_softmax S (\<lambda>i. b-g*ln (d i)+r i))\<le>tanh ((u-l)/4)"
    by (rule softmax_oscillation_bound[OF fin ne lo hi])
  have sum_eq: "(\<Sum>i\<in>S. abs (finite_softmax S (\<lambda>i. b-g*ln (d i)) i-
      finite_softmax S (\<lambda>i. b-g*ln (d i)+r i) i))=
    (\<Sum>i\<in>S. abs (finite_power_profile S d g i-
      finite_softmax S (\<lambda>i. b-g*ln (d i)+r i) i))"
    by (rule sum.cong[OF refl]; simp only: logarithmic_softmax_power[OF pos])
  show ?thesis using bound unfolding tv_distance_def by (simp only: sum_eq)
qed

lemma softmax_sharp_binary:
  fixes w :: real
  assumes w: "0<w"
  defines "s \<equiv> \<lambda>b::bool. if b then 0 else w/2"
    and "r \<equiv> \<lambda>b::bool. if b then w else 0"
  shows "tv_distance {False,True} (finite_softmax {False,True} s)
    (finite_softmax {False,True} (\<lambda>b. s b+r b))=tanh (w/4)"
proof -
  let ?t="exp (w/2)"
  let ?p="\<lambda>b::bool. if b then 1/(?t+1) else ?t/(?t+1)"
  let ?Y="\<lambda>b::bool. if b then ?t^2 else 1"
  have t: "1<?t" using w by simp
  have p: "finite_softmax {False,True} s=?p"
    by (rule ext; rename_tac b; case_tac b; simp add: finite_softmax_def s_def add.commute)
  have square: "?t^2=exp w" by (simp add: power2_eq_square exp_add[symmetric])
  have y: "(\<lambda>b. exp (r b-0))=?Y"
    by (rule ext; rename_tac b; case_tac b; simp add: r_def square)
  have tilt: "finite_softmax {False,True} (\<lambda>b. s b+r b)=finite_tilt {False,True} ?p ?Y"
  proof -
    have raw: "finite_softmax {False,True} (\<lambda>b. s b+r b)=
      finite_tilt {False,True} (finite_softmax {False,True} s) (\<lambda>b. exp (r b-0))"
      by (rule softmax_as_tilt; auto)
    show ?thesis using raw by (simp only: p y)
  qed
  have sharp: "tv_distance {False,True} ?p (finite_tilt {False,True} ?p ?Y)=(?t-1)/(?t+1)"
    by (rule sharp_binary_tilt(2)[OF t])
  have rate: "(?t-1)/(?t+1)=tanh (w/4)"
    using tanh_half_exp[where x="w/2"] by simp
  show ?thesis by (simp only: p tilt sharp rate)
qed

end
