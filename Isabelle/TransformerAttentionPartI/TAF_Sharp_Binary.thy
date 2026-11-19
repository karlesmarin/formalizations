(* Title: Binary witnesses attaining the finite transport bounds
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Sharp_Binary
  imports TAF_Transport
begin

lemma half_double_real:
  fixes r :: real
  shows "(r+r)/2=r"
  by simp

lemma sharp_binary_tilt:
  fixes t :: real
  assumes t: "1<t"
  defines "p \<equiv> \<lambda>b::bool. if b then 1/(t+1) else t/(t+1)"
    and "Y \<equiv> \<lambda>b::bool. if b then t^2 else 1"
  shows "finite_probability {False,True} p"
    "tv_distance {False,True} p (finite_tilt {False,True} p Y)=(t-1)/(t+1)"
proof -
  have tp: "0<t" and den: "0<t+1" using t by linarith+
  show "finite_probability {False,True} p"
    by (unfold_locales; use tp den in \<open>auto simp: p_def add_divide_distrib[symmetric]\<close>)
  have raw: "fw_mean {False,True} p Y=t/(t+1)+t^2/(t+1)"
    by (simp add: fw_mean_def p_def Y_def)
  have poly: "t+t^2=t*(t+1)" by (simp add: algebra_simps power2_eq_square)
  have ratmean: "t/(t+1)+t^2/(t+1)=t"
    using den by (simp only: add_divide_distrib[symmetric] poly; simp)
  have mean: "fw_mean {False,True} p Y=t" using raw ratmean by argo
  have q0: "finite_tilt {False,True} p Y False=1/(t+1)"
    using tp den by (simp only: finite_tilt_def mean; simp add: p_def Y_def)
  have q1: "finite_tilt {False,True} p Y True=t/(t+1)"
    using tp den by (simp only: finite_tilt_def mean; simp add: p_def Y_def power2_eq_square)
  have qfun: "finite_tilt {False,True} p Y=(\<lambda>b::bool. if b then t/(t+1) else 1/(t+1))"
  proof (rule ext)
    fix b show "finite_tilt {False,True} p Y b=(if b then t/(t+1) else 1/(t+1))"
      by (cases b; simp only: q0 q1 if_True if_False)
  qed
  have tm: "0\<le>t-1" using t by linarith
  have am: "abs (1-t)=t-1" using t by (auto simp: abs_if; linarith)
  have ac: "((t-1)/(t+1)+(t-1)/(t+1))/2=(t-1)/(t+1)" by (rule half_double_real)
  have da: "abs (p False-finite_tilt {False,True} p Y False)=(t-1)/(t+1)"
    by (simp only: q0; simp only: p_def if_False diff_divide_distrib[symmetric]
        abs_divide abs_of_nonneg[OF tm] abs_of_pos[OF den])
  have db: "abs (p True-finite_tilt {False,True} p Y True)=(t-1)/(t+1)"
    by (simp only: q1; simp only: p_def if_True diff_divide_distrib[symmetric]
        abs_divide am abs_of_pos[OF den])
  have tvraw: "tv_distance {False,True} p (finite_tilt {False,True} p Y) =
    (abs (p False-finite_tilt {False,True} p Y False)+abs (p True-finite_tilt {False,True} p Y True))/2"
    by (simp add: tv_distance_def)
  show "tv_distance {False,True} p (finite_tilt {False,True} p Y)=(t-1)/(t+1)"
    by (simp only: tvraw da db ac)
qed

lemma binary_output_sharp:
  fixes e M :: real
  assumes e: "0\<le>e" "e<1" and M: "0\<le>M"
  defines "p \<equiv> \<lambda>b::bool. if b then e else 1-e"
    and "v \<equiv> \<lambda>b::bool. if b then M else -M"
  shows "norm (vector_mean {False,True} p v-
    vector_mean {False,True} (cut_prob {False} p) v)=2*e*M"
proof -
  have ne: "1-e\<noteq>0" using e by linarith
  have id: "vector_mean {False,True} p v-
    vector_mean {False,True} (cut_prob {False} p) v=2*e*M"
    using ne by (simp add: vector_mean_def cut_prob_def p_def v_def algebra_simps)
  have nn: "0\<le>2*e*M" using e M by (intro mult_nonneg_nonneg; auto)
  show ?thesis using nn by (simp add: id)
qed

end
