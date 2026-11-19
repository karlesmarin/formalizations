(* Title: Finite quantiles increase with support size
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Power_Support
  imports TAF_Power_Family TAF_Softmax
begin

lemma quantile_support_order:
  assumes N: "1\<le>N" and NM: "N\<le>M" and fn: "fract\<le>F N" and gm: "fract\<le>G M"
    and order: "\<And>k. k\<in>{1..N} \<Longrightarrow> G k\<le>F k"
  shows "finite_quantile N F fract\<le>finite_quantile M G fract"
proof -
  let ?q = "finite_quantile M G fract"
  have M: "1\<le>M" using N NM by linarith
  have q: "?q\<in>{1..M}" and atq: "fract\<le>G ?q"
    using finite_quantile_valid[where N=M and F=G and f=fract, OF M gm] by auto
  show ?thesis
  proof (cases "?q\<le>N")
    case True
    have mem: "?q\<in>{1..N}" using q True by auto
    have f: "fract\<le>F ?q" using atq order[OF mem] by linarith
    have mem_set: "?q\<in>{k\<in>{1..N}. fract\<le>F k}" using mem f by auto
    have min_le: "Min {k\<in>{1..N}. fract\<le>F k}\<le>?q"
      by (rule Min_le) (use mem_set in auto)
    show ?thesis using min_le by (simp only: finite_quantile_def)
  next
    case False
    have "finite_quantile N F fract\<in>{1..N}"
      by (rule finite_quantile_valid(1)[where N=N and F=F and f=fract, OF N fn])
    then show ?thesis using False by auto
  qed
qed

context finite_power_family
begin

lemma cdf_ratio:
  assumes k: "k\<le>N"
  shows "cdf g k=(\<Sum>i\<in>{1..k}. exp (-g*ln (real i)))/
    (\<Sum>i\<in>{1..N}. exp (-g*ln (real i)))"
proof -
  have mn: "min N k=k" using k by simp
  have pt: "f.ep g i=exp (-g*ln (real i))/(\<Sum>j\<in>{1..N}. exp (-g*ln (real j)))" for i
    by (simp only: f.ep_def f.ew_def f.mom_def; simp)
  have efun: "f.ep g=(\<lambda>i. exp (-g*ln (real i))/(\<Sum>j\<in>{1..N}. exp (-g*ln (real j))))"
    by (rule ext; rule pt)
  show ?thesis by (simp only: cdf_def mn efun sum_divide_distrib[symmetric])
qed

end

lemma power_cdf_support_order:
  assumes N: "2\<le>N" and NM: "N\<le>M" and k: "k\<le>N"
  shows "finite_power_family.cdf M g k\<le>finite_power_family.cdf N g k"
proof -
  interpret n: finite_power_family N by (unfold_locales; rule N)
  have M: "2\<le>M" using N NM by linarith
  interpret m: finite_power_family M by (unfold_locales; rule M)
  let ?w = "\<lambda>i. exp (-g*ln (real i))"
  have sub: "{1..N}\<subseteq>{1..M}" using NM by auto
  have denorder: "sum ?w {1..N}\<le>sum ?w {1..M}"
    by (rule sum_mono2; use NM in auto)
  have np: "0<sum ?w {1..N}"
    by (rule exponential_sum_positive; use N in auto)
  have num: "0\<le>sum ?w {1..k}" by (intro sum_nonneg) simp
  have bound: "sum ?w {1..k}/sum ?w {1..M}\<le>sum ?w {1..k}/sum ?w {1..N}"
    by (rule frac_le[OF num order_refl np denorder])
  have km: "k\<le>M" using k NM by linarith
  show ?thesis by (simp only: n.cdf_ratio[OF k] m.cdf_ratio[OF km]) (rule bound)
qed

lemma power_quantile_support_order:
  assumes N: "2\<le>N" and NM: "N\<le>M" and fract: "fract\<le>1"
  shows "finite_power_family.quantile N g fract\<le>finite_power_family.quantile M g fract"
proof -
  interpret n: finite_power_family N by (unfold_locales; rule N)
  have M: "2\<le>M" using N NM by linarith
  interpret m: finite_power_family M by (unfold_locales; rule M)
  show ?thesis unfolding n.quantile_def m.quantile_def
    by (rule quantile_support_order[where N=N and M=M];
        use N NM fract n.cdf_end m.cdf_end power_cdf_support_order[OF N NM] in auto)
qed

end
