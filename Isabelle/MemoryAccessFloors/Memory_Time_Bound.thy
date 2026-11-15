(*  Title:      Memory_Time_Bound.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Corollary cor:time of paper A (memory floors).  The write infidelity of a pulse is r = (1-p)/6 + (1-c)/3, where
    p is the transferred population and c the coherence.  If every pulse of duration T has p <= Bp T and c <= Bc T,
    then r >= r_time = 1/2 - S/6 with S = sup_{T>=0} (Bp T + 2 Bc T).  If the sup is attained at T0 where the
    resonant pulse has pres T0 = Bp T0 and cres T0 = Bc T0 (or approached along T_n with the gap tending to 0),
    the resonant pulse reaches r_time (in the limit).
    Only this algebra over abstract bounds Bp, Bc is formalised; Bp, Bc themselves (Corollary cor:fixed) are not.
*)

theory Memory_Time_Bound
  imports "HOL-Analysis.Analysis"
begin

(* Copied from Isabelle/MemoryAccessFloors/Memory_Access_Floors.thy (our repository), lemma write_channel_monotone;
   the cola build cannot import that session. *)
lemma write_channel_monotone:
  fixes p c P C :: real
  assumes "p \<le> P" and "c \<le> C"
  shows "(1 - P) / 6 + (1 - C) / 3 \<le> (1 - p) / 6 + (1 - c) / 3"
  using assms by argo

definition infidelity :: "real \<Rightarrow> real \<Rightarrow> real" where
  "infidelity p c = (1 - p) / 6 + (1 - c) / 3"

definition Ssup :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "Ssup Bp Bc = Sup {Bp T + 2 * Bc T | T. 0 \<le> T}"

definition r_time :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "r_time Bp Bc = 1 / 2 - Ssup Bp Bc / 6"

(* 1. Pointwise bound. *)
lemma time_pointwise:
  fixes p c :: real and Bp Bc :: "real \<Rightarrow> real"
  assumes "p \<le> Bp T" and "c \<le> Bc T"
  shows "1 / 2 - (Bp T + 2 * Bc T) / 6 \<le> (1 - p) / 6 + (1 - c) / 3"
  using write_channel_monotone[where p = p and c = c and P = "Bp T" and C = "Bc T"] assms
  by argo

(* 2. The bound with the supremum, for any pulse of a set of pulses. *)
lemma time_bound:
  fixes Bp Bc :: "real \<Rightarrow> real" and dur pp cc :: "'a \<Rightarrow> real"
  assumes bdd: "bdd_above {Bp T + 2 * Bc T | T. 0 \<le> T}"
    and pulses: "\<And>x. 0 \<le> dur x \<and> pp x \<le> Bp (dur x) \<and> cc x \<le> Bc (dur x)"
  shows "r_time Bp Bc \<le> infidelity (pp x) (cc x)"
proof -
  have mem: "Bp (dur x) + 2 * Bc (dur x) \<in> {Bp T + 2 * Bc T | T. 0 \<le> T}"
    using pulses[where x = x] by blast
  have le: "Bp (dur x) + 2 * Bc (dur x) \<le> Ssup Bp Bc"
    unfolding Ssup_def using cSup_upper[OF mem bdd] .
  have pt: "1 / 2 - (Bp (dur x) + 2 * Bc (dur x)) / 6 \<le> (1 - pp x) / 6 + (1 - cc x) / 3"
    using time_pointwise[where p = "pp x" and c = "cc x" and Bp = Bp and Bc = Bc and T = "dur x"] pulses[where x = x]
    by blast
  show ?thesis
    unfolding r_time_def infidelity_def using le pt by argo
qed

(* 3. Equality case: the sup is attained at T0 and the resonant values equal the bounds. *)
lemma time_equality:
  fixes Bp Bc pres cres :: "real \<Rightarrow> real"
  assumes bdd: "bdd_above {Bp T + 2 * Bc T | T. 0 \<le> T}"
    and T0: "0 \<le> T0"
    and att: "Ssup Bp Bc = Bp T0 + 2 * Bc T0"
    and p0: "pres T0 = Bp T0" and c0: "cres T0 = Bc T0"
  shows "infidelity (pres T0) (cres T0) = r_time Bp Bc"
  unfolding infidelity_def r_time_def att p0 c0 by (simp add: field_simps)

(* 4. Limit case. *)
lemma time_limit:
  fixes Bp Bc pres cres :: "real \<Rightarrow> real" and T :: "nat \<Rightarrow> real"
  assumes gap: "(\<lambda>n. (Bp (T n) - pres (T n)) + 2 * (Bc (T n) - cres (T n))) \<longlonglongrightarrow> 0"
    and approach: "(\<lambda>n. Bp (T n) + 2 * Bc (T n)) \<longlonglongrightarrow> Ssup Bp Bc"
  shows "(\<lambda>n. infidelity (pres (T n)) (cres (T n))) \<longlonglongrightarrow> r_time Bp Bc"
proof -
  have eq: "\<And>n. infidelity (pres (T n)) (cres (T n)) =
      1 / 2 - ((Bp (T n) + 2 * Bc (T n)) -
               ((Bp (T n) - pres (T n)) + 2 * (Bc (T n) - cres (T n)))) / 6"
    unfolding infidelity_def by (simp add: field_simps)
  have "(\<lambda>n. 1 / 2 - ((Bp (T n) + 2 * Bc (T n)) -
               ((Bp (T n) - pres (T n)) + 2 * (Bc (T n) - cres (T n)))) / 6)
        \<longlonglongrightarrow> 1 / 2 - (Ssup Bp Bc - 0) / 6"
    by (intro tendsto_intros approach gap) simp
  then show ?thesis
    unfolding r_time_def using eq by simp
qed

end
