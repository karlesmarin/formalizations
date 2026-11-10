(*  Title:      Game_of_Life/Life_Fast.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Fast
  imports Life_Base
begin

section \<open>A faster executable step on sorted lists\<close>

text \<open>
  \<open>sim_step\<close> of \<open>Life_Base\<close> is quadratic (\<open>remdups\<close> and list membership).  Here a generation is
  a list sorted strictly in the lexicographic order of \<open>int \<times> int\<close>.  The neighbour multiset is
  obtained by merging the eight translated copies of the list (each one sorted), its run-length
  encoding gives the neighbour counts, and the next generation is read off the runs.

  Correctness does not rely on proving that the lists are sorted: \<open>fast_step\<close> checks
  (linearly) that the input and the run heads are strictly increasing, and otherwise uses
  \<open>sim_step\<close>.  Sortedness only matters for speed.
\<close>

definition clt :: "cell \<Rightarrow> cell \<Rightarrow> bool" where
  "clt a b \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a < snd b)"

definition cle :: "cell \<Rightarrow> cell \<Rightarrow> bool" where
  "cle a b \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a \<le> snd b)"

fun asc :: "cell list \<Rightarrow> bool" where
  "asc (x # y # zs) = (clt x y \<and> asc (y # zs))"
| "asc _ = True"

lemma clt_trans: "clt a b \<Longrightarrow> clt b c \<Longrightarrow> clt a c"
  by (auto simp: clt_def)

lemma asc_Cons_all: "asc (x # xs) \<Longrightarrow> y \<in> set xs \<Longrightarrow> clt x y"
proof (induction xs arbitrary: x)
  case (Cons z zs)
  have xz: "clt x z" and a: "asc (z # zs)" using Cons.prems(1) by simp_all
  show ?case
  proof (cases "y = z")
    case True
    then show ?thesis using xz by simp
  next
    case False
    then have "y \<in> set zs" using Cons.prems(2) by simp
    then have "clt z y" using Cons.IH[OF a] by blast
    then show ?thesis using xz clt_trans by blast
  qed
qed simp

lemma asc_distinct: "asc xs \<Longrightarrow> distinct xs"
proof (induction xs)
  case (Cons x xs)
  have "asc xs" using Cons.prems by (cases xs) auto
  moreover have "x \<notin> set xs"
  proof
    assume "x \<in> set xs"
    then have "clt x x" by (rule asc_Cons_all[OF Cons.prems])
    then show False by (simp add: clt_def)
  qed
  ultimately show ?case using Cons.IH by simp
qed simp

subsection \<open>Merging and counting\<close>

fun merge :: "cell list \<Rightarrow> cell list \<Rightarrow> cell list" where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x # xs) (y # ys) = (if cle x y then x # merge xs (y # ys) else y # merge (x # xs) ys)"

lemma count_merge: "count_list (merge xs ys) c = count_list xs c + count_list ys c"
  by (induction xs ys rule: merge.induct) auto

definition nb :: "cell list \<Rightarrow> cell list" where
  "nb xs = foldr (\<lambda>v acc. merge (map (tr v) xs) acc) moore []"

lemma count_foldr_merge:
  "count_list (foldr (\<lambda>v acc. merge (map (tr v) xs) acc) vs []) c
     = sum_list (map (\<lambda>v. count_list (map (tr v) xs) c) vs)"
  by (induction vs) (simp_all add: count_merge)

lemma count_list_distinct: "distinct ys \<Longrightarrow> count_list ys c = (if c \<in> set ys then 1 else 0)"
  by (induction ys) auto

definition neg :: "cell \<Rightarrow> cell" where "neg v = (- fst v, - snd v)"

lemma count_map_tr:
  assumes "distinct xs"
  shows "count_list (map (tr v) xs) c = (if tr (neg v) c \<in> set xs then 1 else 0)"
proof -
  have "inj (tr v)" using bij_tr bij_is_inj by blast
  then have "inj_on (tr v) (set xs)" by (rule inj_on_subset) simp
  then have "distinct (map (tr v) xs)" using assms by (simp add: distinct_map)
  moreover have a: "tr v (tr (neg v) c) = c" "\<And>x. tr (neg v) (tr v x) = x"
    by (simp_all add: tr_def neg_def)
  have "c \<in> tr v ` set xs \<longleftrightarrow> tr (neg v) c \<in> set xs"
    by (metis a imageE imageI)
  ultimately show ?thesis by (simp add: count_list_distinct)
qed

lemma map_neg_moore: "map neg moore = rev moore"
  by (simp add: moore_def neg_def)

lemma length_filter_sum: "length (filter P ys) = sum_list (map (\<lambda>y. if P y then 1 else 0) ys)"
  by (induction ys) auto

lemma count_nb:
  assumes "distinct xs"
  shows "count_list (nb xs) c = nbrs (set xs) c"
proof -
  have "count_list (nb xs) c = sum_list (map (\<lambda>v. if tr (neg v) c \<in> set xs then 1 else 0) moore)"
    unfolding nb_def count_foldr_merge using count_map_tr[OF assms] by simp
  also have "\<dots> = sum_list (map (\<lambda>w. if tr w c \<in> set xs then 1 else 0) (map neg moore))"
    by (simp add: comp_def)
  also have "\<dots> = sum_list (map (\<lambda>w. if tr w c \<in> set xs then 1 else 0) moore)"
    by (simp add: map_neg_moore rev_map[symmetric] sum_list_rev)
  also have "\<dots> = cnt xs c"
    by (simp add: cnt_def nbhd_list_def length_filter_sum comp_def)
  finally show ?thesis by (simp add: cnt_correct)
qed

lemma set_nb: "set (nb xs) = \<Union> (nbhd ` set xs)"
proof -
  have "c \<in> set (nb xs) \<longleftrightarrow> c \<in> \<Union> (nbhd ` set xs)" for c
  proof -
    have "c \<in> set (nb xs) \<longleftrightarrow> count_list (nb xs) c \<noteq> 0"
      by (simp add: count_list_0_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>v\<in>set moore. count_list (map (tr v) xs) c \<noteq> 0)"
      unfolding nb_def count_foldr_merge by (simp add: sum_list_eq_0_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>v\<in>set moore. c \<in> tr v ` set xs)"
      by (simp add: count_list_0_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>x\<in>set xs. c \<in> set (nbhd_list x))"
      by (auto simp: nbhd_list_def)
    finally show ?thesis by (simp add: set_nbhd_list)
  qed
  then show ?thesis by blast
qed

subsection \<open>Run-length encoding\<close>

fun rle :: "cell list \<Rightarrow> (cell \<times> nat) list" where
  "rle [] = []"
| "rle (x # xs) = (case rle xs of
       [] \<Rightarrow> [(x, 1)]
     | (y, k) # r \<Rightarrow> (if x = y then (y, Suc k) # r else (x, 1) # (y, k) # r))"

lemma fst_rle: "fst ` set (rle xs) = set xs"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "rle xs = []")
    case True
    then have "xs = []" using Cons.IH by auto
    then show ?thesis by simp
  next
    case False
    then obtain y j r where e: "rle xs = (y, j) # r" by (metis list.exhaust prod.exhaust)
    then show ?thesis using Cons.IH by (auto split: if_splits)
  qed
qed simp

lemma rle_count:
  "distinct (map fst (rle xs)) \<Longrightarrow> (c, k) \<in> set (rle xs) \<Longrightarrow> k = count_list xs c"
proof (induction xs arbitrary: c k)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "rle xs = []")
    case True
    then have "xs = []" using fst_rle[of xs] by auto
    then show ?thesis using Cons.prems by simp
  next
    case False
    then obtain y j r where Cons2: "rle xs = (y, j) # r" by (metis list.exhaust prod.exhaust)
    show ?thesis
    proof (cases "x = y")
      case True
      have d: "distinct (map fst (rle xs))" using Cons.prems(1) Cons2 True by simp
      have yj: "j = count_list xs y" using Cons.IH[OF d] Cons2 by simp
      have r: "(z, i) \<in> set r \<Longrightarrow> z \<noteq> y \<and> i = count_list xs z" for z i
        using Cons.prems(1) Cons.IH[OF d, of z i] d Cons2 by force
      have "rle (x # xs) = (y, Suc j) # r" using Cons2 True by simp
      then have "(c, k) = (y, Suc j) \<or> (c, k) \<in> set r" using Cons.prems(2) by simp
      then show ?thesis
      proof
        assume "(c, k) = (y, Suc j)"
        then show ?thesis using yj True by simp
      next
        assume "(c, k) \<in> set r"
        then have "c \<noteq> y" "k = count_list xs c" using r[of c k] by blast+
        then show ?thesis using True by simp
      qed
    next
      case False
      have d: "distinct (map fst (rle xs))" using Cons.prems(1) Cons2 False by simp
      have "x \<notin> fst ` set (rle xs)" using Cons.prems(1) Cons2 False by simp
      then have x0: "count_list xs x = 0" by (simp add: fst_rle count_list_0_iff)
      have o: "(z, i) \<in> set (rle xs) \<Longrightarrow> z \<noteq> x \<and> i = count_list xs z" for z i
        using Cons.IH[OF d, of z i] \<open>x \<notin> fst ` set (rle xs)\<close> by force
      have "rle (x # xs) = (x, 1) # rle xs" using Cons2 False by simp
      then have "(c, k) = (x, 1) \<or> (c, k) \<in> set (rle xs)" using Cons.prems(2) by simp
      then show ?thesis
      proof
        assume "(c, k) = (x, 1)"
        then show ?thesis using x0 by simp
      next
        assume "(c, k) \<in> set (rle xs)"
        then have "c \<noteq> x" "k = count_list xs c" using o[of c k] by blast+
        then show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The fast step\<close>

definition step_runs :: "cell list \<Rightarrow> (cell \<times> nat) list \<Rightarrow> cell list" where
  "step_runs xs rs = map fst (filter (\<lambda>p. snd p = 3 \<or> (snd p = 2 \<and> fst p \<in> set xs)) rs)"

definition fast_step :: "cell list \<Rightarrow> cell list" where
  "fast_step xs = (let rs = rle (nb xs) in
     if asc xs \<and> asc (map fst rs) then step_runs xs rs else sim_step xs)"

lemma step_runs_correct:
  assumes "distinct xs" "distinct (map fst (rle (nb xs)))"
  shows "set (step_runs xs (rle (nb xs))) = step (set xs)"
proof (intro set_eqI)
  fix c
  have cnt: "(c, k) \<in> set (rle (nb xs)) \<Longrightarrow> k = nbrs (set xs) c" for k
    using rle_count[OF assms(2)] count_nb[OF assms(1)] by simp
  have ex: "c \<in> set (nb xs) \<longleftrightarrow> (\<exists>k. (c, k) \<in> set (rle (nb xs)))"
    unfolding fst_rle[of "nb xs", symmetric] by force
  have pos: "c \<notin> set (nb xs) \<Longrightarrow> nbrs (set xs) c = 0"
    using count_nb[OF assms(1), of c] by (simp add: count_list_0_iff)
  show "c \<in> set (step_runs xs (rle (nb xs))) \<longleftrightarrow> c \<in> step (set xs)"
  proof (cases "c \<in> set (nb xs)")
    case True
    then obtain k where k: "(c, k) \<in> set (rle (nb xs))" using ex by blast
    then have kk: "k = nbrs (set xs) c" by (rule cnt)
    have "c \<in> set (step_runs xs (rle (nb xs))) \<longleftrightarrow> k = 3 \<or> (k = 2 \<and> c \<in> set xs)"
    proof
      assume "c \<in> set (step_runs xs (rle (nb xs)))"
      then obtain k' where "(c, k') \<in> set (rle (nb xs))" "k' = 3 \<or> (k' = 2 \<and> c \<in> set xs)"
        by (auto simp: step_runs_def)
      then show "k = 3 \<or> (k = 2 \<and> c \<in> set xs)" using cnt kk by metis
    next
      assume "k = 3 \<or> (k = 2 \<and> c \<in> set xs)"
      then show "c \<in> set (step_runs xs (rle (nb xs)))"
        using k by (force simp: step_runs_def)
    qed
    then show ?thesis using kk by (auto simp: mem_step)
  next
    case False
    then have "c \<notin> set (step_runs xs (rle (nb xs)))"
      using ex by (auto simp: step_runs_def)
    then show ?thesis using pos[OF False] by (simp add: mem_step)
  qed
qed

theorem fast_step_correct: "set (fast_step xs) = step (set xs)"
proof (cases "asc xs \<and> asc (map fst (rle (nb xs)))")
  case True
  then have "distinct xs" "distinct (map fst (rle (nb xs)))" by (simp_all add: asc_distinct)
  moreover have "fast_step xs = step_runs xs (rle (nb xs))"
    unfolding fast_step_def Let_def using True by (rule if_P)
  ultimately show ?thesis by (simp add: step_runs_correct)
next
  case False
  have "fast_step xs = sim_step xs"
    unfolding fast_step_def Let_def using False by (rule if_not_P)
  then show ?thesis by (simp add: sim_step_correct)
qed

text \<open>Trace replay with the fast step; the proposed generations must be given exactly (as the
  sorted lists \<open>fast_step\<close> produces), which makes the comparison linear.\<close>

fun trace_ok2 :: "cell list \<Rightarrow> cell list list \<Rightarrow> bool" where
  "trace_ok2 xs [] = True"
| "trace_ok2 xs (ys # yss) = (fast_step xs = ys \<and> trace_ok2 ys yss)"

theorem trace_ok2_correct:
  "trace_ok2 xs yss \<Longrightarrow> (step ^^ length yss) (set xs) = set (last (xs # yss))"
proof (induction yss arbitrary: xs)
  case (Cons ys yss)
  then have "step (set xs) = set ys" "(step ^^ length yss) (set ys) = set (last (ys # yss))"
    using fast_step_correct by auto
  then show ?case by (simp add: funpow_Suc_right del: funpow.simps)
qed simp

end
