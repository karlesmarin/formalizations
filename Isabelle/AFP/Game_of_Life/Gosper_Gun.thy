(*  Title:      Game_of_Life/Gosper_Gun.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Gosper_Gun
  imports Life_Flight Gosper_Gun_Cert
begin

section \<open>The Gosper glider gun and unbounded population\<close>

text \<open>
  \<open>gun\<close> is the 36-cell Gosper gun; after 30 generations it is again \<open>gun\<close> together with a new
  south-east glider \<open>egl\<close> (cells \<open>(23,9)\<close>, \<open>(23,11)\<close>, \<open>(24,10)\<close>, \<open>(24,11)\<close>, \<open>(25,10)\<close>; \<open>x\<close> the
  column, \<open>y\<close> the row, downwards).  The glider emitted \<open>j\<close> periods earlier is
  \<open>gl j\<close>, the emitted glider after \<open>30 j\<close> generations, and after \<open>30 k\<close> generations the configuration is exactly
  \<open>gun \<union> \<Union>j<k. gl j\<close>.  Separation: every generation of \<open>egl\<close> lies in a 4 by 4 box that moves one cell diagonally every 4
    generations, so two gliders emitted at least one period apart stay in boxes whose
    \<open>x\<close>-offsets differ by at least 7 (\<open>gliders_apart\<close>).  During a period the gun stays in rows \<open>y \<le> 11\<close>, while every older glider is in rows
    \<open>y \<ge> 16\<close> (\<open>gun_old_apart\<close>); the newest glider is checked against the gun generation by
    generation (\<open>gun_egl_apart\<close>).
\<close>

definition gun :: gen where "gun = set gun_l"
definition egl :: gen where "egl = set e_l"
definition gl :: "nat \<Rightarrow> gen" where "gl j = (step ^^ (30 * j)) egl"
definition emitted :: "nat \<Rightarrow> gen" where "emitted k = (\<Union>j<k. gl j)"

subsection \<open>Trace facts\<close>

lemma trace_ok2_nth:
  "trace_ok2 xs yss \<Longrightarrow> k \<le> length yss \<Longrightarrow> (step ^^ k) (set xs) = set ((xs # yss) ! k)"
proof (induction yss arbitrary: xs k)
  case Nil
  then show ?case by simp
next
  case (Cons ys yss)
  then have s: "step (set xs) = set ys" and t: "trace_ok2 ys yss"
    using fast_step_correct by auto
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    then have "j \<le> length yss" using Cons.prems by simp
    then have "(step ^^ j) (set ys) = set ((ys # yss) ! j)" using Cons.IH[OF t] by blast
    then show ?thesis using s Suc by (simp add: funpow_Suc_right del: funpow.simps)
  qed
qed

lemma gun_state: "i \<le> 30 \<Longrightarrow> (step ^^ i) gun = set ((gun_l # gun_trace) ! i)"
  using trace_ok2_nth[OF gun_trace_ok, of i] len_gun_trace by (simp add: gun_def)

lemma egl_state: "i \<le> 29 \<Longrightarrow> (step ^^ i) egl = set ((e_l # e_trace) ! i)"
  using trace_ok2_nth[OF e_trace_ok, of i] len_e_trace by (simp add: egl_def)

theorem gun_period: "(step ^^ 30) gun = gun \<union> egl"
proof -
  have "(step ^^ 30) gun = set ((gun_l # gun_trace) ! 30)" by (rule gun_state) simp
  also have "\<dots> = set (gun_l @ e_l)" using gun_last by (simp only: same_set_correct)
  finally show ?thesis by (simp add: gun_def egl_def)
qed

theorem egl_moves: "(step ^^ 4) egl = transl (1, 1) egl"
proof -
  have "(step ^^ 4) egl = set ((e_l # e_trace) ! 4)" by (rule egl_state) simp
  also have "\<dots> = set (map (tr (1, 1)) e_l)" using e_moves_ok by (simp only: same_set_correct)
  finally show ?thesis by (simp add: egl_def transl_set)
qed

subsection \<open>Free flight of the emitted glider\<close>

lemma egl_decomp:
  "(step ^^ n) egl = transl (int (n div 4), int (n div 4)) ((step ^^ (n mod 4)) egl)"
proof -
  have "(step ^^ n) egl = (step ^^ (n mod 4)) ((step ^^ (4 * (n div 4))) egl)"
    by (metis comp_apply funpow_add mod_mult_div_eq)
  also have "(step ^^ (4 * (n div 4))) egl = transl (int (n div 4), int (n div 4)) egl"
    using flight_mult[OF egl_moves, of "n div 4"] by simp
  finally show ?thesis by (simp add: steps_transl)
qed

definition box :: "cell \<Rightarrow> gen" where
  "box q = {c. fst q \<le> fst c \<and> fst c \<le> fst q + 3 \<and> snd q \<le> snd c \<and> snd c \<le> snd q + 3}"

lemma in_box_correct: "in_box q xs \<Longrightarrow> set xs \<subseteq> box q"
  by (auto simp: in_box_def box_def list_all_iff)

lemma transl_box: "transl v (box q) \<subseteq> box (tr v q)"
  by (auto simp: transl_def box_def tr_def)

lemma transl_mono: "A \<subseteq> B \<Longrightarrow> transl v A \<subseteq> transl v B"
  by (auto simp: transl_def)

lemma list_all_take_nth:
  assumes "list_all P (take n xs)" "i < n" "i < length xs"
  shows "P (xs ! i)"
proof -
  have "i < length (take n xs)" using assms(2,3) by simp
  then have "P (take n xs ! i)" using assms(1) by (simp add: list_all_length)
  then show ?thesis using assms(2) by simp
qed

lemma egl_phase_box:
  assumes "b < 4"
  shows "(step ^^ b) egl \<subseteq> box q0"
proof -
  have "in_box q0 ((e_l # e_trace) ! b)"
    using list_all_take_nth[OF e_box_ok assms] assms len_e_trace by simp
  then show ?thesis using egl_state[of b] assms in_box_correct by simp
qed

lemma egl_box: "(step ^^ n) egl \<subseteq> box (tr (int (n div 4), int (n div 4)) q0)"
proof -
  have "(step ^^ n) egl \<subseteq> transl (int (n div 4), int (n div 4)) (box q0)"
    unfolding egl_decomp[of n] by (rule transl_mono[OF egl_phase_box]) simp
  then show ?thesis using transl_box by blast
qed

lemma card_transl: "card (transl v A) = card A"
proof -
  have "inj_on (tr v) A" using bij_is_inj[OF bij_tr] by (rule inj_on_subset) simp
  then show ?thesis by (simp add: transl_def card_image)
qed

lemma card_egl_steps: "card ((step ^^ n) egl) = 5"
proof -
  have b: "n mod 4 < 4" by simp
  have "distinct ((e_l # e_trace) ! (n mod 4)) \<and> length ((e_l # e_trace) ! (n mod 4)) = 5"
    using list_all_take_nth[OF e_card_ok b] b len_e_trace by simp
  then have "card ((step ^^ (n mod 4)) egl) = 5"
    using egl_state[of "n mod 4"] b by (simp add: distinct_card)
  then show ?thesis by (simp add: egl_decomp[of n] card_transl)
qed

subsection \<open>Separation\<close>

lemma box_apart_x:
  assumes "fst p + 6 \<le> fst p'"
  shows "dil 1 (box p) \<inter> dil 1 (box p') = {}"
proof -
  have "fst d \<le> fst p + 4" if "d \<in> dil 1 (box p)" for d
    using that by (auto simp: dil_def box_def abs_le_iff)
  moreover have "fst p' - 1 \<le> fst d" if "d \<in> dil 1 (box p')" for d
    using that by (auto simp: dil_def box_def abs_le_iff)
  ultimately show ?thesis using assms by fastforce
qed

lemma div_shift:
  fixes i j j' :: nat
  assumes "j < j'"
  shows "(i + 30 * j) div 4 + 7 \<le> (i + 30 * j') div 4"
proof -
  have "i + 30 * j + 7 * 4 \<le> i + 30 * j'" using assms by linarith
  then have "(i + 30 * j + 7 * 4) div 4 \<le> (i + 30 * j') div 4" by (rule div_le_mono)
  moreover have "(i + 30 * j + 7 * 4) div 4 = 7 + (i + 30 * j) div 4" by (rule div_mult_self1) simp
  ultimately show ?thesis by simp
qed

lemma steps_gl: "(step ^^ i) (gl j) = (step ^^ (i + 30 * j)) egl"
  by (simp add: gl_def funpow_add)

lemma gl_box:
  "(step ^^ i) (gl j) \<subseteq> box (tr (int ((i + 30 * j) div 4), int ((i + 30 * j) div 4)) q0)"
  using egl_box[of "i + 30 * j"] by (simp add: steps_gl)

theorem gliders_apart:
  assumes "j < j'"
  shows "dil 1 ((step ^^ i) (gl j)) \<inter> dil 1 ((step ^^ i) (gl j')) = {}"
proof -
  define a where "a = (i + 30 * j) div 4"
  define b where "b = (i + 30 * j') div 4"
  have "a + 7 \<le> b" unfolding a_def b_def using assms by (rule div_shift)
  then have "int (a + 6) \<le> int b" by simp
  then have "fst (tr (int a, int a) q0) + 6 \<le> fst (tr (int b, int b) q0)" by (simp add: tr_def)
  then have "dil 1 (box (tr (int a, int a) q0)) \<inter> dil 1 (box (tr (int b, int b) q0)) = {}"
    by (rule box_apart_x)
  moreover have "dil 1 ((step ^^ i) (gl j)) \<subseteq> dil 1 (box (tr (int a, int a) q0))"
    unfolding a_def by (rule dil_mono[OF gl_box])
  moreover have "dil 1 ((step ^^ i) (gl j')) \<subseteq> dil 1 (box (tr (int b, int b) q0))"
    unfolding b_def by (rule dil_mono[OF gl_box])
  ultimately show ?thesis by blast
qed

theorem stream: "(step ^^ m) (emitted k) = (\<Union>j<k. (step ^^ m) (gl j))"
proof (induction k arbitrary: m)
  case 0
  then show ?case by (simp add: emitted_def)
next
  case (Suc k)
  have E: "emitted (Suc k) = gl k \<union> emitted k"
    by (simp add: emitted_def lessThan_Suc)
  have "\<forall>i<m. dil 1 ((step ^^ i) (gl k)) \<inter> dil 1 ((step ^^ i) (emitted k)) = {}"
  proof (intro allI impI)
    fix i assume "i < m"
    have "dil 1 ((step ^^ i) (emitted k)) = (\<Union>j<k. dil 1 ((step ^^ i) (gl j)))"
      by (simp only: Suc.IH dil_UN)
    moreover have "dil 1 ((step ^^ i) (gl j)) \<inter> dil 1 ((step ^^ i) (gl k)) = {}" if "j < k" for j
      by (rule gliders_apart[OF that])
    ultimately show "dil 1 ((step ^^ i) (gl k)) \<inter> dil 1 ((step ^^ i) (emitted k)) = {}"
      by blast
  qed
  then have "(step ^^ m) (gl k \<union> emitted k) = (step ^^ m) (gl k) \<union> (step ^^ m) (emitted k)"
    by (rule disjoint_steps)
  then show ?case by (simp add: E Suc.IH lessThan_Suc)
qed

lemma dil1_below: "A \<subseteq> {c. snd c \<le> Y} \<Longrightarrow> dil 1 A \<subseteq> {c. snd c \<le> Y + 1}"
proof
  fix d assume A: "A \<subseteq> {c. snd c \<le> Y}" and "d \<in> dil 1 A"
  then obtain c where "c \<in> A" "\<bar>snd d - snd c\<bar> \<le> int 1" unfolding dil_def by blast
  then show "d \<in> {c. snd c \<le> Y + 1}" using A by (auto simp: abs_le_iff)
qed

lemma dil1_box_above: "dil 1 (box p) \<subseteq> {c. snd p - 1 \<le> snd c}"
proof
  fix d assume "d \<in> dil 1 (box p)"
  then obtain c where "c \<in> box p" "\<bar>snd d - snd c\<bar> \<le> int 1" unfolding dil_def by blast
  then show "d \<in> {c. snd p - 1 \<le> snd c}" by (auto simp: box_def abs_le_iff)
qed

lemma gun_low: "i < 30 \<Longrightarrow> (step ^^ i) gun \<subseteq> {c. snd c \<le> ymax}"
proof -
  assume i: "i < 30"
  have "list_all (\<lambda>c. snd c \<le> ymax) ((gun_l # gun_trace) ! i)"
    using list_all_take_nth[OF gun_low_ok i] i len_gun_trace by simp
  then show ?thesis using gun_state[of i] i by (auto simp: list_all_iff)
qed

theorem gun_egl_apart: "i < 30 \<Longrightarrow> dil 1 ((step ^^ i) gun) \<inter> dil 1 ((step ^^ i) egl) = {}"
proof -
  assume i: "i < 30"
  have l: "i < length (take 30 (gun_l # gun_trace))" using i len_gun_trace by simp
  have "far 1 (take 30 (gun_l # gun_trace) ! i) ((e_l # e_trace) ! i)"
    by (rule list_all2_nthD[OF gun_far_ok l])
  then have "far 1 ((gun_l # gun_trace) ! i) ((e_l # e_trace) ! i)" using i by (simp only: nth_take)
  from far_correct[OF this] show ?thesis using gun_state[of i] egl_state[of i] i by simp
qed

theorem gun_old_apart:
  assumes "i < 30" "0 < j"
  shows "dil 1 ((step ^^ i) gun) \<inter> dil 1 ((step ^^ i) (gl j)) = {}"
proof -
  define a where "a = (i + 30 * j) div 4"
  have "(30::nat) div 4 \<le> (i + 30 * j) div 4" using assms(2) by (intro div_le_mono) linarith
  then have a7: "7 \<le> a" by (simp add: a_def)
  have "dil 1 ((step ^^ i) gun) \<subseteq> {c. snd c \<le> ymax + 1}"
    by (rule dil1_below[OF gun_low[OF assms(1)]])
  moreover have "dil 1 ((step ^^ i) (gl j)) \<subseteq> {c. snd (tr (int a, int a) q0) - 1 \<le> snd c}"
    using dil_mono[OF gl_box[of i j]] dil1_box_above unfolding a_def by blast
  moreover have "ymax + 1 < snd (tr (int a, int a) q0) - 1"
    using ymax_sep a7 by (simp add: tr_def)
  ultimately show ?thesis by fastforce
qed

theorem gun_emitted_apart:
  "i < 30 \<Longrightarrow> dil 1 ((step ^^ i) gun) \<inter> dil 1 ((step ^^ i) (emitted k)) = {}"
proof -
  assume i: "i < 30"
  have "dil 1 ((step ^^ i) gun) \<inter> dil 1 ((step ^^ i) (gl j)) = {}" for j
  proof (cases j)
    case 0
    then show ?thesis using gun_egl_apart[OF i] by (simp add: gl_def)
  next
    case (Suc j')
    then show ?thesis using gun_old_apart[OF i] by simp
  qed
  then show ?thesis by (simp only: stream dil_UN) blast
qed

subsection \<open>The gun\<close>

lemma gl_Suc: "(step ^^ 30) (gl j) = gl (Suc j)"
  by (simp only: gl_def mult_Suc_right funpow_add comp_apply)

lemma emitted_Suc: "emitted (Suc k) = egl \<union> (\<Union>j<k. gl (Suc j))"
  unfolding emitted_def lessThan_Suc_eq_insert_0 by (auto simp: gl_def)

theorem gun_stream: "(step ^^ (30 * k)) gun = gun \<union> emitted k"
proof (induction k)
  case 0
  then show ?case by (simp add: emitted_def)
next
  case (Suc k)
  have "(step ^^ (30 * Suc k)) gun = (step ^^ 30) ((step ^^ (30 * k)) gun)"
    by (simp only: mult_Suc_right funpow_add comp_apply)
  also have "\<dots> = (step ^^ 30) (gun \<union> emitted k)"
    by (simp only: Suc.IH)
  also have "\<dots> = (step ^^ 30) gun \<union> (step ^^ 30) (emitted k)"
  proof (rule disjoint_steps, intro allI impI)
    fix i assume "i < (30::nat)"
    then show "dil 1 ((step ^^ i) gun) \<inter> dil 1 ((step ^^ i) (emitted k)) = {}"
      by (rule gun_emitted_apart)
  qed
  also have "\<dots> = gun \<union> egl \<union> (\<Union>j<k. gl (Suc j))"
    by (simp only: gun_period stream gl_Suc)
  also have "\<dots> = gun \<union> emitted (Suc k)"
    by (simp only: emitted_Suc Un_assoc)
  finally show ?case .
qed

subsection \<open>Population\<close>

lemma finite_gun: "finite gun"
  by (simp add: gun_def)

lemma finite_egl_steps: "finite ((step ^^ n) egl)"
  by (rule finite_steps) (simp add: egl_def)

lemma card_gl_stream: "card (\<Union>j<k. (step ^^ m) (gl j)) = 5 * k"
proof -
  have disj: "(step ^^ m) (gl j) \<inter> (step ^^ m) (gl j') = {}" if "j \<noteq> j'" for j j'
  proof -
    have "dil 1 ((step ^^ m) (gl j)) \<inter> dil 1 ((step ^^ m) (gl j')) = {}"
      using that gliders_apart[of j j' m] gliders_apart[of j' j m] by (cases "j < j'") auto
    then show ?thesis using subset_dil[of "(step ^^ m) (gl j)" 1] subset_dil[of "(step ^^ m) (gl j')" 1]
      by blast
  qed
  have "card (\<Union>j<k. (step ^^ m) (gl j)) = (\<Sum>j<k. card ((step ^^ m) (gl j)))"
  proof (rule card_UN_disjoint)
    show "finite {..<k}" by simp
    show "\<forall>j\<in>{..<k}. finite ((step ^^ m) (gl j))" by (simp add: steps_gl finite_egl_steps)
    show "\<forall>j\<in>{..<k}. \<forall>j'\<in>{..<k}. j \<noteq> j' \<longrightarrow> (step ^^ m) (gl j) \<inter> (step ^^ m) (gl j') = {}"
      using disj by blast
  qed
  also have "\<dots> = (\<Sum>j<k. 5)"
    by (simp add: steps_gl card_egl_steps)
  finally show ?thesis by simp
qed

lemma gun_emitted_disjoint: "gun \<inter> emitted k = {}"
proof -
  have g: "gun \<subseteq> {c. snd c < snd q0}"
    using gun_below_ok by (auto simp: gun_def list_all_iff)
  have "gl j \<subseteq> {c. snd q0 \<le> snd c}" for j
    using gl_box[of 0 j] by (auto simp: box_def tr_def)
  then have "emitted k \<subseteq> {c. snd q0 \<le> snd c}" by (auto simp: emitted_def)
  with g show ?thesis by fastforce
qed

theorem gun_population: "card ((step ^^ (30 * k)) gun) = 36 + 5 * k"
proof -
  have "card gun = 36" using gun_card_ok by (simp add: gun_def distinct_card)
  moreover have "card (emitted k) = 5 * k"
    using card_gl_stream[where m = 0 and k = k] by (simp add: emitted_def)
  moreover have "finite (emitted k)"
    by (auto simp: emitted_def gl_def finite_egl_steps)
  ultimately show ?thesis
    by (simp add: gun_stream card_Un_disjoint finite_gun gun_emitted_disjoint)
qed

theorem gun_population_lower: "5 * (n div 30) \<le> card ((step ^^ n) gun)"
proof -
  define k where "k = n div 30"
  define i where "i = n mod 30"
  have n: "n = i + 30 * k" by (simp add: i_def k_def)
  have i30: "i < 30" by (simp add: i_def)
  have "(step ^^ n) gun = (step ^^ i) (gun \<union> emitted k)"
    by (simp only: n funpow_add comp_apply gun_stream)
  also have "\<dots> = (step ^^ i) gun \<union> (step ^^ i) (emitted k)"
  proof (rule disjoint_steps, intro allI impI)
    fix i' assume "i' < i"
    then show "dil 1 ((step ^^ i') gun) \<inter> dil 1 ((step ^^ i') (emitted k)) = {}"
      using i30 by (intro gun_emitted_apart) simp
  qed
  finally have e: "(step ^^ i) (emitted k) \<subseteq> (step ^^ n) gun" by blast
  have "card ((step ^^ i) (emitted k)) = 5 * k"
    by (simp only: stream card_gl_stream)
  moreover have "card ((step ^^ i) (emitted k)) \<le> card ((step ^^ n) gun)"
    using e by (intro card_mono) (simp_all add: finite_steps finite_gun)
  ultimately show ?thesis by (simp add: k_def)
qed

corollary gun_population_linear: "30 \<le> n \<Longrightarrow> n \<le> 12 * card ((step ^^ n) gun)"
proof -
  assume "30 \<le> n"
  then have q: "1 \<le> n div 30" using div_le_mono[of 30 n 30] by simp
  have "n = n mod 30 + 30 * (n div 30)" by simp
  moreover have "n mod 30 < 30" by simp
  ultimately have "n \<le> 60 * (n div 30)" using q by linarith
  then show ?thesis using gun_population_lower[of n] by linarith
qed

theorem unbounded_population:
  "\<exists>S. finite S \<and> \<not> bdd_above (range (\<lambda>n. card ((step ^^ n) S)))"
proof (intro exI conjI)
  show "finite gun" by (rule finite_gun)
  show "\<not> bdd_above (range (\<lambda>n. card ((step ^^ n) gun)))"
  proof
    assume "bdd_above (range (\<lambda>n. card ((step ^^ n) gun)))"
    then obtain M where M: "\<And>n. card ((step ^^ n) gun) \<le> M" by (auto simp: bdd_above_def)
    have "36 + 5 * (M + 1) \<le> M" using M[of "30 * (M + 1)"] by (simp only: gun_population)
    then show False by simp
  qed
qed

end
