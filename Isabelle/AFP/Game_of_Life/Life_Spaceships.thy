(*  Title:      Game_of_Life/Life_Spaceships.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Spaceships
  imports Life_Speed Life_Spaceships_Data
begin

section \<open>The lightweight spaceship\<close>

text \<open>With \<open>x\<close> the column (to the right) and \<open>y\<close> the row (downwards), \<open>lwss\<close> is
  \<open>.X..X / X.... / X...X / XXXX.\<close>; it moves two cells to the left (\<open>-x\<close>) every four generations.\<close>

definition lwss :: gen where "lwss = set lwss_l"

lemma lwss_trace_ok: "trace_ok lwss_l lwss_trace"
  unfolding lwss_l_def lwss_trace_def by code_simp

theorem lwss_moves: "(step ^^ 4) lwss = transl (-2, 0) lwss"
proof -
  have "(step ^^ length lwss_trace) (set lwss_l) = set (last (lwss_l # lwss_trace))"
    by (rule trace_ok_correct[OF lwss_trace_ok])
  moreover have "length lwss_trace = 4" by (simp add: lwss_trace_def)
  moreover have "same_set (last (lwss_l # lwss_trace)) (map (tr (-2, 0)) lwss_l)"
    unfolding lwss_l_def lwss_trace_def by code_simp
  ultimately show ?thesis by (simp add: lwss_def transl_set same_set_correct)
qed

theorem lwss_not_translate:
  assumes "0 < k" "k < 4"
  shows "(step ^^ k) lwss \<noteq> transl v lwss"
proof -
  have d: "\<not> same_set (diffs_list lwss_l) (diffs_list (lwss_trace ! j))" if "j < 3" for j
  proof -
    have "j = 0 \<or> j = 1 \<or> j = 2" using that by auto
    moreover have "\<not> same_set (diffs_list lwss_l) (diffs_list (lwss_trace ! 0))"
                  "\<not> same_set (diffs_list lwss_l) (diffs_list (lwss_trace ! 1))"
                  "\<not> same_set (diffs_list lwss_l) (diffs_list (lwss_trace ! 2))"
      unfolding lwss_l_def lwss_trace_def by code_simp+
    ultimately show ?thesis by auto
  qed
  obtain j where j: "k = Suc j" "j < 3" using assms by (cases k) auto
  have "j < length lwss_trace" using j(2) by (simp add: lwss_trace_def)
  then have "(step ^^ k) lwss = set (lwss_trace ! j)"
    using trace_ok_nth[OF lwss_trace_ok] j(1) by (simp add: lwss_def)
  then show ?thesis
    using not_transl_by_diffs[OF d[OF j(2)]] by (simp add: lwss_def)
qed

theorem lwss_flight: "(step ^^ (4 * k)) lwss = transl (- 2 * int k, 0) lwss"
  using flight_mult[OF lwss_moves, of k] by (simp add: mult.commute)

text \<open>The lightweight spaceship moves by \<open>(-2, 0)\<close> every 4 generations: the orthogonal bound of
  \<open>speed_limit\<close> is attained.\<close>

theorem speed_limit_orthogonal_sharp:
  "finite lwss \<and> lwss \<noteq> {} \<and> (step ^^ 4) lwss = transl (-2, 0) lwss \<and> 2 * \<bar>-2::int\<bar> = int 4"
proof -
  have "finite lwss" "lwss \<noteq> {}" by (simp_all add: lwss_def lwss_l_def)
  then show ?thesis using lwss_moves by simp
qed

section \<open>Eater 1 eats a glider\<close>

text \<open>Eater 1 (fishhook) \<open>XX.. / X.X. / ..X. / ..XX\<close>.  The south-east glider of
  \<open>Life_Objects\<close>, shifted by \<open>(-5,-5)\<close> (initially at Chebyshev distance 3 from the eater, so
  their 1-thickenings are disjoint), is absorbed: after exactly 10 generations only the eater is
  left.  Shifted by one more cell to the right, the same glider destroys the eater and everything
  dies.\<close>

definition eater :: gen where "eater = set eater_l"

theorem eater_still: "step eater = eater"
proof -
  have "trace_ok eater_l [eater_l]" unfolding eater_l_def by code_simp
  from trace_ok_correct[OF this] show ?thesis by (simp add: eater_def)
qed

corollary eater_steps: "(step ^^ n) eater = eater"
  by (induction n) (simp_all add: eater_still)

lemma eater_glider_apart: "dil 1 eater \<inter> dil 1 (transl (-5, -5) glider) = {}"
proof -
  have "far 1 eater_l (map (tr (-5, -5)) glider_l)"
    unfolding eater_l_def glider_l_def by code_simp
  from far_correct[OF this] show ?thesis by (simp add: eater_def glider_set transl_set)
qed

theorem eater_eats_glider: "(step ^^ 10) (eater \<union> transl (-5, -5) glider) = eater"
proof -
  have tok: "trace_ok (eater_l @ map (tr (-5, -5)) glider_l) eat_trace"
    unfolding eater_l_def glider_l_def eat_trace_def by code_simp
  have "length eat_trace = 10" by (simp add: eat_trace_def)
  moreover have "same_set (last ((eater_l @ map (tr (-5, -5)) glider_l) # eat_trace)) eater_l"
    unfolding eater_l_def glider_l_def eat_trace_def by code_simp
  ultimately show ?thesis
    using trace_ok_correct[OF tok] by (simp add: eater_def glider_set transl_set same_set_correct)
qed

corollary eater_eats_glider_forever:
  "n \<ge> 10 \<Longrightarrow> (step ^^ n) (eater \<union> transl (-5, -5) glider) = eater"
proof -
  assume "n \<ge> 10"
  then obtain m where "n = m + 10" by (metis add.commute le_Suc_ex)
  then show ?thesis by (simp add: funpow_add eater_eats_glider eater_steps)
qed

text \<open>One cell further to the right the glider is not eaten: glider and eater annihilate each
  other.\<close>

theorem glider_off_lane_kills_eater:
  "n \<ge> 10 \<Longrightarrow> (step ^^ n) (eater \<union> transl (-4, -5) glider) = {}"
proof -
  assume "n \<ge> 10"
  then obtain m where n: "n = m + 10" by (metis add.commute le_Suc_ex)
  have tok: "trace_ok (eater_l @ map (tr (-4, -5)) glider_l) miss_trace"
    unfolding eater_l_def glider_l_def miss_trace_def by code_simp
  have "length miss_trace = 10" by (simp add: miss_trace_def)
  moreover have "last ((eater_l @ map (tr (-4, -5)) glider_l) # miss_trace) = []"
    by (simp add: miss_trace_def)
  ultimately have "(step ^^ 10) (eater \<union> transl (-4, -5) glider) = {}"
    using trace_ok_correct[OF tok] by (simp add: eater_def glider_set transl_set)
  then show ?thesis by (simp add: n funpow_add)
qed

end
