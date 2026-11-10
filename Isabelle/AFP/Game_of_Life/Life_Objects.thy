(*  Title:      Game_of_Life/Life_Objects.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Objects
  imports Life_Base
begin

section \<open>First objects: block, blinker, glider\<close>

text \<open>
  Coordinates: a cell is \<open>(x, y)\<close>; drawn with \<open>x\<close> as the column (growing to the right) and \<open>y\<close>
  as the row (growing downwards), the glider below is the usual south-east glider
  \<open>.X. / ..X / XXX\<close>, and it moves by \<open>(+1, +1)\<close> every four generations.
  The concrete evolutions are proved by trace replay: the intermediate generations were
  proposed by an external simulator and every transition is checked by \<open>trace_ok\<close>, evaluated
  with \<open>code_simp\<close> (no oracle).
\<close>

definition block :: gen where "block = {(0,0), (1,0), (0,1), (1,1)}"
definition blinker :: gen where "blinker = {(0,0), (1,0), (2,0)}"
definition blinker_v :: gen where "blinker_v = {(1,-1), (1,0), (1,1)}"
definition glider :: gen where "glider = {(1,0), (2,1), (0,2), (1,2), (2,2)}"

subsection \<open>Block: a still life\<close>

theorem block_still: "step block = block"
proof -
  have "trace_ok [(0,0), (1,0), (0,1), (1,1)] [[(0,0), (1,0), (0,1), (1,1)]]"
    by code_simp
  from trace_ok_correct[OF this] show ?thesis by (simp add: block_def)
qed

corollary block_steps: "(step ^^ n) block = block"
  by (induction n) (simp_all add: block_still)

subsection \<open>Blinker: an oscillator of period 2\<close>

lemma blinker_step: "step blinker = blinker_v"
proof -
  have "trace_ok [(0,0), (1,0), (2,0)] [[(1,-1), (1,0), (1,1)]]"
    by code_simp
  from trace_ok_correct[OF this] show ?thesis by (simp add: blinker_def blinker_v_def)
qed

lemma blinker_v_step: "step blinker_v = blinker"
proof -
  have "trace_ok [(1,-1), (1,0), (1,1)] [[(0,0), (1,0), (2,0)]]"
    by code_simp
  from trace_ok_correct[OF this] show ?thesis by (simp add: blinker_def blinker_v_def)
qed

theorem blinker_period_2: "(step ^^ 2) blinker = blinker" "step blinker \<noteq> blinker"
proof -
  show "(step ^^ 2) blinker = blinker"
    by (simp add: numeral_2_eq_2 blinker_step blinker_v_step)
  have "(0, 0) \<in> blinker" "(0, 0) \<notin> blinker_v"
    by (simp_all add: blinker_def blinker_v_def)
  then show "step blinker \<noteq> blinker"
    using blinker_step by auto
qed

corollary blinker_steps: "(step ^^ (2 * k)) blinker = blinker"
proof (induction k)
  case (Suc k)
  have "(step ^^ (2 * Suc k)) blinker = (step ^^ 2) ((step ^^ (2 * k)) blinker)"
    by (simp only: mult_Suc_right funpow_add comp_apply)
  then show ?case using Suc blinker_period_2(1) by simp
qed simp

subsection \<open>Glider\<close>

definition glider_l :: "cell list" where "glider_l = [(1,0), (2,1), (0,2), (1,2), (2,2)]"

text \<open>The intermediate generations of the glider, proposed by an external simulator (not trusted:
  every transition is checked by \<open>trace_ok\<close> below).\<close>

definition g1 :: "cell list" where "g1 = [(0,1), (1,2), (1,3), (2,1), (2,2)]"
definition g2 :: "cell list" where "g2 = [(0,2), (1,3), (2,1), (2,2), (2,3)]"
definition g3 :: "cell list" where "g3 = [(1,1), (1,3), (2,2), (2,3), (3,2)]"
definition g4 :: "cell list" where "g4 = [(1,3), (2,1), (2,3), (3,2), (3,3)]"

lemma glider_set: "glider = set glider_l"
  by (simp add: glider_def glider_l_def)

lemma glider_trace: "trace_ok glider_l [g1, g2, g3, g4]"
  unfolding glider_l_def g1_def g2_def g3_def g4_def by code_simp

lemma trace_ok_prefix: "trace_ok xs (yss @ zss) \<Longrightarrow> trace_ok xs yss"
  by (induction yss arbitrary: xs) auto

lemma glider_steps_1_to_4:
  "step glider = set g1" "(step ^^ 2) glider = set g2" "(step ^^ 3) glider = set g3"
  "(step ^^ 4) glider = set g4"
proof -
  have t: "trace_ok glider_l [g1]" "trace_ok glider_l [g1, g2]" "trace_ok glider_l [g1, g2, g3]"
    using trace_ok_prefix[of glider_l "[g1]" "[g2, g3, g4]"]
          trace_ok_prefix[of glider_l "[g1, g2]" "[g3, g4]"]
          trace_ok_prefix[of glider_l "[g1, g2, g3]" "[g4]"] glider_trace by simp_all
  show "step glider = set g1" using trace_ok_correct[OF t(1)] by (simp add: glider_set eval_nat_numeral)
  show "(step ^^ 2) glider = set g2" using trace_ok_correct[OF t(2)] by (simp add: glider_set eval_nat_numeral)
  show "(step ^^ 3) glider = set g3" using trace_ok_correct[OF t(3)] by (simp add: glider_set eval_nat_numeral)
  show "(step ^^ 4) glider = set g4" using trace_ok_correct[OF glider_trace] by (simp add: glider_set eval_nat_numeral)
qed

theorem glider_moves: "(step ^^ 4) glider = transl (1, 1) glider"
proof -
  have "same_set g4 (map (tr (1, 1)) glider_l)"
    unfolding g4_def glider_l_def by code_simp
  then have "set g4 = transl (1, 1) glider"
    by (simp add: glider_set transl_set same_set_correct)
  then show ?thesis
    by (simp add: glider_steps_1_to_4(4))
qed

text \<open>Minimal period: in generations 1, 2 and 3 the glider is not a translate of itself (the
  difference set, a translation invariant, differs).\<close>

theorem glider_not_translate:
  assumes "0 < k" "k < 4"
  shows "(step ^^ k) glider \<noteq> transl v glider"
proof -
  have "\<not> same_set (diffs_list glider_l) (diffs_list g1)"
       "\<not> same_set (diffs_list glider_l) (diffs_list g2)"
       "\<not> same_set (diffs_list glider_l) (diffs_list g3)"
    unfolding glider_l_def g1_def g2_def g3_def by code_simp+
  then have "set g1 \<noteq> transl v (set glider_l)" "set g2 \<noteq> transl v (set glider_l)"
            "set g3 \<noteq> transl v (set glider_l)"
    by (simp_all add: not_transl_by_diffs)
  moreover have "k = 1 \<or> k = 2 \<or> k = 3" using assms by auto
  ultimately show ?thesis
    using glider_steps_1_to_4 by (auto simp: glider_set)
qed

lemma transl_transl: "transl v (transl w S) = transl (fst v + fst w, snd v + snd w) S"
  unfolding transl_def image_image by (rule image_cong) (simp_all add: tr_def)

theorem glider_flight: "(step ^^ (4 * k)) glider = transl (int k, int k) glider"
proof (induction k)
  case 0
  then show ?case by (simp add: transl_def tr_def)
next
  case (Suc k)
  have "(step ^^ (4 * Suc k)) glider = (step ^^ 4) ((step ^^ (4 * k)) glider)"
    by (simp only: mult_Suc_right funpow_add comp_apply)
  also have "\<dots> = transl (int k, int k) ((step ^^ 4) glider)"
    by (simp add: Suc steps_transl)
  also have "\<dots> = transl (int (Suc k), int (Suc k)) glider"
    by (simp add: glider_moves transl_transl add.commute)
  finally show ?case .
qed

text \<open>Every translate of the glider glides, and so does the quarter-turned glider (which moves
  by \<open>(-1, 1)\<close>); the other two directions follow by turning again.\<close>

corollary glider_moves_anywhere: "(step ^^ 4) (transl w glider) = transl (1, 1) (transl w glider)"
  by (simp add: steps_transl glider_moves transl_transl add.commute)

lemma rot_transl: "rot ` transl v S = transl (rot v) (rot ` S)"
  by (auto simp: transl_def tr_def rot_def image_image)

corollary rotated_glider_moves: "(step ^^ 4) (rot ` glider) = transl (-1, 1) (rot ` glider)"
proof -
  have "(step ^^ 4) (rot ` glider) = rot ` (step ^^ 4) glider"
    by (rule steps_equivariant[OF bij_rot nbhd_rot])
  also have "\<dots> = transl (rot (1, 1)) (rot ` glider)"
    by (simp only: glider_moves rot_transl)
  also have "rot (1, 1) = (-1, 1)"
    by (simp add: rot_def)
  finally show ?thesis .
qed

end
