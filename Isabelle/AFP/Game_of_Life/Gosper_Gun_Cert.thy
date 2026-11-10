(*  Title:      Game_of_Life/Gosper_Gun_Cert.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Gosper_Gun_Cert
  imports Life_Disjoint Life_Fast Gosper_Gun_Data
begin

section \<open>Finite certificates for the Gosper gun\<close>

text \<open>Every fact here is a closed computation on the data of \<open>Gosper_Gun_Data\<close> (proposed by
  an external simulator), checked by \<open>code_simp\<close>: the 30 generations of the gun (\<open>trace_ok2\<close>), the 29
  generations of the emitted glider, and the numerical side conditions used in \<open>Gosper_Gun\<close>.\<close>

definition in_box :: "cell \<Rightarrow> cell list \<Rightarrow> bool" where
  "in_box q xs = list_all (\<lambda>c. fst q \<le> fst c \<and> fst c \<le> fst q + 3 \<and> snd q \<le> snd c \<and> snd c \<le> snd q + 3) xs"

lemma len_gun_trace: "length gun_trace = 30"
  by (simp add: gun_trace_def)

lemma len_e_trace: "length e_trace = 29"
  by (simp add: e_trace_def)

lemma gun_trace_ok: "trace_ok2 gun_l gun_trace"
  unfolding gun_l_def gun_trace_def by code_simp

lemma gun_last: "same_set ((gun_l # gun_trace) ! 30) (gun_l @ e_l)"
  unfolding gun_l_def gun_trace_def e_l_def by code_simp

lemma gun_low_ok: "list_all (\<lambda>s. list_all (\<lambda>c. snd c \<le> ymax) s) (take 30 (gun_l # gun_trace))"
  unfolding gun_l_def gun_trace_def ymax_def by code_simp

lemma gun_far_ok: "list_all2 (far 1) (take 30 (gun_l # gun_trace)) (e_l # e_trace)"
  unfolding gun_l_def gun_trace_def e_l_def e_trace_def by code_simp

lemma gun_below_ok: "list_all (\<lambda>c. snd c < snd q0) gun_l"
  unfolding gun_l_def q0_def by code_simp

lemma gun_card_ok: "distinct gun_l \<and> length gun_l = 36"
  unfolding gun_l_def by code_simp

lemma e_trace_ok: "trace_ok2 e_l e_trace"
  unfolding e_l_def e_trace_def by code_simp

lemma e_moves_ok: "same_set ((e_l # e_trace) ! 4) (map (tr (1, 1)) e_l)"
  unfolding e_l_def e_trace_def by code_simp

lemma e_box_ok: "list_all (in_box q0) (take 4 (e_l # e_trace))"
  unfolding e_l_def e_trace_def q0_def in_box_def by code_simp

lemma e_card_ok: "list_all (\<lambda>s. distinct s \<and> length s = 5) (take 4 (e_l # e_trace))"
  unfolding e_l_def e_trace_def by code_simp

lemma ymax_sep: "ymax + 1 < snd q0 + 6"
  by (simp add: ymax_def q0_def)

end
