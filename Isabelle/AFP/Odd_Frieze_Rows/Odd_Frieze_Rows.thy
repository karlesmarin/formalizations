(*  Title:      Odd_Frieze_Rows.thy
    Author:     Carles Marín

    Integer friezes of odd order with two sign changes

    For every odd n >= 15, two integer Conway-Coxeter frieze patterns of width w = n - 3 whose rows
    k = floor (w/2) differ, along the period, with no zero and exactly two sign changes. Row floor (w/2) lies in the
    range 1 <= k <= floor (w/2) of Problem 1 of S. Tabachnikov, which asks whether four sign changes must occur.

    Model as in the entry Integer_Frieze_Rows: lattice polygons V_0, ..., V_(n-1). With n = 2h + 1, the cyclic row
    k = h - 1 has the entries det (V_i, V_(i+h)) for i <= h and, by the glide symmetry V_(i+n) = - V_i,
    det (V_(i-h-1), V_i) for h < i < n.

    Main results:
    * two_sign_changes.

    References:
    * S. Tabachnikov, A four-vertex theorem for frieze patterns?, Math. Intelligencer 40 (2018) 14--18, Problem 1.
*)

theory Odd_Frieze_Rows
  imports Integer_Frieze_Rows.Integer_Frieze_Rows
begin

section \<open>The two families\<close>

text \<open>Both polygons consist of five pieces: three fixed vectors, an arithmetic progression of $t + 1$ vectors,
  five fixed vectors, a second progression of $t + 1$ vectors, and five fixed vectors; $n = 15 + 2t$.\<close>

definition pA1 :: "nat \<Rightarrow> nat \<Rightarrow> vec" where
  "pA1 t s = (- (int t + 2 - int s), 2 * (int t + 2 - int s) - 1)"

definition pA2 :: "nat \<Rightarrow> nat \<Rightarrow> vec" where
  "pA2 t s = (- 6 - 11 * (int t + 1 - int s), 7 + 13 * (int t + 1 - int s))"

definition pB1 :: "nat \<Rightarrow> nat \<Rightarrow> vec" where
  "pB1 t s = (- (int t + 1 - int s), 3 * (int t + 1 - int s) - 1)"

definition pB2 :: "nat \<Rightarrow> nat \<Rightarrow> vec" where
  "pB2 t s = (- 8 - 13 * (int t - int s), 3 + 5 * (int t - int s))"

definition VA :: "nat \<Rightarrow> vec list" where
  "VA t = [(1, 0), (0, 1), (-1, 2)] @ map (pA1 t) [0..<Suc t] @ [(-3, 4), (-4, 5), (-9, 11), (-5, 6), (-11, 13)]
     @ map (pA2 t) [0..<Suc t] @ [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)]"

definition VB :: "nat \<Rightarrow> vec list" where
  "VB t = [(1, 0), (0, 1), (-1, 3)] @ map (pB1 t) [0..<Suc t] @ [(-1, 1), (-2, 1), (-5, 2), (-18, 7), (-13, 5)]
     @ map (pB2 t) [0..<Suc t] @ [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)]"

lemma length_VA [simp]: "length (VA t) = 15 + 2 * t"
  by (simp add: VA_def)

lemma length_VB [simp]: "length (VB t) = 15 + 2 * t"
  by (simp add: VB_def)

text \<open>Inserting two ears, after positions $t + 8$ and $2$, gives the next member: each progression gains a new
  first vector.\<close>

section \<open>Inserting into concatenated lists\<close>

lemma ins_mid: assumes "length xs = n" shows "ins (xs @ a # b # ys) n = xs @ a # vadd a b # b # ys"
  unfolding assms[symmetric] ins_def by (simp add: nth_append)

lemma ins_2: "ins (x # y # a # b # ys) 2 = x # y # a # vadd a b # b # ys"
  by (simp add: ins_def numeral_2_eq_2)

lemma map_shift2:
  assumes "\<And>s. f (Suc s) = g s"
  shows "map f [0..<Suc (Suc t)] = f 0 # map g [0..<Suc t]"
proof -
  have "[0..<Suc (Suc t)] = 0 # [Suc 0..<Suc (Suc t)]" by (rule upt_conv_Cons) simp
  also have "[Suc 0..<Suc (Suc t)] = map Suc [0..<Suc t]" by (simp only: map_Suc_upt)
  finally have "map f [0..<Suc (Suc t)] = f 0 # map (f \<circ> Suc) [0..<Suc t]" by (simp only: list.map map_map)
  moreover have "f \<circ> Suc = g" by (rule ext, simp add: assms)
  ultimately show ?thesis by simp
qed

lemma map_hd_upt: "map f [0..<Suc t] = f 0 # map f [Suc 0..<Suc t]"
proof -
  have "[0..<Suc t] = 0 # [Suc 0..<Suc t]" by (rule upt_conv_Cons) simp
  then show ?thesis by (simp only: list.map)
qed

lemma VA_step: "ins (ins (VA t) (t + 8)) 2 = VA (Suc t)"
proof -
  have m1: "map (pA1 (Suc t)) [0..<Suc (Suc t)] = pA1 (Suc t) 0 # map (pA1 t) [0..<Suc t]"
    by (rule map_shift2) (simp add: pA1_def)
  have m2: "map (pA2 (Suc t)) [0..<Suc (Suc t)] = pA2 (Suc t) 0 # map (pA2 t) [0..<Suc t]"
    by (rule map_shift2) (simp add: pA2_def)
  have v1: "vadd (-1, 2) (pA1 t 0) = pA1 (Suc t) 0" by (simp add: vadd_def pA1_def algebra_simps)
  have v2: "vadd (-11, 13) (pA2 t 0) = pA2 (Suc t) 0" by (simp add: vadd_def pA2_def algebra_simps)
  have e: "VA t = ([(1, 0), (0, 1), (-1, 2)] @ pA1 t 0 # map (pA1 t) [Suc 0..<Suc t]
       @ [(-3, 4), (-4, 5), (-9, 11), (-5, 6)]) @ (-11, 13) # pA2 t 0 # (map (pA2 t) [Suc 0..<Suc t]
       @ [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)])"
    by (simp del: upt_Suc add: VA_def map_hd_upt[of "pA1 t" t] map_hd_upt[of "pA2 t" t])
  have s1: "ins (VA t) (t + 8) = ([(1, 0), (0, 1)] @ (-1, 2) # pA1 t 0 # (map (pA1 t) [Suc 0..<Suc t]
       @ [(-3, 4), (-4, 5), (-9, 11), (-5, 6)])) @ (-11, 13) # pA2 (Suc t) 0 # pA2 t 0 #
       (map (pA2 t) [Suc 0..<Suc t] @ [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)])"
    by (subst e, subst ins_mid[where n = "t + 8"]) (simp_all del: upt_Suc add: v2)
  have s2: "ins (ins (VA t) (t + 8)) 2 = [(1, 0), (0, 1)] @ (-1, 2) # pA1 (Suc t) 0 # pA1 t 0 #
       ((map (pA1 t) [Suc 0..<Suc t] @ [(-3, 4), (-4, 5), (-9, 11), (-5, 6)]) @ (-11, 13) # pA2 (Suc t) 0 # pA2 t 0 #
       (map (pA2 t) [Suc 0..<Suc t] @ [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)]))"
    by (subst s1, simp only: append_assoc append_Cons append_Nil, subst ins_2)
      (simp del: upt_Suc add: v1)
  show ?thesis
    by (subst s2) (simp del: upt_Suc add: VA_def m1 m2 map_hd_upt[of "pA1 t" t] map_hd_upt[of "pA2 t" t])
qed

lemma VB_step: "ins (ins (VB t) (t + 8)) 2 = VB (Suc t)"
proof -
  have m1: "map (pB1 (Suc t)) [0..<Suc (Suc t)] = pB1 (Suc t) 0 # map (pB1 t) [0..<Suc t]"
    by (rule map_shift2) (simp add: pB1_def)
  have m2: "map (pB2 (Suc t)) [0..<Suc (Suc t)] = pB2 (Suc t) 0 # map (pB2 t) [0..<Suc t]"
    by (rule map_shift2) (simp add: pB2_def)
  have v1: "vadd (-1, 3) (pB1 t 0) = pB1 (Suc t) 0" by (simp add: vadd_def pB1_def algebra_simps)
  have v2: "vadd (-13, 5) (pB2 t 0) = pB2 (Suc t) 0" by (simp add: vadd_def pB2_def algebra_simps)
  have e: "VB t = ([(1, 0), (0, 1), (-1, 3)] @ pB1 t 0 # map (pB1 t) [Suc 0..<Suc t]
       @ [(-1, 1), (-2, 1), (-5, 2), (-18, 7)]) @ (-13, 5) # pB2 t 0 # (map (pB2 t) [Suc 0..<Suc t]
       @ [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)])"
    by (simp del: upt_Suc add: VB_def map_hd_upt[of "pB1 t" t] map_hd_upt[of "pB2 t" t])
  have s1: "ins (VB t) (t + 8) = ([(1, 0), (0, 1)] @ (-1, 3) # pB1 t 0 # (map (pB1 t) [Suc 0..<Suc t]
       @ [(-1, 1), (-2, 1), (-5, 2), (-18, 7)])) @ (-13, 5) # pB2 (Suc t) 0 # pB2 t 0 #
       (map (pB2 t) [Suc 0..<Suc t] @ [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)])"
    by (subst e, subst ins_mid[where n = "t + 8"]) (simp_all del: upt_Suc add: v2)
  have s2: "ins (ins (VB t) (t + 8)) 2 = [(1, 0), (0, 1)] @ (-1, 3) # pB1 (Suc t) 0 # pB1 t 0 #
       ((map (pB1 t) [Suc 0..<Suc t] @ [(-1, 1), (-2, 1), (-5, 2), (-18, 7)]) @ (-13, 5) # pB2 (Suc t) 0 # pB2 t 0 #
       (map (pB2 t) [Suc 0..<Suc t] @ [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)]))"
    by (subst s1, simp only: append_assoc append_Cons append_Nil, subst ins_2)
      (simp del: upt_Suc add: v1)
  show ?thesis
    by (subst s2) (simp del: upt_Suc add: VB_def m1 m2 map_hd_upt[of "pB1 t" t] map_hd_upt[of "pB2 t" t])
qed

lemma frieze_VA0: "frieze (VA 0)"
  unfolding frieze_def VA_def pA1_def pA2_def det_def by code_simp

lemma frieze_VB0: "frieze (VB 0)"
  unfolding frieze_def VB_def pB1_def pB2_def det_def by code_simp

lemma frieze_VA: "frieze (VA t)"
proof (induction t)
  case 0
  show ?case by (rule frieze_VA0)
next
  case (Suc t)
  have a: "frieze (ins (VA t) (t + 8))" by (rule ins_frieze[OF Suc.IH]) simp
  have "frieze (ins (ins (VA t) (t + 8)) 2)" by (rule ins_frieze[OF a]) simp
  then show ?case by (simp add: VA_step)
qed

lemma frieze_VB: "frieze (VB t)"
proof (induction t)
  case 0
  show ?case by (rule frieze_VB0)
next
  case (Suc t)
  have a: "frieze (ins (VB t) (t + 8))" by (rule ins_frieze[OF Suc.IH]) simp
  have "frieze (ins (ins (VB t) (t + 8)) 2)" by (rule ins_frieze[OF a]) simp
  then show ?case by (simp add: VB_step)
qed

section \<open>The row and its differences\<close>

text \<open>Row $k = h - 1$ of a frieze with $n = 2h + 1$, as a cyclic sequence of $n$ entries.\<close>

definition row_entry :: "vec list \<Rightarrow> nat \<Rightarrow> int" where
  "row_entry V i = (let h = length V div 2 in
     if i \<le> h then det (V ! i) (V ! (i + h)) else det (V ! (i - h - 1)) (V ! i))"

definition dd :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "dd t i = row_entry (VB t) i - row_entry (VA t) i"

text \<open>The number of cyclic sign changes of a sequence of length \<open>n\<close>.\<close>

definition sign_changes :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat" where
  "sign_changes d n = card {i. i < n \<and> d i * d (Suc i mod n) < 0}"

section \<open>Counting sign changes\<close>

lemma sign_changes_list:
  "sign_changes d n = length (filter (\<lambda>i. d i * d (Suc i mod n) < 0) [0..<n])"
proof -
  have "{i. i < n \<and> d i * d (Suc i mod n) < 0} = set (filter (\<lambda>i. d i * d (Suc i mod n) < 0) [0..<n])"
    by auto
  moreover have "card (set (filter (\<lambda>i. d i * d (Suc i mod n) < 0) [0..<n])) =
      length (filter (\<lambda>i. d i * d (Suc i mod n) < 0) [0..<n])"
    by (rule distinct_card) simp
  ultimately show ?thesis unfolding sign_changes_def by simp
qed

lemma ball_list: "(\<forall>i < n. P i) \<longleftrightarrow> list_all P [0..<n]"
  by (simp add: list_all_iff Ball_def)

section \<open>The vectors of the two polygons\<close>

lemma nth_skip: "length a \<le> i \<Longrightarrow> k = i - length a \<Longrightarrow> (a @ r) ! i = r ! k"
  by (simp add: nth_append)

lemma nth_head: "i < length a \<Longrightarrow> (a @ r) ! i = a ! i"
  by (simp add: nth_append)

lemma nth_VA:
  assumes "i < 15 + 2 * t"
  shows "VA t ! i =
    (if i < 3 then [(1, 0), (0, 1), (-1, 2)] ! i
     else if i < t + 4 then pA1 t (i - 3)
     else if i < t + 9 then [(-3, 4), (-4, 5), (-9, 11), (-5, 6), (-11, 13)] ! (i - (t + 4))
     else if i < 2 * t + 10 then pA2 t (i - (t + 9))
     else [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)] ! (i - (2 * t + 10)))"
proof (cases "i < 3")
  case True
  then have "i = 0 \<or> i = 1 \<or> i = 2" by presburger
  then show ?thesis by (auto simp add: VA_def)
next
  case n1: False
  show ?thesis
  proof (cases "i < t + 4")
    case True
    have h: "VA t ! i = map (pA1 t) [0..<Suc t] ! (i - 3)"
      apply (unfold VA_def)
      apply (insert True n1)
      apply (subst nth_skip[where k = "i - 3"])
      prefer 3
      apply (subst nth_head)
      apply (((simp; fail) | presburger | (simp; presburger))+)
      done
    have h2: "map (pA1 t) [0..<Suc t] ! (i - 3) = pA1 t (i - 3)"
      using True n1 by (simp add: nth_map del: upt_Suc)
    show ?thesis using h h2 True n1 by simp
  next
    case n2: False
    show ?thesis
    proof (cases "i < t + 9")
      case True
      have h: "VA t ! i = [(-3, 4), (-4, 5), (-9, 11), (-5, 6), (-11, 13)] ! (i - (t + 4))"
        apply (unfold VA_def)
        apply (insert True n1 n2)
        apply (subst nth_skip[where k = "i - 3"])
        prefer 3
        apply (subst nth_skip[where k = "i - (t + 4)"])
        prefer 3
        apply (subst nth_head)
        apply (((simp; fail) | presburger | (simp; presburger))+)
        done
      show ?thesis using h True n1 n2 by simp
    next
      case n3: False
      show ?thesis
      proof (cases "i < 2 * t + 10")
        case True
        have h: "VA t ! i = map (pA2 t) [0..<Suc t] ! (i - (t + 9))"
          apply (unfold VA_def)
          apply (insert True n1 n2 n3)
          apply (subst nth_skip[where k = "i - 3"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 4)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 9)"])
          prefer 3
          apply (subst nth_head)
          apply (((simp; fail) | presburger | (simp; presburger))+)
          done
        have h2: "map (pA2 t) [0..<Suc t] ! (i - (t + 9)) = pA2 t (i - (t + 9))"
          using True n3 by (simp add: nth_map del: upt_Suc)
        show ?thesis using h h2 True n1 n2 n3 by simp
      next
        case n4: False
        have h: "VA t ! i = [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)] ! (i - (2 * t + 10))"
          apply (unfold VA_def)
          apply (insert n1 n2 n3 n4)
          apply (subst nth_skip[where k = "i - 3"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 4)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 9)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (2 * t + 10)"])
          apply (((simp; fail) | presburger | (simp; presburger))+)
          done
        show ?thesis using h n1 n2 n3 n4 by simp
      qed
    qed
  qed
qed

lemma nth_VB:
  assumes "i < 15 + 2 * t"
  shows "VB t ! i =
    (if i < 3 then [(1, 0), (0, 1), (-1, 3)] ! i
     else if i < t + 4 then pB1 t (i - 3)
     else if i < t + 9 then [(-1, 1), (-2, 1), (-5, 2), (-18, 7), (-13, 5)] ! (i - (t + 4))
     else if i < 2 * t + 10 then pB2 t (i - (t + 9))
     else [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)] ! (i - (2 * t + 10)))"
proof (cases "i < 3")
  case True
  then have "i = 0 \<or> i = 1 \<or> i = 2" by presburger
  then show ?thesis by (auto simp add: VB_def)
next
  case n1: False
  show ?thesis
  proof (cases "i < t + 4")
    case True
    have h: "VB t ! i = map (pB1 t) [0..<Suc t] ! (i - 3)"
      apply (unfold VB_def)
      apply (insert True n1)
      apply (subst nth_skip[where k = "i - 3"])
      prefer 3
      apply (subst nth_head)
      apply (((simp; fail) | presburger | (simp; presburger))+)
      done
    have h2: "map (pB1 t) [0..<Suc t] ! (i - 3) = pB1 t (i - 3)"
      using True n1 by (simp add: nth_map del: upt_Suc)
    show ?thesis using h h2 True n1 by simp
  next
    case n2: False
    show ?thesis
    proof (cases "i < t + 9")
      case True
      have h: "VB t ! i = [(-1, 1), (-2, 1), (-5, 2), (-18, 7), (-13, 5)] ! (i - (t + 4))"
        apply (unfold VB_def)
        apply (insert True n1 n2)
        apply (subst nth_skip[where k = "i - 3"])
        prefer 3
        apply (subst nth_skip[where k = "i - (t + 4)"])
        prefer 3
        apply (subst nth_head)
        apply (((simp; fail) | presburger | (simp; presburger))+)
        done
      show ?thesis using h True n1 n2 by simp
    next
      case n3: False
      show ?thesis
      proof (cases "i < 2 * t + 10")
        case True
        have h: "VB t ! i = map (pB2 t) [0..<Suc t] ! (i - (t + 9))"
          apply (unfold VB_def)
          apply (insert True n1 n2 n3)
          apply (subst nth_skip[where k = "i - 3"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 4)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 9)"])
          prefer 3
          apply (subst nth_head)
          apply (((simp; fail) | presburger | (simp; presburger))+)
          done
        have h2: "map (pB2 t) [0..<Suc t] ! (i - (t + 9)) = pB2 t (i - (t + 9))"
          using True n3 by (simp add: nth_map del: upt_Suc)
        show ?thesis using h h2 True n1 n2 n3 by simp
      next
        case n4: False
        have h: "VB t ! i = [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)] ! (i - (2 * t + 10))"
          apply (unfold VB_def)
          apply (insert n1 n2 n3 n4)
          apply (subst nth_skip[where k = "i - 3"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 4)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (t + 9)"])
          prefer 3
          apply (subst nth_skip[where k = "i - (2 * t + 10)"])
          apply (((simp; fail) | presburger | (simp; presburger))+)
          done
        show ?thesis using h n1 n2 n3 n4 by simp
      qed
    qed
  qed
qed

lemma A_F0: "k < 3 \<Longrightarrow> VA t ! k = [(1, 0), (0, 1), (-1, 2)] ! k"
  by (subst nth_VA) auto

lemma A_P1: "k = s + 3 \<Longrightarrow> s \<le> t \<Longrightarrow> VA t ! k = pA1 t s"
  by (subst nth_VA) auto

lemma A_F1: "k = t + 4 + r \<Longrightarrow> r < 5 \<Longrightarrow>
    VA t ! k = [(-3, 4), (-4, 5), (-9, 11), (-5, 6), (-11, 13)] ! r"
  by (subst nth_VA) auto

lemma A_P2: "k = t + 9 + s \<Longrightarrow> s \<le> t \<Longrightarrow> VA t ! k = pA2 t s"
  by (subst nth_VA) auto

lemma A_F2: "k = 2 * t + 10 + r \<Longrightarrow> r < 5 \<Longrightarrow>
    VA t ! k = [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)] ! r"
  by (subst nth_VA) auto

lemma B_F0: "k < 3 \<Longrightarrow> VB t ! k = [(1, 0), (0, 1), (-1, 3)] ! k"
  by (subst nth_VB) auto

lemma B_P1: "k = s + 3 \<Longrightarrow> s \<le> t \<Longrightarrow> VB t ! k = pB1 t s"
  by (subst nth_VB) auto

lemma B_F1: "k = t + 4 + r \<Longrightarrow> r < 5 \<Longrightarrow>
    VB t ! k = [(-1, 1), (-2, 1), (-5, 2), (-18, 7), (-13, 5)] ! r"
  by (subst nth_VB) auto

lemma B_P2: "k = t + 9 + s \<Longrightarrow> s \<le> t \<Longrightarrow> VB t ! k = pB2 t s"
  by (subst nth_VB) auto

lemma B_F2: "k = 2 * t + 10 + r \<Longrightarrow> r < 5 \<Longrightarrow>
    VB t ! k = [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)] ! r"
  by (subst nth_VB) auto

section \<open>Values of the row differences\<close>

lemma dd_lo: "i \<le> t + 7 \<Longrightarrow>
    dd t i = det (VB t ! i) (VB t ! (i + (t + 7))) - det (VA t ! i) (VA t ! (i + (t + 7)))"
proof -
  assume h: "i \<le> t + 7"
  have l: "(15 + 2 * t) div 2 = t + 7" by simp
  show ?thesis using h l by (simp add: dd_def row_entry_def Let_def)
qed

lemma dd_hi: "t + 7 < i \<Longrightarrow>
    dd t i = det (VB t ! (i - (t + 8))) (VB t ! i) - det (VA t ! (i - (t + 8))) (VA t ! i)"
proof -
  assume h: "t + 7 < i"
  have l: "(15 + 2 * t) div 2 = t + 7" by simp
  have n: "\<not> i \<le> t + 7" using h by simp
  have e: "i - (t + 7) - 1 = i - (t + 8)" by simp
  show ?thesis using n l e by (simp add: dd_def row_entry_def Let_def)
qed

lemma dd_lo_eq:
  assumes "i \<le> t + 7" "k = i + (t + 7)" "VA t ! i = a" "VA t ! k = b" "VB t ! i = c" "VB t ! k = d"
  shows "dd t i = det c d - det a b"
proof -
  have e: "i + (t + 7) = k" using assms(2) by simp
  note h = dd_lo[OF assms(1)]
  show ?thesis using h by (simp only: e assms(3-6))
qed

lemma dd_hi_eq:
  assumes "t + 7 < i" "i = j + (t + 8)" "VA t ! j = a" "VA t ! i = b" "VB t ! j = c" "VB t ! i = d"
  shows "dd t i = det c d - det a b"
proof -
  have e: "i - (t + 8) = j" using assms(2) by simp
  note h = dd_hi[OF assms(1)]
  show ?thesis using h by (simp only: e assms(3-6))
qed

lemma dd_0: "dd t 0 = 1"
proof -
  have "dd t 0 = det (1, 0) (-18, 7) - det (1, 0) (-5, 6)"
  proof (rule dd_lo_eq[where k = "t + 7"])
    show "0 \<le> t + 7" by simp
    show "t + 7 = 0 + (t + 7)" by simp
    show "VA t ! 0 = (1, 0)" by (subst A_F0) auto
    show "VA t ! (t + 7) = (-5, 6)" by (subst A_F1[where r = 3]) auto
    show "VB t ! 0 = (1, 0)" by (subst B_F0) auto
    show "VB t ! (t + 7) = (-18, 7)" by (subst B_F1[where r = 3]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_1: "dd t 1 = 2"
proof -
  have "dd t 1 = det (0, 1) (-13, 5) - det (0, 1) (-11, 13)"
  proof (rule dd_lo_eq[where k = "t + 8"])
    show "1 \<le> t + 7" by simp
    show "t + 8 = 1 + (t + 7)" by simp
    show "VA t ! 1 = (0, 1)" by (subst A_F0) auto
    show "VA t ! (t + 8) = (-11, 13)" by (subst A_F1[where r = 4]) auto
    show "VB t ! 1 = (0, 1)" by (subst B_F0) auto
    show "VB t ! (t + 8) = (-13, 5)" by (subst B_F1[where r = 4]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_2: "dd t 2 = 25 * int t + 7"
proof -
  have "dd t 2 = det (-1, 3) (pB2 t 0) - det (-1, 2) (pA2 t 0)"
  proof (rule dd_lo_eq[where k = "t + 9"])
    show "2 \<le> t + 7" by simp
    show "t + 9 = 2 + (t + 7)" by simp
    show "VA t ! 2 = (-1, 2)" by (subst A_F0) auto
    show "VA t ! (t + 9) = pA2 t 0" by (rule A_P2) auto
    show "VB t ! 2 = (-1, 3)" by (subst B_F0) auto
    show "VB t ! (t + 9) = pB2 t 0" by (rule B_P2) auto
  qed
  then show ?thesis by (simp add: det_def pA2_def pB2_def algebra_simps)
qed

lemma dd_c1:
  assumes "s < t"
  shows "dd t (s + 3) = 25 * (int t - int s)\<^sup>2 - 4 * (int t - int s) - 12"
proof -
  have "dd t (s + 3) = det (pB1 t s) (pB2 t (s + 1)) - det (pA1 t s) (pA2 t (s + 1))"
  proof (rule dd_lo_eq[where k = "t + 10 + s"])
    show "s + 3 \<le> t + 7" using assms by simp
    show "t + 10 + s = s + 3 + (t + 7)" by simp
    show "VA t ! (s + 3) = pA1 t s" using assms by (intro A_P1) auto
    show "VA t ! (t + 10 + s) = pA2 t (s + 1)" using assms by (intro A_P2) auto
    show "VB t ! (s + 3) = pB1 t s" using assms by (intro B_P1) auto
    show "VB t ! (t + 10 + s) = pB2 t (s + 1)" using assms by (intro B_P2) auto
  qed
  then show ?thesis by (simp add: det_def pA1_def pA2_def pB1_def pB2_def algebra_simps power2_eq_square)
qed

lemma poly1: "(u::int) \<ge> 1 \<Longrightarrow> 0 < 25 * u\<^sup>2 - 4 * u - 12"
proof -
  assume u: "u \<ge> 1"
  have h: "0 \<le> (u - 1) * u" by (rule mult_nonneg_nonneg) (use u in linarith)+
  have e: "(u - 1) * u = u\<^sup>2 - u" by (simp add: algebra_simps power2_eq_square)
  show ?thesis using h e u by linarith
qed

lemma poly2: "(u::int) \<ge> 2 \<Longrightarrow> 0 < 25 * u\<^sup>2 - 29 * u - 26"
proof -
  assume u: "u \<ge> 2"
  have h: "0 \<le> (u - 2) * u" by (rule mult_nonneg_nonneg) (use u in linarith)+
  have e: "(u - 2) * u = u\<^sup>2 - 2 * u" by (simp add: algebra_simps power2_eq_square)
  show ?thesis using h e u by linarith
qed

lemma dd_c1_pos:
  assumes "s < t"
  shows "0 < dd t (s + 3)"
proof -
  have u: "1 \<le> int t - int s" using assms by simp
  have "0 < 25 * (int t - int s)\<^sup>2 - 4 * (int t - int s) - 12"
    by (rule poly1) (use u in simp)
  then show ?thesis using dd_c1[OF assms] by simp
qed

lemma dd_3t: "dd t (t + 3) = 1"
proof -
  have "dd t (t + 3) = det (pB1 t t) (-3, 1) - det (pA1 t t) (-6, 7)"
  proof (rule dd_lo_eq[where k = "2 * t + 10"])
    show "t + 3 \<le> t + 7" by simp
    show "2 * t + 10 = t + 3 + (t + 7)" by simp
    show "VA t ! (t + 3) = pA1 t t" by (rule A_P1) auto
    show "VA t ! (2 * t + 10) = (-6, 7)" by (subst A_F2[where r = 0]) auto
    show "VB t ! (t + 3) = pB1 t t" by (rule B_P1) auto
    show "VB t ! (2 * t + 10) = (-3, 1)" by (subst B_F2[where r = 0]) auto
  qed
  then show ?thesis by (simp add: det_def pA1_def pB1_def algebra_simps)
qed

lemma dd_F1_0: "dd t (t + 4) = 1"
proof -
  have "dd t (t + 4) = det (-1, 1) (-7, 2) - det (-3, 4) (-7, 8)"
  proof (rule dd_lo_eq[where k = "2 * t + 11"])
    show "t + 4 \<le> t + 7" by simp
    show "2 * t + 11 = t + 4 + (t + 7)" by simp
    show "VA t ! (t + 4) = (-3, 4)" by (subst A_F1[where r = 0]) auto
    show "VA t ! (2 * t + 11) = (-7, 8)" by (subst A_F2[where r = 1]) auto
    show "VB t ! (t + 4) = (-1, 1)" by (subst B_F1[where r = 0]) auto
    show "VB t ! (2 * t + 11) = (-7, 2)" by (subst B_F2[where r = 1]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_F1_1: "dd t (t + 5) = 1"
proof -
  have "dd t (t + 5) = det (-2, 1) (-11, 3) - det (-4, 5) (-8, 9)"
  proof (rule dd_lo_eq[where k = "2 * t + 12"])
    show "t + 5 \<le> t + 7" by simp
    show "2 * t + 12 = t + 5 + (t + 7)" by simp
    show "VA t ! (t + 5) = (-4, 5)" by (subst A_F1[where r = 1]) auto
    show "VA t ! (2 * t + 12) = (-8, 9)" by (subst A_F2[where r = 2]) auto
    show "VB t ! (t + 5) = (-2, 1)" by (subst B_F1[where r = 1]) auto
    show "VB t ! (2 * t + 12) = (-11, 3)" by (subst B_F2[where r = 2]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_F1_2: "dd t (t + 6) = 1"
proof -
  have "dd t (t + 6) = det (-5, 2) (-15, 4) - det (-9, 11) (-9, 10)"
  proof (rule dd_lo_eq[where k = "2 * t + 13"])
    show "t + 6 \<le> t + 7" by simp
    show "2 * t + 13 = t + 6 + (t + 7)" by simp
    show "VA t ! (t + 6) = (-9, 11)" by (subst A_F1[where r = 2]) auto
    show "VA t ! (2 * t + 13) = (-9, 10)" by (subst A_F2[where r = 3]) auto
    show "VB t ! (t + 6) = (-5, 2)" by (subst B_F1[where r = 2]) auto
    show "VB t ! (2 * t + 13) = (-15, 4)" by (subst B_F2[where r = 3]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_F1_3: "dd t (t + 7) = 9"
proof -
  have "dd t (t + 7) = det (-18, 7) (-4, 1) - det (-5, 6) (-1, 1)"
  proof (rule dd_lo_eq[where k = "2 * t + 14"])
    show "t + 7 \<le> t + 7" by simp
    show "2 * t + 14 = t + 7 + (t + 7)" by simp
    show "VA t ! (t + 7) = (-5, 6)" by (subst A_F1[where r = 3]) auto
    show "VA t ! (2 * t + 14) = (-1, 1)" by (subst A_F2[where r = 4]) auto
    show "VB t ! (t + 7) = (-18, 7)" by (subst B_F1[where r = 3]) auto
    show "VB t ! (2 * t + 14) = (-4, 1)" by (subst B_F2[where r = 4]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_h0: "dd t (t + 8) = -8"
proof -
  have "dd t (t + 8) = det (1, 0) (-13, 5) - det (1, 0) (-11, 13)"
  proof (rule dd_hi_eq[where j = 0])
    show "t + 7 < t + 8" by simp
    show "t + 8 = 0 + (t + 8)" by simp
    show "VA t ! 0 = (1, 0)" by (subst A_F0) auto
    show "VA t ! (t + 8) = (-11, 13)" by (subst A_F1[where r = 4]) auto
    show "VB t ! 0 = (1, 0)" by (subst B_F0) auto
    show "VB t ! (t + 8) = (-13, 5)" by (subst B_F1[where r = 4]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_h1: "dd t (t + 9) = 2 * int t - 9"
proof -
  have "dd t (t + 9) = det (0, 1) (pB2 t 0) - det (0, 1) (pA2 t 0)"
  proof (rule dd_hi_eq[where j = 1])
    show "t + 7 < t + 9" by simp
    show "t + 9 = 1 + (t + 8)" by simp
    show "VA t ! 1 = (0, 1)" by (subst A_F0) auto
    show "VA t ! (t + 9) = pA2 t 0" by (rule A_P2) auto
    show "VB t ! 1 = (0, 1)" by (subst B_F0) auto
    show "VB t ! (t + 9) = pB2 t 0" by (rule B_P2) auto
  qed
  then show ?thesis by (simp add: det_def pA2_def pB2_def algebra_simps)
qed

lemma dd_h2: "1 \<le> t \<Longrightarrow> dd t (t + 10) = 25 * int t - 18"
proof -
  assume t1: "1 \<le> t"
  have "dd t (t + 10) = det (-1, 3) (pB2 t 1) - det (-1, 2) (pA2 t 1)"
  proof (rule dd_hi_eq[where j = 2])
    show "t + 7 < t + 10" by simp
    show "t + 10 = 2 + (t + 8)" by simp
    show "VA t ! 2 = (-1, 2)" by (subst A_F0) auto
    show "VA t ! (t + 10) = pA2 t 1" by (rule A_P2) (use t1 in auto)
    show "VB t ! 2 = (-1, 3)" by (subst B_F0) auto
    show "VB t ! (t + 10) = pB2 t 1" by (rule B_P2) (use t1 in auto)
  qed
  then show ?thesis by (simp add: det_def pA2_def pB2_def algebra_simps)
qed

lemma dd_c2:
  assumes "s + 2 \<le> t"
  shows "dd t (t + 11 + s) = 25 * (int t - int s)\<^sup>2 - 29 * (int t - int s) - 26"
proof -
  have "dd t (t + 11 + s) = det (pB1 t s) (pB2 t (s + 2)) - det (pA1 t s) (pA2 t (s + 2))"
  proof (rule dd_hi_eq[where j = "s + 3"])
    show "t + 7 < t + 11 + s" by simp
    show "t + 11 + s = s + 3 + (t + 8)" by simp
    show "VA t ! (s + 3) = pA1 t s" using assms by (intro A_P1) auto
    show "VA t ! (t + 11 + s) = pA2 t (s + 2)" using assms by (intro A_P2) auto
    show "VB t ! (s + 3) = pB1 t s" using assms by (intro B_P1) auto
    show "VB t ! (t + 11 + s) = pB2 t (s + 2)" using assms by (intro B_P2) auto
  qed
  then show ?thesis by (simp add: det_def pA1_def pA2_def pB1_def pB2_def algebra_simps power2_eq_square)
qed

lemma dd_c2_pos:
  assumes "s + 2 \<le> t"
  shows "0 < dd t (t + 11 + s)"
proof -
  have u: "2 \<le> int t - int s" using assms by simp
  have "0 < 25 * (int t - int s)\<^sup>2 - 29 * (int t - int s) - 26"
    by (rule poly2) (use u in simp)
  then show ?thesis using dd_c2[OF assms] by simp
qed

lemma dd_h_end0: "5 \<le> t \<Longrightarrow> dd t (2 * t + 10) = 4"
proof -
  assume t5: "5 \<le> t"
  obtain m where tm: "t = Suc m" using t5 by (cases t) auto
  have "dd t (2 * t + 10) = det (pB1 t m) (-3, 1) - det (pA1 t m) (-6, 7)"
  proof (rule dd_hi_eq[where j = "t + 2"])
    show "t + 7 < 2 * t + 10" by simp
    show "2 * t + 10 = t + 2 + (t + 8)" by simp
    show "VA t ! (t + 2) = pA1 t m" using tm by (intro A_P1) auto
    show "VA t ! (2 * t + 10) = (-6, 7)" by (subst A_F2[where r = 0]) auto
    show "VB t ! (t + 2) = pB1 t m" using tm by (intro B_P1) auto
    show "VB t ! (2 * t + 10) = (-3, 1)" by (subst B_F2[where r = 0]) auto
  qed
  then show ?thesis by (simp add: det_def pA1_def pB1_def algebra_simps tm)
qed

lemma dd_h_end1: "dd t (2 * t + 11) = 7"
proof -
  have "dd t (2 * t + 11) = det (pB1 t t) (-7, 2) - det (pA1 t t) (-7, 8)"
  proof (rule dd_hi_eq[where j = "t + 3"])
    show "t + 7 < 2 * t + 11" by simp
    show "2 * t + 11 = t + 3 + (t + 8)" by simp
    show "VA t ! (t + 3) = pA1 t t" by (rule A_P1) auto
    show "VA t ! (2 * t + 11) = (-7, 8)" by (subst A_F2[where r = 1]) auto
    show "VB t ! (t + 3) = pB1 t t" by (rule B_P1) auto
    show "VB t ! (2 * t + 11) = (-7, 2)" by (subst B_F2[where r = 1]) auto
  qed
  then show ?thesis by (simp add: det_def pA1_def pB1_def algebra_simps)
qed

lemma dd_h_f0: "dd t (2 * t + 12) = 3"
proof -
  have "dd t (2 * t + 12) = det (-1, 1) (-11, 3) - det (-3, 4) (-8, 9)"
  proof (rule dd_hi_eq[where j = "t + 4"])
    show "t + 7 < 2 * t + 12" by simp
    show "2 * t + 12 = t + 4 + (t + 8)" by simp
    show "VA t ! (t + 4) = (-3, 4)" by (subst A_F1[where r = 0]) auto
    show "VA t ! (2 * t + 12) = (-8, 9)" by (subst A_F2[where r = 2]) auto
    show "VB t ! (t + 4) = (-1, 1)" by (subst B_F1[where r = 0]) auto
    show "VB t ! (2 * t + 12) = (-11, 3)" by (subst B_F2[where r = 2]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_h_f1: "dd t (2 * t + 13) = 2"
proof -
  have "dd t (2 * t + 13) = det (-2, 1) (-15, 4) - det (-4, 5) (-9, 10)"
  proof (rule dd_hi_eq[where j = "t + 5"])
    show "t + 7 < 2 * t + 13" by simp
    show "2 * t + 13 = t + 5 + (t + 8)" by simp
    show "VA t ! (t + 5) = (-4, 5)" by (subst A_F1[where r = 1]) auto
    show "VA t ! (2 * t + 13) = (-9, 10)" by (subst A_F2[where r = 3]) auto
    show "VB t ! (t + 5) = (-2, 1)" by (subst B_F1[where r = 1]) auto
    show "VB t ! (2 * t + 13) = (-15, 4)" by (subst B_F2[where r = 3]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

lemma dd_h_f2: "dd t (2 * t + 14) = 1"
proof -
  have "dd t (2 * t + 14) = det (-5, 2) (-4, 1) - det (-9, 11) (-1, 1)"
  proof (rule dd_hi_eq[where j = "t + 6"])
    show "t + 7 < 2 * t + 14" by simp
    show "2 * t + 14 = t + 6 + (t + 8)" by simp
    show "VA t ! (t + 6) = (-9, 11)" by (subst A_F1[where r = 2]) auto
    show "VA t ! (2 * t + 14) = (-1, 1)" by (subst A_F2[where r = 4]) auto
    show "VB t ! (t + 6) = (-5, 2)" by (subst B_F1[where r = 2]) auto
    show "VB t ! (2 * t + 14) = (-4, 1)" by (subst B_F2[where r = 4]) auto
  qed
  then show ?thesis by (simp add: det_def)
qed

text \<open>The single negative entry, for every $t$: $5 - 13 = -8$.\<close>

lemma dd_neg: "dd t (t + 8) = -8"
  by (rule dd_h0)

text \<open>For $t \geq 5$ every other entry is positive. Writing $u = t - s$, the two long classes give
  $25u^2 - 4u - 12$ ($u \geq 1$) and $25u^2 - 29u - 26$ ($u \geq 2$); the entry next to the negative one is
  $2t - 9$.\<close>

lemma dd_pos: "5 \<le> t \<Longrightarrow> i < 15 + 2 * t \<Longrightarrow> i \<noteq> t + 8 \<Longrightarrow> 0 < dd t i"
proof -
  assume t5: "5 \<le> t" and il: "i < 15 + 2 * t" and ne: "i \<noteq> t + 8"
  show ?thesis
  proof (cases "i \<le> t + 7")
    case True
    have cs: "i = 0 \<or> i = 1 \<or> i = 2 \<or> (3 \<le> i \<and> i < t + 3) \<or> i = t + 3 \<or> i = t + 4 \<or> i = t + 5
      \<or> i = t + 6 \<or> i = t + 7" using True by presburger
    then show ?thesis
    proof (elim disjE)
      assume "i = 0" then show ?thesis by (simp add: dd_0)
    next
      assume h1: "i = 1" then show ?thesis by (subst h1, subst dd_1, simp)
    next
      assume "i = 2" then show ?thesis using dd_2 t5 by simp
    next
      assume c: "3 \<le> i \<and> i < t + 3"
      have e: "i - 3 + 3 = i" using c by presburger
      have "0 < dd t (i - 3 + 3)" using c by (intro dd_c1_pos) auto
      then show ?thesis by (simp only: e)
    next
      assume "i = t + 3" then show ?thesis by (simp add: dd_3t)
    next
      assume "i = t + 4" then show ?thesis by (simp add: dd_F1_0)
    next
      assume "i = t + 5" then show ?thesis by (simp add: dd_F1_1)
    next
      assume "i = t + 6" then show ?thesis by (simp add: dd_F1_2)
    next
      assume "i = t + 7" then show ?thesis by (simp add: dd_F1_3)
    qed
  next
    case False
    have cs: "i = t + 9 \<or> i = t + 10 \<or> (t + 11 \<le> i \<and> i < 2 * t + 10) \<or> i = 2 * t + 10
      \<or> i = 2 * t + 11 \<or> i = 2 * t + 12 \<or> i = 2 * t + 13 \<or> i = 2 * t + 14"
      using False il ne by presburger
    then show ?thesis
    proof (elim disjE)
      assume "i = t + 9" then show ?thesis using dd_h1 t5 by simp
    next
      assume "i = t + 10" then show ?thesis using dd_h2[of t] t5 by simp
    next
      assume c: "t + 11 \<le> i \<and> i < 2 * t + 10"
      have e: "t + 11 + (i - (t + 11)) = i" using c by presburger
      have "0 < dd t (t + 11 + (i - (t + 11)))" using c by (intro dd_c2_pos) auto
      then show ?thesis by (simp only: e)
    next
      assume "i = 2 * t + 10" then show ?thesis using dd_h_end0 t5 by simp
    next
      assume "i = 2 * t + 11" then show ?thesis by (simp add: dd_h_end1)
    next
      assume "i = 2 * t + 12" then show ?thesis by (simp add: dd_h_f0)
    next
      assume "i = 2 * t + 13" then show ?thesis by (simp add: dd_h_f1)
    next
      assume "i = 2 * t + 14" then show ?thesis by (simp add: dd_h_f2)
    qed
  qed
qed

lemma sign_changes_one_negative:
  assumes "0 < p" "Suc p < n" "d p < 0" "\<And>i. i < n \<Longrightarrow> i \<noteq> p \<Longrightarrow> 0 < d i"
  shows "sign_changes d n = 2"
proof -
  have S: "{i. i < n \<and> d i * d (Suc i mod n) < 0} = {p - 1, p}"
  proof (rule set_eqI)
    fix i
    show "i \<in> {i. i < n \<and> d i * d (Suc i mod n) < 0} \<longleftrightarrow> i \<in> {p - 1, p}"
    proof
      assume H: "i \<in> {i. i < n \<and> d i * d (Suc i mod n) < 0}"
      then have in_: "i < n" and neg: "d i * d (Suc i mod n) < 0" by simp_all
      show "i \<in> {p - 1, p}"
      proof (rule ccontr)
        assume "i \<notin> {p - 1, p}"
        then have ip: "i \<noteq> p" and ip1: "i \<noteq> p - 1" by simp_all
        have di: "0 < d i" using assms(4) in_ ip by blast
        have "0 < d (Suc i mod n)"
        proof (cases "Suc i < n")
          case True
          then have "Suc i mod n = Suc i" by simp
          moreover have "Suc i \<noteq> p" using ip1 assms(1) by linarith
          ultimately show ?thesis using assms(4) True by simp
        next
          case False
          then have "Suc i = n" using in_ by simp
          then have "Suc i mod n = 0" using assms(1,2) by simp
          then show ?thesis using assms(4)[of 0] assms(1,2) by simp
        qed
        then have "0 < d i * d (Suc i mod n)" using di by (simp add: zero_less_mult_iff)
        then show False using neg by linarith
      qed
    next
      assume H: "i \<in> {p - 1, p}"
      then consider "i = p - 1" | "i = p" by auto
      then show "i \<in> {i. i < n \<and> d i * d (Suc i mod n) < 0}"
      proof cases
        case 1
        then have i1: "Suc i = p" using assms(1) by simp
        have "0 < d i" using assms(4)[of i] 1 assms(1,2) by simp
        moreover have "d (Suc i mod n) < 0" using i1 assms(2,3) by simp
        ultimately show ?thesis using 1 assms(1,2) by (simp add: mult_pos_neg)
      next
        case 2
        have "Suc p mod n = Suc p" using assms(2) by simp
        moreover have "0 < d (Suc p)" using assms(4)[of "Suc p"] assms(2) by simp
        ultimately show ?thesis using 2 assms(2,3) by (simp add: mult_neg_pos)
      qed
    qed
  qed
  have "p - 1 \<noteq> p" using assms(1) by simp
  then show ?thesis unfolding sign_changes_def S by simp
qed

lemma small_t: "t \<le> 4 \<Longrightarrow> (\<forall>i < 15 + 2 * t. dd t i \<noteq> 0) \<and> sign_changes (dd t) (15 + 2 * t) = 2"
proof -
  assume "t \<le> 4"
  then consider "t = 0" | "t = 1" | "t = 2" | "t = 3" | "t = 4" by linarith
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      unfolding sign_changes_list ball_list
      by (simp add: dd_def row_entry_def VA_def VB_def pA1_def pA2_def pB1_def pB2_def det_def) code_simp
  next
    case 2 then show ?thesis
      unfolding sign_changes_list ball_list
      by (simp add: dd_def row_entry_def VA_def VB_def pA1_def pA2_def pB1_def pB2_def det_def) code_simp
  next
    case 3 then show ?thesis
      unfolding sign_changes_list ball_list
      by (simp add: dd_def row_entry_def VA_def VB_def pA1_def pA2_def pB1_def pB2_def det_def) code_simp
  next
    case 4 then show ?thesis
      unfolding sign_changes_list ball_list
      by (simp add: dd_def row_entry_def VA_def VB_def pA1_def pA2_def pB1_def pB2_def det_def) code_simp
  next
    case 5 then show ?thesis
      unfolding sign_changes_list ball_list
      by (simp add: dd_def row_entry_def VA_def VB_def pA1_def pA2_def pB1_def pB2_def det_def) code_simp
  qed
qed

section \<open>Main result\<close>

theorem two_sign_changes:
  "frieze (VA t) \<and> frieze (VB t) \<and> length (VA t) = 15 + 2 * t \<and> length (VB t) = 15 + 2 * t \<and>
   (\<forall>i < 15 + 2 * t. dd t i \<noteq> 0) \<and> sign_changes (dd t) (15 + 2 * t) = 2"
proof -
  have R: "(\<forall>i < 15 + 2 * t. dd t i \<noteq> 0) \<and> sign_changes (dd t) (15 + 2 * t) = 2"
  proof (cases "t \<le> 4")
    case True
    then show ?thesis by (rule small_t)
  next
    case False
    then have t5: "5 \<le> t" by simp
    have nz: "\<forall>i < 15 + 2 * t. dd t i \<noteq> 0"
    proof (intro allI impI)
      fix i assume i: "i < 15 + 2 * t"
      show "dd t i \<noteq> 0"
      proof (cases "i = t + 8")
        case True then show ?thesis using dd_neg by simp
      next
        case False then show ?thesis using dd_pos[OF t5 i] by simp
      qed
    qed
    have "sign_changes (dd t) (15 + 2 * t) = 2"
      by (rule sign_changes_one_negative[where p = "t + 8"])
         (use dd_neg dd_pos[OF t5] in auto)
    with nz show ?thesis by simp
  qed
  show ?thesis using R frieze_VA frieze_VB by simp
qed

text \<open>The row is row $\lfloor w/2 \rfloor$, $w = n - 3$: \<open>length (VA t) div 2 - 1 = (length (VA t) - 3) div 2\<close>.\<close>

lemma row_index: "length (VA t) div 2 - 1 = (length (VA t) - 3) div 2"
  by simp

text \<open>Control: the counter of sign changes is not degenerate; an alternating sequence of length $4$ has four.\<close>

lemma "sign_changes (\<lambda>i. if even i then 1 else -1) 4 = 4"
  unfolding sign_changes_list by code_simp

end
