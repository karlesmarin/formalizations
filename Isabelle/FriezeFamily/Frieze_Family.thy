(*  Title:      Frieze_Family.thy
    Author:     Carles Marín

For every even n >= 14, two integer Conway-Coxeter frieze patterns of width n - 3 whose middle rows (the
diameters of the n-gon) are strictly ordered at every position.

Model. An integer Conway-Coxeter frieze of width n - 3 is the same as a list of lattice vectors
V_0, ..., V_(n-1) in Z^2 with det (V_i, V_(i+1)) = 1, det (V_0, V_(n-1)) = 1 and det (V_i, V_j) > 0 for
i < j (a lattice polygon turning half a turn); its entries are m (i, j) = det (V_i, V_j) and its quiddity is
a_i = det (V_(i-1), V_(i+1)). Inserting V_j + V_(j+1) between V_j and V_(j+1) is inserting an ear in the
triangulation. With n = 2h, the middle row is the row of the diameters det (V_i, V_(i+h)), i < h.

S. Tabachnikov (Math. Intelligencer 40 (2018), Problem 1) asks whether the cyclic sequence of differences of a
row of two friezes must change sign at least four times; M. Cuntz gave a rational counterexample (width 5,
middle row) and the integer case was left open. Here the differences have no sign change at all.
*)

theory Frieze_Family
  imports Main
begin

section \<open>Lattice vectors\<close>

type_synonym vec = "int \<times> int"

definition det :: "vec \<Rightarrow> vec \<Rightarrow> int" where
  "det u v = fst u * snd v - snd u * fst v"

definition vadd :: "vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vadd u v = (fst u + fst v, snd u + snd v)"

lemma det_vadd_right: "det u (vadd v w) = det u v + det u w"
  by (simp add: det_def vadd_def algebra_simps)

lemma det_vadd_left: "det (vadd v w) u = det v u + det w u"
  by (simp add: det_def vadd_def algebra_simps)

lemma det_self [simp]: "det u u = 0"
  by (simp add: det_def)

section \<open>Friezes as lattice polygons\<close>

definition frieze :: "vec list \<Rightarrow> bool" where
  "frieze V \<longleftrightarrow> 3 \<le> length V \<and>
     (\<forall>j < length V. \<forall>i < j. 0 < det (V ! i) (V ! j)) \<and>
     (\<forall>i < length V - 1. det (V ! i) (V ! Suc i) = 1) \<and>
     det (V ! 0) (V ! (length V - 1)) = 1"

text \<open>Insert an ear after position \<open>j\<close>.\<close>

definition ins :: "vec list \<Rightarrow> nat \<Rightarrow> vec list" where
  "ins V j = take (Suc j) V @ [vadd (V ! j) (V ! Suc j)] @ drop (Suc j) V"

lemma length_ins [simp]: "Suc j < length V \<Longrightarrow> length (ins V j) = Suc (length V)"
  by (simp add: ins_def)

lemma nth_ins:
  assumes "Suc j < length V" "k < Suc (length V)"
  shows "ins V j ! k =
    (if k \<le> j then V ! k else if k = Suc j then vadd (V ! j) (V ! Suc j) else V ! (k - 1))"
proof -
  have lt: "length (take (Suc j) V) = Suc j" using assms(1) by simp
  consider "k \<le> j" | "k = Suc j" | "Suc j < k" by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using assms by (simp add: ins_def nth_append)
  next
    case 2
    then show ?thesis using assms by (simp add: ins_def nth_append)
  next
    case 3
    then have "ins V j ! k = drop (Suc j) V ! (k - Suc j - 1)"
      using assms by (simp add: ins_def nth_append)
    also have "\<dots> = V ! (Suc j + (k - Suc j - 1))"
      using 3 assms by (subst nth_drop) auto
    also have "Suc j + (k - Suc j - 1) = k - 1" using 3 by simp
    finally show ?thesis using 3 by simp
  qed
qed

lemma ins_frieze:
  assumes F: "frieze V" and j: "Suc j < length V"
  shows "frieze (ins V j)"
proof -
  let ?n = "length V"
  let ?W = "ins V j"
  let ?w = "vadd (V ! j) (V ! Suc j)"
  have pos: "\<And>i k. i < k \<Longrightarrow> k < ?n \<Longrightarrow> 0 < det (V ! i) (V ! k)"
    using F by (simp add: frieze_def)
  have one: "\<And>i. Suc i < ?n \<Longrightarrow> det (V ! i) (V ! Suc i) = 1"
    using F by (simp add: frieze_def)
  have nonneg: "\<And>i k. i \<le> k \<Longrightarrow> k < ?n \<Longrightarrow> 0 \<le> det (V ! i) (V ! k)"
    by (metis det_self le_neq_implies_less less_imp_le pos order_refl)
  have P: "0 < det (?W ! i) (?W ! k)" if ik: "i < k" "k < Suc ?n" for i k
  proof -
    have i_lt: "i < Suc ?n" using ik by simp
    consider "k \<le> j" | "i \<le> j" "k = Suc j" | "i \<le> j" "Suc j < k" | "i = Suc j" "Suc j < k"
      | "Suc j < i" using ik by linarith
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using ik j by (simp add: nth_ins pos)
    next
      case 2
      then have "det (?W ! i) (?W ! k) = det (V ! i) (V ! j) + det (V ! i) (V ! Suc j)"
        using ik j by (simp add: nth_ins det_vadd_right)
      moreover have "0 \<le> det (V ! i) (V ! j)" using 2 j by (intro nonneg) auto
      moreover have "0 < det (V ! i) (V ! Suc j)" using 2 j by (intro pos) auto
      ultimately show ?thesis by linarith
    next
      case 3
      then show ?thesis using ik j by (simp add: nth_ins pos)
    next
      case 4
      then have "det (?W ! i) (?W ! k) = det (V ! j) (V ! (k - 1)) + det (V ! Suc j) (V ! (k - 1))"
        using ik j by (simp add: nth_ins det_vadd_left)
      moreover have "0 < det (V ! j) (V ! (k - 1))" using 4 ik by (intro pos) auto
      moreover have "0 \<le> det (V ! Suc j) (V ! (k - 1))" using 4 ik by (intro nonneg) auto
      ultimately show ?thesis by linarith
    next
      case 5
      then show ?thesis using ik j by (simp add: nth_ins pos)
    qed
  qed
  have O: "det (?W ! i) (?W ! Suc i) = 1" if i: "Suc i < Suc ?n" for i
  proof -
    consider "Suc i \<le> j" | "i = j" | "i = Suc j" | "Suc j < i" by linarith
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using i j by (simp add: nth_ins one)
    next
      case 2
      then show ?thesis using j by (simp add: nth_ins det_vadd_right one)
    next
      case 3
      then show ?thesis using j by (simp add: nth_ins det_vadd_left one)
    next
      case 4
      then have w: "?W ! i = V ! (i - 1)" "?W ! Suc i = V ! i"
        using i j by (simp_all add: nth_ins)
      have "det (V ! (i - 1)) (V ! Suc (i - 1)) = 1" using one[of "i - 1"] 4 i by simp
      moreover have "Suc (i - 1) = i" using 4 by simp
      ultimately show ?thesis using w by simp
    qed
  qed
  have E: "det (?W ! 0) (?W ! (length ?W - 1)) = 1"
  proof -
    have "?W ! 0 = V ! 0" using j by (simp add: nth_ins)
    moreover have "?W ! (length ?W - 1) = V ! (?n - 1)" using j by (simp add: nth_ins)
    ultimately show ?thesis using F by (simp add: frieze_def)
  qed
  have len: "length ?W = Suc ?n" using j by simp
  have P': "\<forall>k < length ?W. \<forall>i < k. 0 < det (?W ! i) (?W ! k)" using P len by auto
  have O': "\<forall>i < length ?W - 1. det (?W ! i) (?W ! Suc i) = 1" using O len by auto
  show ?thesis using F len P' O' E unfolding frieze_def by simp
qed

section \<open>Antipodal ear insertion and the diameters\<close>

definition ins2 :: "vec list \<Rightarrow> nat \<Rightarrow> vec list" where
  "ins2 V j = ins (ins V (j + length V div 2)) j"

definition dia :: "vec list \<Rightarrow> nat \<Rightarrow> int" where
  "dia V i = det (V ! i) (V ! (i + length V div 2))"

text \<open>The value of the new diameter, between the two inserted vectors.\<close>

definition S :: "vec list \<Rightarrow> nat \<Rightarrow> int" where
  "S V j = det (vadd (V ! j) (V ! Suc j)) (vadd (V ! (j + length V div 2)) (V ! Suc (j + length V div 2)))"

lemma ins2_facts:
  assumes "even (length V)" "Suc j < length V div 2"
  defines "h \<equiv> length V div 2"
  shows "length (ins2 V j) = length V + 2"
    and "\<And>k. k \<le> j \<Longrightarrow> ins2 V j ! k = V ! k"
    and "ins2 V j ! Suc j = vadd (V ! j) (V ! Suc j)"
    and "\<And>k. Suc j < k \<Longrightarrow> k \<le> Suc (j + h) \<Longrightarrow> ins2 V j ! k = V ! (k - 1)"
    and "ins2 V j ! (j + h + 2) = vadd (V ! (j + h)) (V ! Suc (j + h))"
    and "\<And>k. j + h + 2 < k \<Longrightarrow> k < length V + 2 \<Longrightarrow> ins2 V j ! k = V ! (k - 2)"
proof -
  have n: "Suc (j + h) < length V" using assms(2) unfolding h_def by linarith
  have jh: "Suc j < h" using assms(2) unfolding h_def .
  let ?U = "ins V (j + h)"
  have lU: "length ?U = Suc (length V)" using n by simp
  have jU: "Suc j < length ?U" using n lU by linarith
  have U_nth: "\<And>k. k < Suc (length V) \<Longrightarrow> ?U ! k =
      (if k \<le> j + h then V ! k else if k = Suc (j + h) then vadd (V ! (j + h)) (V ! Suc (j + h)) else V ! (k - 1))"
    using n by (simp add: nth_ins)
  have W_nth: "\<And>k. k < Suc (length ?U) \<Longrightarrow> ins2 V j ! k =
      (if k \<le> j then ?U ! k else if k = Suc j then vadd (?U ! j) (?U ! Suc j) else ?U ! (k - 1))"
    using jU unfolding ins2_def h_def by (simp add: nth_ins)
  show "length (ins2 V j) = length V + 2" using jU lU unfolding ins2_def h_def by simp
  show "\<And>k. k \<le> j \<Longrightarrow> ins2 V j ! k = V ! k" using W_nth U_nth n lU jh by auto
  show "ins2 V j ! Suc j = vadd (V ! j) (V ! Suc j)" using W_nth U_nth n lU jh by auto
  show "\<And>k. Suc j < k \<Longrightarrow> k \<le> Suc (j + h) \<Longrightarrow> ins2 V j ! k = V ! (k - 1)"
    using W_nth U_nth n lU jh by auto
  show "ins2 V j ! (j + h + 2) = vadd (V ! (j + h)) (V ! Suc (j + h))"
    using W_nth U_nth n lU jh by auto
  show "\<And>k. j + h + 2 < k \<Longrightarrow> k < length V + 2 \<Longrightarrow> ins2 V j ! k = V ! (k - 2)"
    using W_nth U_nth n lU jh by (auto simp: numeral_2_eq_2)
qed

lemma ins2_frieze:
  assumes "frieze V" "even (length V)" "Suc j < length V div 2"
  shows "frieze (ins2 V j)"
proof -
  have n: "Suc (j + length V div 2) < length V" using assms(2,3) by linarith
  have F1: "frieze (ins V (j + length V div 2))" using assms(1) n by (rule ins_frieze)
  have "Suc j < length (ins V (j + length V div 2))" using n by simp
  then show ?thesis using F1 unfolding ins2_def by (rule ins_frieze[rotated])
qed

lemma dia_ins2:
  assumes ev: "even (length V)" and j: "Suc j < length V div 2" and i: "i < Suc (length V div 2)"
  shows "dia (ins2 V j) i =
    (if i \<le> j then dia V i else if i = Suc j then S V j else dia V (i - 1))"
proof -
  define h where "h = length V div 2"
  have L: "length (ins2 V j) = length V + 2" using ins2_facts(1)[OF ev j] .
  have hh: "length (ins2 V j) div 2 = Suc h" using L ev unfolding h_def by auto
  note fa = ins2_facts[OF ev j, folded h_def]
  have jh: "Suc j < h" using j unfolding h_def .
  consider "i \<le> j" | "i = Suc j" | "Suc j < i" by linarith
  then show ?thesis
  proof cases
    case 1
    then have "ins2 V j ! i = V ! i" "ins2 V j ! (i + Suc h) = V ! (i + h)"
      using fa(2) fa(4)[of "i + Suc h"] jh by auto
    then show ?thesis using 1 hh unfolding dia_def h_def by simp
  next
    case 2
    then have "ins2 V j ! i = vadd (V ! j) (V ! Suc j)"
      "ins2 V j ! (i + Suc h) = vadd (V ! (j + h)) (V ! Suc (j + h))"
      using fa(3) fa(5) by (simp_all add: add.commute add.left_commute)
    then show ?thesis using 2 hh unfolding dia_def S_def h_def by simp
  next
    case 3
    have ih: "i \<le> h" using i unfolding h_def by simp
    have A: "ins2 V j ! i = V ! (i - 1)" using fa(4)[of i] 3 ih by auto
    have B: "ins2 V j ! (i + Suc h) = V ! (i + Suc h - 2)"
      using fa(6)[of "i + Suc h"] 3 ih ev unfolding h_def by auto
    have "i + Suc h - 2 = (i - 1) + h" using 3 by simp
    then show ?thesis using 3 A B hh unfolding dia_def h_def by simp
  qed
qed

definition dominated :: "vec list \<Rightarrow> vec list \<Rightarrow> bool" where
  "dominated V W \<longleftrightarrow> length V = length W \<and> (\<forall>i < length V div 2. dia V i < dia W i)"

lemma dominated_ins2:
  assumes D: "dominated V W" and ev: "even (length V)" and j: "Suc j < length V div 2"
    and SS: "S V j < S W j"
  shows "dominated (ins2 V j) (ins2 W j)"
proof -
  have lW: "length W = length V" using D by (simp add: dominated_def)
  have evW: "even (length W)" and jW: "Suc j < length W div 2" using ev j lW by simp_all
  have LV: "length (ins2 V j) = length V + 2" using ins2_facts(1)[OF ev j] .
  have LW: "length (ins2 W j) = length V + 2" using ins2_facts(1)[OF evW jW] lW by simp
  have d: "\<And>i. i < length V div 2 \<Longrightarrow> dia V i < dia W i" using D by (simp add: dominated_def)
  have "dia (ins2 V j) i < dia (ins2 W j) i" if i: "i < length (ins2 V j) div 2" for i
  proof -
    have i': "i < Suc (length V div 2)" using i LV ev by auto
    have i'': "i < Suc (length W div 2)" using i' lW by simp
    show ?thesis
      using dia_ins2[OF ev j i'] dia_ins2[OF evW jW i''] d SS j i' lW by auto
  qed
  then show ?thesis using LV LW by (simp add: dominated_def)
qed

section \<open>The two base friezes (n = 14) and the family\<close>

text \<open>Quiddities (1,2,2,2,2,3,1,3,2,2,2,2,1,11) and (1,5,2,3,1,2,5,4,1,2,2,4,2,2), as lattice polygons
  with V_0 = (1,0), V_1 = (0,1) and V_(i+1) = a_i V_i - V_(i-1).\<close>

definition A0 :: "vec list" where
  "A0 = [(1, 0), (0, 1), (-1, 2), (-2, 3), (-3, 4), (-4, 5), (-9, 11), (-5, 6), (-6, 7), (-7, 8), (-8, 9),
         (-9, 10), (-10, 11), (-1, 1)]"

definition B0 :: "vec list" where
  "B0 = [(1, 0), (0, 1), (-1, 5), (-2, 9), (-5, 22), (-3, 13), (-1, 4), (-2, 7), (-7, 24), (-5, 17), (-3, 10),
         (-1, 3), (-1, 2), (-1, 1)]"

lemma frieze_A0: "frieze A0"
  unfolding frieze_def A0_def det_def by code_simp

lemma frieze_B0: "frieze B0"
  unfolding frieze_def B0_def det_def by code_simp

lemma dominated_0: "dominated A0 B0"
  unfolding dominated_def dia_def A0_def B0_def det_def by code_simp

text \<open>Negative control: the order is not the other way round.\<close>

lemma not_dominated_0: "\<not> dominated B0 A0"
  unfolding dominated_def dia_def A0_def B0_def det_def by code_simp

definition FA :: "nat \<Rightarrow> vec list" where "FA t = ((\<lambda>V. ins2 V 0) ^^ t) A0"
definition FB :: "nat \<Rightarrow> vec list" where "FB t = ((\<lambda>V. ins2 V 0) ^^ t) B0"

text \<open>Invariants of the insertion at \<open>j = 0\<close>: \<open>V_0\<close> and \<open>V_h\<close> stay, \<open>V_1\<close> and \<open>V_(h+1)\<close> move by
  \<open>V_0\<close> and \<open>V_h\<close>.\<close>

definition vsmul :: "int \<Rightarrow> vec \<Rightarrow> vec" where "vsmul c u = (c * fst u, c * snd u)"

lemma family:
  assumes F: "frieze V0" and L: "length V0 = 14"
  shows "frieze (((\<lambda>V. ins2 V 0) ^^ t) V0) \<and> length (((\<lambda>V. ins2 V 0) ^^ t) V0) = 14 + 2 * t \<and>
    ((\<lambda>V. ins2 V 0) ^^ t) V0 ! 0 = V0 ! 0 \<and>
    ((\<lambda>V. ins2 V 0) ^^ t) V0 ! 1 = vadd (V0 ! 1) (vsmul (int t) (V0 ! 0)) \<and>
    ((\<lambda>V. ins2 V 0) ^^ t) V0 ! (7 + t) = V0 ! 7 \<and>
    ((\<lambda>V. ins2 V 0) ^^ t) V0 ! (8 + t) = vadd (V0 ! 8) (vsmul (int t) (V0 ! 7))"
proof (induction t)
  case 0
  then show ?case using F L by (simp add: vadd_def vsmul_def)
next
  case (Suc t)
  let ?V = "((\<lambda>V. ins2 V 0) ^^ t) V0"
  have ev: "even (length ?V)" and j: "Suc 0 < length ?V div 2" using Suc.IH by auto
  have h: "length ?V div 2 = 7 + t" using Suc.IH by simp
  note fa = ins2_facts[OF ev j]
  have "frieze (ins2 ?V 0)" using ins2_frieze Suc.IH ev j by blast
  moreover have "length (ins2 ?V 0) = 14 + 2 * Suc t" using fa(1) Suc.IH by simp
  moreover have "ins2 ?V 0 ! 0 = V0 ! 0" using fa(2)[of 0] Suc.IH by simp
  moreover have "ins2 ?V 0 ! 1 = vadd (V0 ! 1) (vsmul (int (Suc t)) (V0 ! 0))"
    using fa(3) Suc.IH by (simp add: vadd_def vsmul_def algebra_simps)
  moreover have "ins2 ?V 0 ! (7 + Suc t) = V0 ! 7"
    using fa(4)[of "7 + Suc t"] h Suc.IH by simp
  moreover have "ins2 ?V 0 ! (8 + Suc t) = vadd (V0 ! 8) (vsmul (int (Suc t)) (V0 ! 7))"
    using fa(5) h Suc.IH by (simp add: vadd_def vsmul_def algebra_simps)
  ultimately show ?case by simp
qed

lemma S_poly:
  "det (vadd x0 (vadd x1 (vsmul s x0))) (vadd y0 (vadd y1 (vsmul s y0))) =
     (s + 1)^2 * det x0 y0 + (s + 1) * (det x0 y1 + det x1 y0) + det x1 y1"
  by (cases x0; cases x1; cases y0; cases y1) (simp add: det_def vadd_def vsmul_def power2_eq_square algebra_simps)

lemma S_family:
  assumes F: "frieze V0" and L: "length V0 = 14"
  shows "S (((\<lambda>V. ins2 V 0) ^^ t) V0) 0 =
    (int t + 1)^2 * det (V0 ! 0) (V0 ! 7) + (int t + 1) * (det (V0 ! 0) (V0 ! 8) + det (V0 ! 1) (V0 ! 7))
    + det (V0 ! 1) (V0 ! 8)"
proof -
  let ?V = "((\<lambda>V. ins2 V 0) ^^ t) V0"
  have f: "?V ! 0 = V0 ! 0" "?V ! 1 = vadd (V0 ! 1) (vsmul (int t) (V0 ! 0))"
    "?V ! (7 + t) = V0 ! 7" "?V ! (8 + t) = vadd (V0 ! 8) (vsmul (int t) (V0 ! 7))"
    "length ?V = 14 + 2 * t"
    using family[OF F L] by auto
  have h: "length ?V div 2 = 7 + t" using f(5) by simp
  have s8: "Suc (0 + (7 + t)) = 8 + t" by simp
  have "S ?V 0 = det (vadd (?V ! 0) (?V ! 1)) (vadd (?V ! (7 + t)) (?V ! (8 + t)))"
    unfolding S_def h s8 by simp
  also have "\<dots> = det (vadd (V0 ! 0) (vadd (V0 ! 1) (vsmul (int t) (V0 ! 0))))
                      (vadd (V0 ! 7) (vadd (V0 ! 8) (vsmul (int t) (V0 ! 7))))"
    using f(1-4) by simp
  also have "\<dots> = (int t + 1)^2 * det (V0 ! 0) (V0 ! 7) + (int t + 1) * (det (V0 ! 0) (V0 ! 8) + det (V0 ! 1) (V0 ! 7))
    + det (V0 ! 1) (V0 ! 8)"
    by (rule S_poly)
  finally show ?thesis .
qed

theorem strictly_ordered_middle_rows:
  "frieze (FA t) \<and> frieze (FB t) \<and> length (FA t) = 14 + 2 * t \<and> length (FB t) = 14 + 2 * t \<and>
   (\<forall>i < 7 + t. dia (FA t) i < dia (FB t) i)"
proof -
  have LA: "length A0 = 14" and LB: "length B0 = 14" by (simp_all add: A0_def B0_def)
  have SAB: "\<And>t. S (FA t) 0 < S (FB t) 0"
  proof -
    fix t :: nat
    have SA': "S (FA t) 0 = 6 * (int t + 1)^2 + 12 * (int t + 1) + 6"
      using S_family[OF frieze_A0 LA, of t] unfolding FA_def by (simp add: A0_def det_def)
    have SB': "S (FB t) 0 = 7 * (int t + 1)^2 + 26 * (int t + 1) + 7"
      using S_family[OF frieze_B0 LB, of t] unfolding FB_def by (simp add: B0_def det_def)
    define s where "s = int t + 1"
    have s1: "1 \<le> s" unfolding s_def by simp
    have ss: "0 \<le> s * s" using s1 by simp
    have "S (FA t) 0 = 6 * (s * s) + 12 * s + 6" using SA' unfolding s_def by (simp add: power2_eq_square)
    moreover have "S (FB t) 0 = 7 * (s * s) + 26 * s + 7" using SB' unfolding s_def by (simp add: power2_eq_square)
    ultimately show "S (FA t) 0 < S (FB t) 0" using s1 ss by linarith
  qed
  have D: "dominated (FA t) (FB t)"
  proof (induction t)
    case 0
    then show ?case using dominated_0 by (simp add: FA_def FB_def)
  next
    case (Suc t)
    have fA: "frieze (FA t) \<and> length (FA t) = 14 + 2 * t"
      using family[OF frieze_A0 LA, of t] unfolding FA_def by simp
    have ev: "even (length (FA t))" and j: "Suc 0 < length (FA t) div 2" using fA by auto
    have "dominated (ins2 (FA t) 0) (ins2 (FB t) 0)"
      using dominated_ins2[OF Suc.IH ev j SAB[of t]] .
    then show ?case by (simp add: FA_def FB_def)
  qed
  show ?thesis
    using family[OF frieze_A0 LA, of t] family[OF frieze_B0 LB, of t] D
    unfolding FA_def FB_def dominated_def by auto
qed

end
