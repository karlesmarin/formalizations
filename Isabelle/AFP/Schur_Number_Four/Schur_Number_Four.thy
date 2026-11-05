(*  Title:      Schur_Number_Four.thy
    Author:     Carles Marín
*)

section \<open>The Schur number \<open>S(4) = 44\<close>\<close>

theory Schur_Number_Four
  imports LRAT_Replay
begin

text \<open>A colouring \<open>f\<close> of \<open>{1..n}\<close> with \<open>k\<close> colours is Schur-free if no \<open>a + b = c\<close> in that range has
  \<open>f a = f b = f c\<close>.  Baumert found by computer that the largest \<open>n\<close> with a Schur-free 4-colouring is 44
  (S. W. Golomb and L. D. Baumert, Backtrack Programming, J. ACM 12 (1965), 516--524).

  Upper bound: colour swaps, proved in HOL, take any Schur-free 4-colouring of \<open>{1..45}\<close> to one whose colours
  appear for the first time in the order 0, 1, 2, 3: \<open>f 1 = 0\<close>, \<open>f 2 = 1\<close> and \<open>f k = 2\<close> for the first \<open>k\<close>
  with another colour, \<open>k \<in> {3, 4, 5}\<close> (the case where \<open>{1..5}\<close> uses two colours is a fourth, tiny case).
  Each case is encoded by explicit instances of three facts about the
  colouring (each colour is one of \<open>0..3\<close>, at most one colour per number, no monochromatic triple), refuted by a
  SAT solver, and the LRAT proof is replayed by the kernel (method \<open>lrat\<close>).  Lower bound: a witness for
  \<open>{1..44}\<close>, checked by \<open>code_simp\<close>.\<close>

definition schur_free :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "schur_free k n f \<longleftrightarrow> (\<forall>i. 1 \<le> i \<longrightarrow> i \<le> n \<longrightarrow> f i < k) \<and>
     (\<forall>a b. 1 \<le> a \<longrightarrow> 1 \<le> b \<longrightarrow> a + b \<le> n \<longrightarrow> \<not> (f a = f b \<and> f b = f (a + b)))"

lemma schur_free_range: "schur_free k n f \<Longrightarrow> 1 \<le> i \<Longrightarrow> i \<le> n \<Longrightarrow> f i < k"
  unfolding schur_free_def by blast

lemma schur_free_trip:
  "schur_free k n f \<Longrightarrow> 1 \<le> a \<Longrightarrow> 1 \<le> b \<Longrightarrow> a + b \<le> n \<Longrightarrow> \<not> (f a = f b \<and> f b = f (a + b))"
  unfolding schur_free_def by blast

ML \<open>LRAT_Solver.dir := Resources.master_directory \<^theory>\<close>

subsection \<open>Colour symmetry and the upper bound\<close>

definition sw :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sw x y c = (if c = x then y else if c = y then x else c)"

lemma sw_eq_iff: "sw x y a = sw x y b \<longleftrightarrow> a = b"
  unfolding sw_def by auto

lemma sw_less: "c < k \<Longrightarrow> x < k \<Longrightarrow> y < k \<Longrightarrow> sw x y c < k"
  unfolding sw_def by auto

lemma schur_free_sw:
  assumes sf: "schur_free k n f" and x: "x < k" and y: "y < k"
  shows "schur_free k n (sw x y \<circ> f)"
  unfolding schur_free_def comp_def sw_eq_iff
  using schur_free_range[OF sf] schur_free_trip[OF sf] sw_less[OF _ x y] by blast

lemma recolour:
  assumes sh: "schur_free 4 45 h" and h1: "h 1 = 0" and h2: "h 2 = 1"
    and k: "3 \<le> k" "k \<le> 45" and hk: "h k \<noteq> 0" "h k \<noteq> 1"
    and low: "\<And>i. 3 \<le> i \<Longrightarrow> i < k \<Longrightarrow> h i = 0 \<or> h i = 1"
  shows "\<exists>g. schur_free 4 45 g \<and> g 1 = 0 \<and> g 2 = 1 \<and> g k = 2 \<and> (\<forall>i. 3 \<le> i \<longrightarrow> i < k \<longrightarrow> g i = 0 \<or> g i = 1)"
proof -
  have x: "h k < 4" using schur_free_range[OF sh] k by simp
  define g where "g = sw 2 (h k) \<circ> h"
  have "schur_free 4 45 g" unfolding g_def by (rule schur_free_sw[OF sh _ x]) simp
  moreover have "g 1 = 0" "g 2 = 1" "g k = 2" unfolding g_def comp_def sw_def using h1 h2 hk by auto
  moreover have "\<forall>i. 3 \<le> i \<longrightarrow> i < k \<longrightarrow> g i = 0 \<or> g i = 1"
    unfolding g_def comp_def sw_def using low hk by fastforce
  ultimately show ?thesis by blast
qed

subsection \<open>The four cases left by the colour symmetry\<close>

lemma schur4_leaf_3:
  assumes sf: "schur_free 4 45 f" and f1: "f 1 = 0" and f2: "f 2 = 1" and fk: "f 3 = 2"
  shows False
proof -
  have range: "f i = 0 \<or> f i = 1 \<or> f i = 2 \<or> f i = 3" if "1 \<le> i" "i \<le> 45" for i
    using schur_free_range[OF sf that] by linarith
  have amo: "\<not> f i = c \<or> \<not> f i = d" if "c \<noteq> d" for i c d
    using that by auto
  have trip: "\<not> f a = k \<or> \<not> f b = k \<or> \<not> f c = k" if "a + b = c" "1 \<le> a" "1 \<le> b" "c \<le> 45" for a b c k
    using schur_free_trip[OF sf, of a b] that by auto
  show False
    apply (tactic \<open>
      let
        val ctxt = \<^context>
        val r = LRAT_Replay.instances ctxt @{thm range} ["i"] (map single (1 upto 45))
        val m = LRAT_Replay.instances ctxt @{thm amo} ["i", "c", "d"]
          (maps (fn i => maps (fn c => map (fn d => [i, c, d]) (c + 1 upto 3)) (0 upto 3)) (1 upto 45))
        val t = LRAT_Replay.instances ctxt @{thm trip} ["a", "b", "c", "k"]
          (maps (fn a => maps (fn b => map (fn k => [a, b, a + b, k]) (0 upto 3)) (a upto 45 - a)) (1 upto 22))
        val l = []
      in Method.insert_tac ctxt (r @ m @ t @ l @ @{thms f1 f2 fk}) 1 end\<close>)
    by lrat
qed

lemma schur4_leaf_4:
  assumes sf: "schur_free 4 45 f" and f1: "f 1 = 0" and f2: "f 2 = 1" and fk: "f 4 = 2"
    and low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 4 \<Longrightarrow> f i = 0 \<or> f i = 1"
  shows False
proof -
  have range: "f i = 0 \<or> f i = 1 \<or> f i = 2 \<or> f i = 3" if "1 \<le> i" "i \<le> 45" for i
    using schur_free_range[OF sf that] by linarith
  have amo: "\<not> f i = c \<or> \<not> f i = d" if "c \<noteq> d" for i c d
    using that by auto
  have trip: "\<not> f a = k \<or> \<not> f b = k \<or> \<not> f c = k" if "a + b = c" "1 \<le> a" "1 \<le> b" "c \<le> 45" for a b c k
    using schur_free_trip[OF sf, of a b] that by auto
  have low1: "f i = 0 \<or> f i = 1" if "3 \<le> i" "i < 4" for i using low that by blast
  show False
    apply (tactic \<open>
      let
        val ctxt = \<^context>
        val r = LRAT_Replay.instances ctxt @{thm range} ["i"] (map single (1 upto 45))
        val m = LRAT_Replay.instances ctxt @{thm amo} ["i", "c", "d"]
          (maps (fn i => maps (fn c => map (fn d => [i, c, d]) (c + 1 upto 3)) (0 upto 3)) (1 upto 45))
        val t = LRAT_Replay.instances ctxt @{thm trip} ["a", "b", "c", "k"]
          (maps (fn a => maps (fn b => map (fn k => [a, b, a + b, k]) (0 upto 3)) (a upto 45 - a)) (1 upto 22))
        val l = LRAT_Replay.instances ctxt @{thm low1} ["i"] (map single (3 upto 3))
      in Method.insert_tac ctxt (r @ m @ t @ l @ @{thms f1 f2 fk}) 1 end\<close>)
    by lrat
qed

lemma schur4_leaf_5:
  assumes sf: "schur_free 4 45 f" and f1: "f 1 = 0" and f2: "f 2 = 1" and fk: "f 5 = 2"
    and low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 5 \<Longrightarrow> f i = 0 \<or> f i = 1"
  shows False
proof -
  have range: "f i = 0 \<or> f i = 1 \<or> f i = 2 \<or> f i = 3" if "1 \<le> i" "i \<le> 45" for i
    using schur_free_range[OF sf that] by linarith
  have amo: "\<not> f i = c \<or> \<not> f i = d" if "c \<noteq> d" for i c d
    using that by auto
  have trip: "\<not> f a = k \<or> \<not> f b = k \<or> \<not> f c = k" if "a + b = c" "1 \<le> a" "1 \<le> b" "c \<le> 45" for a b c k
    using schur_free_trip[OF sf, of a b] that by auto
  have low1: "f i = 0 \<or> f i = 1" if "3 \<le> i" "i < 5" for i using low that by blast
  show False
    apply (tactic \<open>
      let
        val ctxt = \<^context>
        val r = LRAT_Replay.instances ctxt @{thm range} ["i"] (map single (1 upto 45))
        val m = LRAT_Replay.instances ctxt @{thm amo} ["i", "c", "d"]
          (maps (fn i => maps (fn c => map (fn d => [i, c, d]) (c + 1 upto 3)) (0 upto 3)) (1 upto 45))
        val t = LRAT_Replay.instances ctxt @{thm trip} ["a", "b", "c", "k"]
          (maps (fn a => maps (fn b => map (fn k => [a, b, a + b, k]) (0 upto 3)) (a upto 45 - a)) (1 upto 22))
        val l = LRAT_Replay.instances ctxt @{thm low1} ["i"] (map single (3 upto 4))
      in Method.insert_tac ctxt (r @ m @ t @ l @ @{thms f1 f2 fk}) 1 end\<close>)
    by lrat
qed

lemma schur4_leaf_6:
  assumes sf: "schur_free 4 45 f" and f1: "f 1 = 0" and f2: "f 2 = 1"
    and low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 6 \<Longrightarrow> f i = 0 \<or> f i = 1"
  shows False
proof -
  have range: "f i = 0 \<or> f i = 1 \<or> f i = 2 \<or> f i = 3" if "1 \<le> i" "i \<le> 45" for i
    using schur_free_range[OF sf that] by linarith
  have amo: "\<not> f i = c \<or> \<not> f i = d" if "c \<noteq> d" for i c d
    using that by auto
  have trip: "\<not> f a = k \<or> \<not> f b = k \<or> \<not> f c = k" if "a + b = c" "1 \<le> a" "1 \<le> b" "c \<le> 45" for a b c k
    using schur_free_trip[OF sf, of a b] that by auto
  have low1: "f i = 0 \<or> f i = 1" if "3 \<le> i" "i < 6" for i using low that by blast
  show False
    apply (tactic \<open>
      let
        val ctxt = \<^context>
        val r = LRAT_Replay.instances ctxt @{thm range} ["i"] (map single (1 upto 45))
        val m = LRAT_Replay.instances ctxt @{thm amo} ["i", "c", "d"]
          (maps (fn i => maps (fn c => map (fn d => [i, c, d]) (c + 1 upto 3)) (0 upto 3)) (1 upto 45))
        val t = LRAT_Replay.instances ctxt @{thm trip} ["a", "b", "c", "k"]
          (maps (fn a => maps (fn b => map (fn k => [a, b, a + b, k]) (0 upto 3)) (a upto 45 - a)) (1 upto 22))
        val l = LRAT_Replay.instances ctxt @{thm low1} ["i"] (map single (3 upto 5))
      in Method.insert_tac ctxt (r @ m @ t @ l @ @{thms f1 f2}) 1 end\<close>)
    by lrat
qed

theorem schur4_upper: "\<not> (\<exists>f. schur_free 4 45 f)"
proof
  assume "\<exists>f. schur_free 4 45 f"
  then obtain f where sf: "schur_free 4 45 f" ..
  have f1: "f 1 < 4" by (rule schur_free_range[OF sf]) simp_all
  define g where "g = sw 0 (f 1) \<circ> f"
  have sg: "schur_free 4 45 g" unfolding g_def by (rule schur_free_sw[OF sf _ f1]) simp
  have g1: "g 1 = 0" unfolding g_def comp_def sw_def by simp
  have "\<not> (g 1 = g 1 \<and> g 1 = g (1 + 1))" by (rule schur_free_trip[OF sg]) simp_all
  then have g2: "g 2 \<noteq> 0" using g1 by (simp add: numeral_2_eq_2)
  have g2r: "g 2 < 4" by (rule schur_free_range[OF sg]) simp_all
  define h where "h = sw 1 (g 2) \<circ> g"
  have sh: "schur_free 4 45 h" unfolding h_def by (rule schur_free_sw[OF sg _ g2r]) simp
  have h1: "h 1 = 0" unfolding h_def comp_def sw_def using g1 g2 by simp
  have h2: "h 2 = 1" unfolding h_def comp_def sw_def by simp
  show False
  proof (cases "h 3 = 0 \<or> h 3 = 1")
    case False
    then obtain e where "schur_free 4 45 e" "e 1 = 0" "e 2 = 1" "e 3 = 2"
      using recolour[OF sh h1 h2, of 3] by auto
    then show False by (rule schur4_leaf_3)
  next
    case h3: True
    show False
    proof (cases "h 4 = 0 \<or> h 4 = 1")
      case False
      have low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 4 \<Longrightarrow> h i = 0 \<or> h i = 1"
      proof -
        fix i :: nat assume "3 \<le> i" "i < 4"
        then have "i = 3" by auto
        then show "h i = 0 \<or> h i = 1" using h3 by auto
      qed
      obtain e where e: "schur_free 4 45 e" "e 1 = 0" "e 2 = 1" "e 4 = 2"
        "\<forall>i. 3 \<le> i \<longrightarrow> i < 4 \<longrightarrow> e i = 0 \<or> e i = 1"
        using recolour[OF sh h1 h2, of 4] False low by auto
      show False by (rule schur4_leaf_4[OF e(1-4)]) (use e(5) in blast)
    next
      case h4: True
      show False
      proof (cases "h 5 = 0 \<or> h 5 = 1")
        case False
        have low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 5 \<Longrightarrow> h i = 0 \<or> h i = 1"
        proof -
          fix i :: nat assume "3 \<le> i" "i < 5"
          then have "i = 3 \<or> i = 4" by auto
          then show "h i = 0 \<or> h i = 1" using h3 h4 by auto
        qed
        obtain e where e: "schur_free 4 45 e" "e 1 = 0" "e 2 = 1" "e 5 = 2"
          "\<forall>i. 3 \<le> i \<longrightarrow> i < 5 \<longrightarrow> e i = 0 \<or> e i = 1"
          using recolour[OF sh h1 h2, of 5] False low by auto
        show False by (rule schur4_leaf_5[OF e(1-4)]) (use e(5) in blast)
      next
        case h5: True
        have low: "\<And>i. 3 \<le> i \<Longrightarrow> i < 6 \<Longrightarrow> h i = 0 \<or> h i = 1"
        proof -
          fix i :: nat assume "3 \<le> i" "i < 6"
          then have "i = 3 \<or> i = 4 \<or> i = 5" by auto
          then show "h i = 0 \<or> h i = 1" using h3 h4 h5 by auto
        qed
        show False by (rule schur4_leaf_6[OF sh h1 h2 low])
      qed
    qed
  qed
qed

subsection \<open>Lower bound: a witness\<close>

definition w44 :: "nat \<Rightarrow> nat" where
  "w44 i = [0, 0, 2, 0, 3, 2, 3, 1, 2, 0, 1, 1, 1, 3, 0, 3, 1, 2, 2, 0, 3, 2, 3, 3, 0, 3, 0, 2, 2, 1, 1, 2, 0, 1, 0,
            1, 0, 2, 1, 3, 2, 3, 0, 2, 0] ! i"

lemma schur_free_lists:
  "schur_free k n f \<longleftrightarrow> list_all (\<lambda>i. f i < k) [1..<n+1] \<and>
     list_all (\<lambda>a. list_all (\<lambda>b. a + b \<le> n \<longrightarrow> \<not> (f a = f b \<and> f b = f (a + b))) [1..<n+1]) [1..<n+1]"
  (is "?s \<longleftrightarrow> ?l1 \<and> ?l2")
proof
  assume s: ?s
  show "?l1 \<and> ?l2" unfolding list_all_iff
  proof (intro conjI ballI impI)
    fix i assume "i \<in> set [1..<n+1]"
    then show "f i < k" using schur_free_range[OF s] by auto
  next
    fix a b assume "a \<in> set [1..<n+1]" "b \<in> set [1..<n+1]" "a + b \<le> n"
    then show "\<not> (f a = f b \<and> f b = f (a + b))" using schur_free_trip[OF s, of a b] by auto
  qed
next
  assume l: "?l1 \<and> ?l2"
  show ?s unfolding schur_free_def
  proof (intro conjI allI impI)
    fix i :: nat assume "1 \<le> i" "i \<le> n"
    with l show "f i < k" by (auto simp: list_all_iff)
  next
    fix a b :: nat assume ab: "1 \<le> a" "1 \<le> b" "a + b \<le> n"
    then have "a \<in> set [1..<n+1]" "b \<in> set [1..<n+1]" by auto
    with l ab show "\<not> (f a = f b \<and> f b = f (a + b))" unfolding list_all_iff by blast
  qed
qed

theorem schur4_lower: "schur_free 4 44 w44"
  unfolding schur_free_lists w44_def by code_simp

theorem schur_number_4: "(\<exists>f. schur_free 4 44 f) \<and> \<not> (\<exists>f. schur_free 4 45 f)"
  using schur4_lower schur4_upper by blast

end
