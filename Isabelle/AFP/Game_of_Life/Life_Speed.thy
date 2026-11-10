(*  Title:      Game_of_Life/Life_Speed.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Life_Speed
  imports Life_Flight
begin

section \<open>The speed limit\<close>

text \<open>Conway's speed limit (Johnston and Greene, Conway's Game of Life: Mathematics and
  Construction, Theorem 4.1): a pattern contained in a diagonal half-plane needs two generations
  to advance one diagonal.  The half-plane lemmas (\<open>steps_below\<close>, and \<open>steps_signed\<close> for the four
  diagonal directions) hold for arbitrary patterns, finite or not, because the argument is local;
  the source states its theorem for finite objects only.

  The periodic consequence, \<open>speed_limit\<close>, is for a finite non-empty pattern that reappears displaced
  by \<open>(a, b)\<close> after \<open>p\<close> generations: \<open>2 (|a| + |b|) \<le> p\<close>.  In this oblique form it is the statement
  of Exercise 4.26 of the same book; its diagonal and orthogonal cases are the bounds \<open>c/4\<close> and
  \<open>c/2\<close> of Theorem 4.1.  For \<open>a = b = 0\<close> (oscillators, still lifes) it says nothing.  The
  consequence for objects that never reappear exactly (puffers, rakes) is not stated here.  The
  glider attains the diagonal bound (\<open>speed_limit_sharp\<close>); the lightweight spaceship attains the orthogonal
  one (\<open>speed_limit_orthogonal_sharp\<close>, in \<open>Life_Spaceships\<close>).\<close>

definition below :: "int \<Rightarrow> cell set" where
  "below m = {c. fst c + snd c \<le> m}"

text \<open>A cell beyond the half-plane can only be born on the next diagonal, and then the three cells
  under it are alive.\<close>

lemma front_step:
  assumes "S \<subseteq> below m" and "c \<in> step S" and "m < fst c + snd c"
  shows "fst c + snd c = m + 1"
    and "{(fst c - 1, snd c - 1), (fst c - 1, snd c), (fst c, snd c - 1)} \<subseteq> S"
proof -
  obtain x y where c: "c = (x, y)" by (cases c)
  have cS: "c \<notin> S" using assms(1,3) by (auto simp: below_def)
  have n3: "card (S \<inter> nbhd c) = 3" using assms(2) cS by (simp add: mem_step nbrs_def)
  have sum: "a + b \<le> m" if "(a, b) \<in> S" for a b
    using assms(1) that by (auto simp: below_def)
  have sub: "S \<inter> nbhd c \<subseteq> {(x - 1, y - 1), (x - 1, y), (x, y - 1)}"
  proof
    fix d assume d: "d \<in> S \<inter> nbhd c"
    obtain a b where dd: "d = (a, b)" by (cases d)
    have "a + b \<le> m" using sum d dd by blast
    moreover have "\<bar>a - x\<bar> \<le> 1" "\<bar>b - y\<bar> \<le> 1" "(a, b) \<noteq> (x, y)"
      using d dd c by (auto simp: nbhd_def)
    moreover have "m < x + y" using assms(3) c by simp
    ultimately show "d \<in> {(x - 1, y - 1), (x - 1, y), (x, y - 1)}"
      unfolding dd by (auto simp: abs_le_iff prod_eq_iff)
  qed
  have e1: "fst c + snd c = m + 1"
  proof (rule ccontr)
    assume "fst c + snd c \<noteq> m + 1"
    then have far: "m + 2 \<le> x + y" using assms(3) c by simp
    have "S \<inter> nbhd c \<subseteq> {(x - 1, y - 1)}"
    proof
      fix d assume d: "d \<in> S \<inter> nbhd c"
      then have "d \<in> {(x - 1, y - 1), (x - 1, y), (x, y - 1)}" using sub by blast
      moreover obtain a b where dd: "d = (a, b)" by (cases d)
      moreover have "a + b \<le> m" using sum d dd by blast
      ultimately show "d \<in> {(x - 1, y - 1)}" using far by auto
    qed
    then have "card (S \<inter> nbhd c) \<le> card {(x - 1, y - 1)}" by (rule card_mono[OF finite.insertI[OF finite.emptyI]])
    then show False using n3 by simp
  qed
  then show "fst c + snd c = m + 1" .
  have card3: "card {(x - 1, y - 1), (x - 1, y), (x, y - 1)} = 3" by (simp add: card_insert_if)
  have "S \<inter> nbhd c = {(x - 1, y - 1), (x - 1, y), (x, y - 1)}"
  proof (rule card_subset_eq[OF _ sub])
    show "finite {(x - 1, y - 1), (x - 1, y), (x, y - 1)}" by simp
    show "card (S \<inter> nbhd c) = card {(x - 1, y - 1), (x - 1, y), (x, y - 1)}"
      using n3 card3 by simp
  qed
  then show "{(fst c - 1, snd c - 1), (fst c - 1, snd c), (fst c, snd c - 1)} \<subseteq> S"
    unfolding c by (metis Int_lower1 fst_conv snd_conv)
qed

theorem step_below: "S \<subseteq> below m \<Longrightarrow> step S \<subseteq> below (m + 1)"
proof
  fix c assume S: "S \<subseteq> below m" and c: "c \<in> step S"
  show "c \<in> below (m + 1)"
  proof (rule ccontr)
    assume "c \<notin> below (m + 1)"
    then have "m < fst c + snd c" by (simp add: below_def)
    then have "fst c + snd c = m + 1" by (rule front_step(1)[OF S c])
    then show False using \<open>c \<notin> below (m + 1)\<close> by (simp add: below_def)
  qed
qed

theorem step2_below: "S \<subseteq> below m \<Longrightarrow> step (step S) \<subseteq> below (m + 1)"
proof
  fix c assume S: "S \<subseteq> below m" and c: "c \<in> step (step S)"
  show "c \<in> below (m + 1)"
  proof (rule ccontr)
    assume nb: "c \<notin> below (m + 1)"
    obtain x y where cxy: "c = (x, y)" by (cases c)
    have S1: "step S \<subseteq> below (m + 1)" by (rule step_below[OF S])
    have gt: "m + 1 < x + y" using nb cxy by (simp add: below_def)
    have e: "x + y = m + 2" using front_step(1)[OF S1 c] gt cxy by simp
    have T: "{(x - 1, y - 1), (x - 1, y), (x, y - 1)} \<subseteq> step S"
      using front_step(2)[OF S1 c] gt cxy by simp
    then have R: "(x - 1, y - 1) \<in> step S" and P: "(x - 1, y) \<in> step S"
      and Q: "(x, y - 1) \<in> step S" by simp_all
    have fP: "{(x - 2, y - 1), (x - 2, y), (x - 1, y - 1)} \<subseteq> S"
      using front_step(2)[OF S P] e by simp
    have fQ: "{(x - 1, y - 2), (x - 1, y - 1), (x, y - 2)} \<subseteq> S"
      using front_step(2)[OF S Q] e by simp
    have RS: "(x - 1, y - 1) \<in> S" using fP by simp
    have "nbrs S (x - 1, y - 1) = 2 \<or> nbrs S (x - 1, y - 1) = 3"
      using R RS by (simp add: mem_step)
    moreover have "4 \<le> nbrs S (x - 1, y - 1)"
    proof -
      let ?F = "{(x - 2, y - 1), (x - 2, y), (x - 1, y - 2), (x, y - 2)}"
      have "?F \<subseteq> S \<inter> nbhd (x - 1, y - 1)"
        using fP fQ by (auto simp: nbhd_def)
      then have "card ?F \<le> card (S \<inter> nbhd (x - 1, y - 1))"
        by (rule card_mono[OF finite_Int[OF disjI2[OF finite_nbhd]]])
      moreover have "card ?F = 4" by (simp add: card_insert_if)
      ultimately show ?thesis by (simp add: nbrs_def)
    qed
    ultimately show False by simp
  qed
qed

theorem steps_below: "S \<subseteq> below m \<Longrightarrow> (step ^^ n) S \<subseteq> below (m + int ((n + 1) div 2))"
proof -
  assume S: "S \<subseteq> below m"
  have even: "(step ^^ (2 * k)) S \<subseteq> below (m + int k)" if "S \<subseteq> below m" for k S m
    using that
  proof (induction k arbitrary: S m)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    have e: "2 * Suc k = 2 * k + 2" by simp
    have s2: "(step ^^ 2) S = step (step S)" by (simp add: eval_nat_numeral)
    have "(step ^^ (2 * Suc k)) S = (step ^^ (2 * k)) ((step ^^ 2) S)"
      by (simp only: e funpow_add comp_apply)
    also have "\<dots> = (step ^^ (2 * k)) (step (step S))" by (simp only: s2)
    also have "\<dots> \<subseteq> below (m + 1 + int k)"
      by (rule Suc.IH[OF step2_below[OF Suc.prems]])
    finally show ?case by (simp add: algebra_simps)
  qed
  have "\<exists>k. n = 2 * k \<or> n = 2 * k + 1" by (rule exI[of _ "n div 2"]) arith
  then obtain k where k: "n = 2 * k \<or> n = 2 * k + 1" by blast
  show ?thesis
  proof (cases "n = 2 * k")
    case True
    have "(n + 1) div 2 = k" using True by arith
    then show ?thesis using even[OF S, of k] True by simp
  next
    case False
    then have n: "n = 2 * k + 1" using k by simp
    have "(n + 1) div 2 = k + 1" using n by arith
    moreover have "(step ^^ n) S = step ((step ^^ (2 * k)) S)" using n by simp
    moreover have "step ((step ^^ (2 * k)) S) \<subseteq> below (m + int k + 1)"
      by (rule step_below[OF even[OF S]])
    ultimately show ?thesis by (simp add: add.commute add.left_commute)
  qed
qed

text \<open>The same in the four diagonal directions.\<close>

lemma steps_rot: "(step ^^ n) (rot ` S) = rot ` (step ^^ n) S"
  by (induction n) (simp_all add: step_rot)

lemma steps_flip: "(step ^^ n) (flip ` S) = flip ` (step ^^ n) S"
  by (induction n) (simp_all add: step_flip)

lemma steps_signed_conj:
  assumes "\<And>n S. (step ^^ n) (g ` S) = g ` (step ^^ n) S"
    and "\<And>c. fst (g c) + snd (g c) = s * fst c + t * snd c"
    and "S \<subseteq> {c. s * fst c + t * snd c \<le> m}"
  shows "(step ^^ n) S \<subseteq> {c. s * fst c + t * snd c \<le> m + int ((n + 1) div 2)}"
proof
  fix c assume c: "c \<in> (step ^^ n) S"
  have "g ` S \<subseteq> below m" using assms(2,3) by (auto simp: below_def)
  from steps_below[OF this, of n] have "(step ^^ n) (g ` S) \<subseteq> below (m + int ((n + 1) div 2))" .
  then have "g ` (step ^^ n) S \<subseteq> below (m + int ((n + 1) div 2))" using assms(1) by simp
  then have "g c \<in> below (m + int ((n + 1) div 2))" using c by blast
  then show "c \<in> {c. s * fst c + t * snd c \<le> m + int ((n + 1) div 2)}"
    using assms(2) by (simp add: below_def)
qed

theorem steps_signed:
  assumes "\<bar>s\<bar> = 1" and "\<bar>t\<bar> = 1" and "S \<subseteq> {c. s * fst c + t * snd c \<le> m}"
  shows "(step ^^ n) S \<subseteq> {c. s * fst c + t * snd c \<le> m + int ((n + 1) div 2)}"
proof -
  have s: "s = 1 \<or> s = -1" and t: "t = 1 \<or> t = -1" using assms(1,2) by arith+
  show ?thesis
  proof (cases "s = 1")
    case s1: True
    show ?thesis
    proof (cases "t = 1")
      case True
      show ?thesis
        by (rule steps_signed_conj[where g = id]) (use s1 True assms(3) in simp_all)
    next
      case False
      then have t1: "t = -1" using t by simp
      have "(step ^^ n) ((\<lambda>c. flip (rot c)) ` S') = (\<lambda>c. flip (rot c)) ` (step ^^ n) S'"
        for n S'
      proof -
        have e: "\<And>A. (\<lambda>c. flip (rot c)) ` A = flip ` rot ` A" by (simp add: image_image)
        show ?thesis by (simp only: e steps_flip steps_rot)
      qed
      then show ?thesis
        by (rule steps_signed_conj[where g = "\<lambda>c. flip (rot c)"])
          (use s1 t1 assms(3) in \<open>simp_all add: image_image rot_def flip_def\<close>)
    qed
  next
    case False
    then have s1: "s = -1" using s by simp
    show ?thesis
    proof (cases "t = 1")
      case True
      have "(step ^^ n) ((\<lambda>c. rot (flip c)) ` S') = (\<lambda>c. rot (flip c)) ` (step ^^ n) S'"
        for n S'
      proof -
        have e: "\<And>A. (\<lambda>c. rot (flip c)) ` A = rot ` flip ` A" by (simp add: image_image)
        show ?thesis by (simp only: e steps_flip steps_rot)
      qed
      then show ?thesis
        by (rule steps_signed_conj[where g = "\<lambda>c. rot (flip c)"])
          (use s1 True assms(3) in \<open>simp_all add: image_image rot_def flip_def\<close>)
    next
      case False
      then have t1: "t = -1" using t by simp
      have "(step ^^ n) ((\<lambda>c. rot (rot c)) ` S') = (\<lambda>c. rot (rot c)) ` (step ^^ n) S'"
        for n S'
      proof -
        have e: "\<And>A. (\<lambda>c. rot (rot c)) ` A = rot ` rot ` A" by (simp add: image_image)
        show ?thesis by (simp only: e steps_rot)
      qed
      then show ?thesis
        by (rule steps_signed_conj[where g = "\<lambda>c. rot (rot c)"])
          (use s1 t1 assms(3) in \<open>simp_all add: image_image rot_def\<close>)
    qed
  qed
qed

theorem speed_limit:
  assumes "finite S" and "S \<noteq> {}" and "(step ^^ p) S = transl (a, b) S"
  shows "2 * (\<bar>a\<bar> + \<bar>b\<bar>) \<le> int p"
proof -
  define s :: int where "s = (if 0 \<le> a then 1 else -1)"
  define t :: int where "t = (if 0 \<le> b then 1 else -1)"
  have s1: "\<bar>s\<bar> = 1" and t1: "\<bar>t\<bar> = 1" by (simp_all add: s_def t_def)
  have sa: "s * a = \<bar>a\<bar>" and tb: "t * b = \<bar>b\<bar>"
    by (cases "0 \<le> a", simp_all add: s_def) (cases "0 \<le> b", simp_all add: t_def)
  define f where "f c = s * fst c + t * snd c" for c
  define M where "M = Max (f ` S)"
  have fin: "finite (f ` S)" using assms(1) by simp
  have ne: "f ` S \<noteq> {}" using assms(2) by simp
  have SM: "S \<subseteq> {c. s * fst c + t * snd c \<le> M}"
    using Max_ge[OF fin] unfolding M_def f_def by blast
  have "M \<in> f ` S" unfolding M_def by (rule Max_in[OF fin ne])
  then obtain c0 where c0: "c0 \<in> S" "f c0 = M" by (auto simp: image_iff eq_commute)
  have "(step ^^ (p * 2)) S \<subseteq> {c. s * fst c + t * snd c \<le> M + int ((p * 2 + 1) div 2)}"
    by (rule steps_signed[OF s1 t1 SM])
  moreover have "(step ^^ (p * 2)) S = transl (2 * a, 2 * b) S"
    using flight_mult[OF assms(3), of 2] by simp
  moreover have "(p * 2 + 1) div 2 = p" by arith
  ultimately have sub: "transl (2 * a, 2 * b) S \<subseteq> {c. s * fst c + t * snd c \<le> M + int p}"
    by simp
  have "tr (2 * a, 2 * b) c0 \<in> transl (2 * a, 2 * b) S" using c0(1) by (auto simp: transl_def)
  then have "s * (fst c0 + 2 * a) + t * (snd c0 + 2 * b) \<le> M + int p"
    using sub by (auto simp: tr_def)
  moreover have "s * fst c0 + t * snd c0 = M" using c0(2) by (simp add: f_def)
  ultimately show ?thesis using sa tb by (simp add: algebra_simps)
qed

corollary speed_limit_diagonal:
  assumes "finite S" and "S \<noteq> {}" and "(step ^^ p) S = transl (a, a) S"
  shows "4 * \<bar>a\<bar> \<le> int p"
  using speed_limit[OF assms] by simp

corollary speed_limit_orthogonal:
  assumes "finite S" and "S \<noteq> {}" and "(step ^^ p) S = transl (a, 0) S"
  shows "2 * \<bar>a\<bar> \<le> int p"
  using speed_limit[OF assms] by simp

text \<open>The glider moves by \<open>(1, 1)\<close> every 4 generations: the diagonal bound is attained.\<close>

theorem speed_limit_sharp:
  "finite glider \<and> glider \<noteq> {} \<and> (step ^^ 4) glider = transl (1, 1) glider \<and> 2 * (\<bar>1::int\<bar> + \<bar>1\<bar>) = int 4"
proof -
  have "finite glider" "glider \<noteq> {}" by (simp_all add: glider_def)
  then show ?thesis using glider_moves by simp
qed

end
