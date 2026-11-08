(*  Title:      Trace_Rank.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: elementary trace bound used in V236 branch e = 1: a symmetric X with X <= I that factors through
   T terms (rank <= |T|) has tr X <= |T|, and tr X < |T| - 1 if X has a negative direction;
   no spectral theorem: projections P = I - u u^T and induction on |T| *)
theory Trace_Rank
  imports Complex_Main
begin

text \<open>The spectral step of branch $e=1$ of the note: ``$\tilde H\preceq I$, rank $a+1$, one negative
  eigenvalue, hence $\operatorname{tr}\tilde H<a$''. It is proved here without eigenvalues.
  Vectors and matrices are functions on a finite index set \<open>I\<close>. The rank hypothesis is a
  factorization $X=\sum_{t\in T}W_tC_t^{\mathsf T}$ (rank $\le|T|$, which is the direction used).

  \<^item> \<open>trace_rank_le\<close>: $X$ symmetric, $X\preceq I$, rank $\le|T|$ $\Rightarrow$ $\operatorname{tr}X\le|T|$.
    Take a unit vector $u$ proportional to a nonzero $W_s$ and $P=I-uu^{\mathsf T}$:
    $PXP\preceq I$, $PXP$ factors through $T\setminus\{s\}$ and $\operatorname{tr}X=\operatorname{tr}PXP+u^{\mathsf T}Xu
    \le\operatorname{tr}PXP+1$; induct on $|T|$.
  \<^item> \<open>trace_rank_neg\<close>: if moreover $v^{\mathsf T}Xv<0$ for some $v$, then $\operatorname{tr}X<|T|-1$.
    Project $v$ orthogonally onto the span of the $W_t$ (\<open>projection_exists\<close>): the remainder lies
    in $\ker X$, so the projection $p$ has $p^{\mathsf T}Xp<0$; one step with $u=p/|p|$ and then
    \<open>trace_rank_le\<close>.\<close>

definition dI :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "dI I u v = (\<Sum>i\<in>I. u i * v i)"

definition qI :: "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "qI I X v = (\<Sum>i\<in>I. \<Sum>j\<in>I. v i * X i j * v j)"

definition trI :: "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> real" where
  "trI I X = (\<Sum>i\<in>I. X i i)"

definition symI :: "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> bool" where
  "symI I X \<longleftrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. X j i = X i j)"

text \<open>$X\preceq I$.\<close>
definition leI :: "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> bool" where
  "leI I X \<longleftrightarrow> (\<forall>v. qI I X v \<le> dI I v v)"

text \<open>$X=\sum_{t\in T}W_tC_t^{\mathsf T}$ on $I$.\<close>
definition factI :: "'i set \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> ('t \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow>
    ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> bool" where
  "factI I T W C X \<longleftrightarrow> (\<forall>i\<in>I. \<forall>j\<in>I. X i j = (\<Sum>t\<in>T. W t i * C t j))"

text \<open>$Pv=v-u\,(u\cdot v)$ and $PXP$.\<close>
definition pv :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> 'i \<Rightarrow> real" where
  "pv I u v = (\<lambda>i. v i - u i * dI I u v)"

definition pX :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> real" where
  "pX I u X = (\<lambda>i j. X i j - u i * (\<Sum>l\<in>I. u l * X l j) - (\<Sum>k\<in>I. X i k * u k) * u j
                    + qI I X u * u i * u j)"

section \<open>Linear algebra of the dot product\<close>

lemma dI_comm: "dI I u v = dI I v u"
  unfolding dI_def by (simp add: mult.commute)

lemma dI_nonneg: "0 \<le> dI I u u"
  unfolding dI_def by (rule sum_nonneg) simp

lemma dI_zero:
  assumes "finite I" "dI I u u = 0" "i \<in> I" shows "u i = 0"
proof -
  have "\<forall>i\<in>I. u i * u i = 0"
    using assms(1,2) unfolding dI_def by (subst sum_nonneg_eq_0_iff[symmetric]) auto
  with assms(3) show ?thesis by simp
qed

lemma dI_pos:
  assumes "finite I" "i \<in> I" "u i \<noteq> 0" shows "0 < dI I u u"
proof -
  have "dI I u u \<noteq> 0" using dI_zero[OF assms(1) _ assms(2), of u] assms(3) by blast
  then show ?thesis using dI_nonneg[of I u] by linarith
qed

lemma dI_normalize:
  assumes "0 < dI I p p"
  shows "dI I (\<lambda>i. p i / sqrt (dI I p p)) (\<lambda>i. p i / sqrt (dI I p p)) = 1"
proof -
  have "dI I (\<lambda>i. p i / sqrt (dI I p p)) (\<lambda>i. p i / sqrt (dI I p p))
      = dI I p p / (sqrt (dI I p p) * sqrt (dI I p p))"
    unfolding dI_def sum_divide_distrib by (intro sum.cong refl) simp
  also have "sqrt (dI I p p) * sqrt (dI I p p) = dI I p p" using assms by simp
  finally show ?thesis using assms by simp
qed

lemma dI_diff_left: "dI I (\<lambda>i. u i - w i) v = dI I u v - dI I w v"
  unfolding dI_def by (simp add: left_diff_distrib sum_subtractf)

lemma dI_add_left: "dI I (\<lambda>i. u i + w i) v = dI I u v + dI I w v"
  unfolding dI_def by (simp add: distrib_right sum.distrib)

lemma dI_scale_left: "dI I (\<lambda>i. c * u i) v = c * dI I u v"
  unfolding dI_def by (simp add: sum_distrib_left mult_ac)

lemma dI_scale_right: "dI I v (\<lambda>i. c * u i) = c * dI I v u"
  unfolding dI_def by (simp add: sum_distrib_left mult_ac)

lemma dI_sum_left: "dI I (\<lambda>i. \<Sum>t\<in>T. c t * W t i) v = (\<Sum>t\<in>T. c t * dI I (W t) v)"
  unfolding dI_def sum_distrib_right by (subst sum.swap) (simp add: sum_distrib_left mult_ac)

lemma dI_diff_right: "dI I v (\<lambda>i. u i - w i) = dI I v u - dI I v w"
  unfolding dI_def by (simp add: right_diff_distrib sum_subtractf)

lemma dI_add_right: "dI I v (\<lambda>i. u i + w i) = dI I v u + dI I v w"
  unfolding dI_def by (simp add: distrib_left sum.distrib)

lemma dI_mult_left: "dI I (\<lambda>i. u i * c) v = dI I u v * c"
  unfolding dI_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)

lemma dI_mult_right: "dI I v (\<lambda>i. u i * c) = dI I v u * c"
  unfolding dI_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)

text \<open>The bilinear form $x^{\mathsf T}Xy$.\<close>
definition bI :: "'i set \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "bI I X x y = (\<Sum>i\<in>I. \<Sum>j\<in>I. x i * X i j * y j)"

lemma qI_bI: "qI I X v = bI I X v v"
  unfolding qI_def bI_def ..

lemma bI_diff_left: "bI I X (\<lambda>i. x i - y i) z = bI I X x z - bI I X y z"
  unfolding bI_def by (simp add: left_diff_distrib sum_subtractf)

lemma bI_diff_right: "bI I X z (\<lambda>i. x i - y i) = bI I X z x - bI I X z y"
  unfolding bI_def by (simp add: right_diff_distrib sum_subtractf)

lemma bI_add_left: "bI I X (\<lambda>i. x i + y i) z = bI I X x z + bI I X y z"
  unfolding bI_def by (simp add: distrib_right sum.distrib)

lemma bI_add_right: "bI I X z (\<lambda>i. x i + y i) = bI I X z x + bI I X z y"
  unfolding bI_def by (simp add: distrib_left sum.distrib)

lemma bI_mult_left: "bI I X (\<lambda>i. x i * c) z = bI I X x z * c"
  unfolding bI_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)

lemma bI_mult_right: "bI I X z (\<lambda>i. x i * c) = bI I X z x * c"
  unfolding bI_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)

lemma bI_row: "bI I X x y = (\<Sum>i\<in>I. x i * (\<Sum>j\<in>I. X i j * y j))"
  unfolding bI_def by (simp add: sum_distrib_left mult_ac)

lemma bI_col: "bI I X x y = (\<Sum>j\<in>I. (\<Sum>i\<in>I. x i * X i j) * y j)"
  unfolding bI_def sum_distrib_right by (subst sum.swap) simp

lemma dI_cong:
  assumes "\<forall>i\<in>I. u i = u' i" "\<forall>i\<in>I. v i = v' i" shows "dI I u v = dI I u' v'"
  unfolding dI_def using assms by simp

section \<open>Orthogonal projection onto the span of a finite family\<close>

lemma projection_exists:
  assumes I: "finite I" and T: "finite T"
  shows "\<exists>\<beta>. \<forall>t\<in>T. dI I (\<lambda>i. v i - (\<Sum>s\<in>T. \<beta> s * W s i)) (W t) = 0"
  using T
proof (induction T arbitrary: v rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert r T)
  obtain \<beta> where b: "\<forall>t\<in>T. dI I (\<lambda>i. v i - (\<Sum>s\<in>T. \<beta> s * W s i)) (W t) = 0"
    using insert.IH by blast
  obtain \<gamma> where g: "\<forall>t\<in>T. dI I (\<lambda>i. W r i - (\<Sum>s\<in>T. \<gamma> s * W s i)) (W t) = 0"
    using insert.IH by blast
  define z where "z = (\<lambda>i. v i - (\<Sum>s\<in>T. \<beta> s * W s i))"
  define zr where "zr = (\<lambda>i. W r i - (\<Sum>s\<in>T. \<gamma> s * W s i))"
  have bz: "\<forall>t\<in>T. dI I z (W t) = 0" using b unfolding z_def .
  have gz: "\<forall>t\<in>T. dI I zr (W t) = 0" using g unfolding zr_def .
  have Wr: "W r i = zr i + (\<Sum>s\<in>T. \<gamma> s * W s i)" for i unfolding zr_def by simp
  have dWr: "dI I y (W r) = dI I y zr + (\<Sum>s\<in>T. \<gamma> s * dI I y (W s))" for y
  proof -
    have "dI I y (W r) = dI I (W r) y" by (rule dI_comm)
    also have "\<dots> = dI I (\<lambda>i. zr i + (\<Sum>s\<in>T. \<gamma> s * W s i)) y" by (simp add: Wr[abs_def])
    also have "\<dots> = dI I zr y + (\<Sum>s\<in>T. \<gamma> s * dI I (W s) y)" by (simp add: dI_add_left dI_sum_left)
    finally show ?thesis by (simp add: dI_comm)
  qed
  show ?case
  proof (cases "dI I zr zr = 0")
    case True
    have z0: "\<forall>i\<in>I. zr i = 0" using dI_zero[OF I True] by blast
    have zr0: "dI I y zr = 0" for y unfolding dI_def using z0 by simp
    define \<beta>' where "\<beta>' t = (if t = r then 0 else \<beta> t)" for t
    have sumeq: "(\<Sum>s\<in>insert r T. \<beta>' s * W s i) = (\<Sum>s\<in>T. \<beta> s * W s i)" for i
      using insert.hyps unfolding \<beta>'_def by (simp add: sum.insert) (intro sum.cong, auto)
    have "\<forall>t\<in>insert r T. dI I z (W t) = 0"
    proof
      fix t assume "t \<in> insert r T"
      then show "dI I z (W t) = 0"
      proof
        assume "t = r"
        then show ?thesis using dWr[of z] zr0 bz by simp
      qed (use bz in blast)
    qed
    then show ?thesis unfolding z_def sumeq[symmetric] by blast
  next
    case False
    define \<kappa> where "\<kappa> = dI I z zr / dI I zr zr"
    define \<beta>' where "\<beta>' t = (if t = r then \<kappa> else \<beta> t - \<kappa> * \<gamma> t)" for t
    define z' where "z' = (\<lambda>i. z i - \<kappa> * zr i)"
    have sumeq: "v i - (\<Sum>s\<in>insert r T. \<beta>' s * W s i) = z' i" for i
    proof -
      have "(\<Sum>s\<in>insert r T. \<beta>' s * W s i) = \<kappa> * W r i + (\<Sum>s\<in>T. (\<beta> s - \<kappa> * \<gamma> s) * W s i)"
        using insert.hyps unfolding \<beta>'_def by (simp add: sum.insert) (intro sum.cong, auto)
      also have "\<dots> = \<kappa> * zr i + (\<Sum>s\<in>T. \<beta> s * W s i)"
        unfolding Wr by (simp add: algebra_simps sum.distrib sum_subtractf sum_distrib_left)
      finally show ?thesis unfolding z'_def z_def by simp
    qed
    have o1: "dI I z' (W t) = 0" if "t \<in> T" for t
      unfolding z'_def dI_diff_left dI_scale_left using bz gz that by simp
    have o2: "dI I z' zr = 0"
      unfolding z'_def dI_diff_left dI_scale_left \<kappa>_def using False by simp
    have o3: "dI I z' (W r) = 0" using dWr[of z'] o1 o2 by simp
    have "\<forall>t\<in>insert r T. dI I (\<lambda>i. v i - (\<Sum>s\<in>insert r T. \<beta>' s * W s i)) (W t) = 0"
      unfolding sumeq using o1 o3 by blast
    then show ?thesis by blast
  qed
qed

section \<open>One projection step\<close>

lemma bI_outer: "bI I (\<lambda>i j. f i * g j) x y = dI I x f * dI I g y"
  unfolding bI_def dI_def sum_product by (simp add: mult_ac)

lemma qI_pX: "qI I (pX I u X) v = qI I X (pv I u v)"
proof -
  define a where "a j = (\<Sum>l\<in>I. u l * X l j)" for j
  define b where "b i = (\<Sum>k\<in>I. X i k * u k)" for i
  define \<alpha> where "\<alpha> = dI I u v"
  define q where "q = qI I X u"
  have pt: "v i * pX I u X i j * v j = v i * X i j * v j - v i * (u i * a j) * v j
        - v i * (b i * u j) * v j + q * (v i * (u i * u j) * v j)" for i j
    unfolding pX_def a_def b_def q_def by (simp add: algebra_simps)
  have "qI I (pX I u X) v = bI I X v v - bI I (\<lambda>i j. u i * a j) v v - bI I (\<lambda>i j. b i * u j) v v
        + qI I X u * bI I (\<lambda>i j. u i * u j) v v"
    unfolding qI_bI[of I "pX I u X" v] bI_def pt q_def[symmetric]
    by (simp only: sum.distrib sum_subtractf sum_distrib_left)
  also have "bI I (\<lambda>i j. u i * a j) v v = \<alpha> * bI I X u v"
    by (simp only: bI_outer) (simp add: \<alpha>_def bI_col a_def dI_def dI_comm[of I v u] mult_ac)
  also have "bI I (\<lambda>i j. b i * u j) v v = bI I X v u * \<alpha>"
    by (simp only: bI_outer) (simp add: \<alpha>_def bI_row b_def dI_def mult_ac)
  also have "bI I (\<lambda>i j. u i * u j) v v = \<alpha> * \<alpha>"
    by (simp only: bI_outer) (simp add: \<alpha>_def dI_comm[of I v u])
  finally have l: "qI I (pX I u X) v = bI I X v v - \<alpha> * bI I X u v - bI I X v u * \<alpha> + bI I X u u * (\<alpha> * \<alpha>)"
    by (simp add: qI_bI)
  have r: "qI I X (pv I u v) = bI I X v v - \<alpha> * bI I X u v - bI I X v u * \<alpha> + bI I X u u * (\<alpha> * \<alpha>)"
    unfolding qI_bI pv_def \<alpha>_def[symmetric] bI_diff_left bI_diff_right bI_mult_left bI_mult_right
    by (simp add: algebra_simps)
  show ?thesis using l r by simp
qed

lemma dI_pv:
  assumes "dI I u u = 1" shows "dI I (pv I u v) (pv I u v) = dI I v v - (dI I u v)\<^sup>2"
proof -
  have "dI I (pv I u v) (pv I u v) = dI I v v - 2 * dI I u v * dI I u v + (dI I u v)\<^sup>2 * dI I u u"
    unfolding pv_def dI_diff_left dI_diff_right dI_mult_left dI_mult_right
    by (simp add: dI_comm[of I v u] algebra_simps power2_eq_square)
  then show ?thesis using assms by (simp add: power2_eq_square)
qed

lemma leI_pX:
  assumes "leI I X" "dI I u u = 1" shows "leI I (pX I u X)"
  unfolding leI_def
proof
  fix v
  have "qI I (pX I u X) v = qI I X (pv I u v)" by (rule qI_pX)
  also have "\<dots> \<le> dI I (pv I u v) (pv I u v)" using assms(1) unfolding leI_def by blast
  also have "\<dots> \<le> dI I v v" unfolding dI_pv[OF assms(2)] by simp
  finally show "qI I (pX I u X) v \<le> dI I v v" .
qed

lemma symI_pX:
  assumes "symI I X" shows "symI I (pX I u X)"
proof -
  have s: "X j i = X i j" if "i \<in> I" "j \<in> I" for i j using assms that unfolding symI_def by blast
  have r: "(\<Sum>l\<in>I. u l * X l j) = (\<Sum>k\<in>I. X j k * u k)" if "j \<in> I" for j
    by (rule sum.cong) (use s that in \<open>auto simp: mult.commute\<close>)
  show ?thesis unfolding symI_def pX_def using s r by (simp add: algebra_simps)
qed

lemma trI_pX:
  assumes "dI I u u = 1"
  shows "trI I X = trI I (pX I u X) + qI I X u"
proof -
  have a: "(\<Sum>i\<in>I. u i * (\<Sum>l\<in>I. u l * X l i)) = qI I X u"
    unfolding qI_bI bI_col by (simp add: mult.commute)
  have b: "(\<Sum>i\<in>I. (\<Sum>k\<in>I. X i k * u k) * u i) = qI I X u"
    unfolding qI_bI bI_row by (simp add: mult.commute)
  have c: "(\<Sum>i\<in>I. qI I X u * u i * u i) = qI I X u * dI I u u"
    unfolding dI_def by (simp add: sum_distrib_left mult_ac)
  have "trI I (pX I u X) = trI I X - qI I X u - qI I X u + qI I X u * dI I u u"
    unfolding trI_def pX_def using a b c by (simp add: sum.distrib sum_subtractf)
  then show ?thesis using assms by simp
qed

lemma factI_pX:
  assumes F: "factI I T W C X"
  shows "factI I T (\<lambda>t. pv I u (W t)) (\<lambda>t. pv I u (C t)) (pX I u X)"
  unfolding factI_def
proof (intro ballI)
  fix i j assume i: "i \<in> I" and j: "j \<in> I"
  have X: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> X i j = (\<Sum>t\<in>T. W t i * C t j)" using F unfolding factI_def by blast
  have e1: "(\<Sum>l\<in>I. u l * X l j) = (\<Sum>t\<in>T. dI I u (W t) * C t j)"
  proof -
    have "(\<Sum>l\<in>I. u l * X l j) = (\<Sum>l\<in>I. \<Sum>t\<in>T. u l * W t l * C t j)"
      by (intro sum.cong refl) (simp add: X[OF _ j] sum_distrib_left mult_ac)
    also have "\<dots> = (\<Sum>t\<in>T. dI I u (W t) * C t j)"
      unfolding dI_def by (subst sum.swap) (simp add: sum_distrib_right)
    finally show ?thesis .
  qed
  have e2: "(\<Sum>k\<in>I. X i k * u k) = (\<Sum>t\<in>T. W t i * dI I u (C t))"
  proof -
    have "(\<Sum>k\<in>I. X i k * u k) = (\<Sum>k\<in>I. \<Sum>t\<in>T. W t i * (u k * C t k))"
      by (intro sum.cong refl) (simp add: X[OF i] sum_distrib_left sum_distrib_right mult_ac)
    also have "\<dots> = (\<Sum>t\<in>T. W t i * dI I u (C t))"
      unfolding dI_def by (subst sum.swap) (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  have e3: "qI I X u = (\<Sum>t\<in>T. dI I u (W t) * dI I u (C t))"
  proof -
    have "qI I X u = (\<Sum>k\<in>I. u k * (\<Sum>l\<in>I. X k l * u l))"
      unfolding qI_bI bI_row ..
    also have "\<dots> = (\<Sum>k\<in>I. u k * (\<Sum>t\<in>T. W t k * dI I u (C t)))"
    proof (rule sum.cong[OF refl])
      fix k assume k: "k \<in> I"
      have "(\<Sum>l\<in>I. X k l * u l) = (\<Sum>l\<in>I. \<Sum>t\<in>T. W t k * (u l * C t l))"
        by (intro sum.cong refl) (simp add: X[OF k] sum_distrib_left sum_distrib_right mult_ac)
      also have "\<dots> = (\<Sum>t\<in>T. W t k * dI I u (C t))"
        unfolding dI_def by (subst sum.swap) (simp add: sum_distrib_left)
      finally show "u k * (\<Sum>l\<in>I. X k l * u l) = u k * (\<Sum>t\<in>T. W t k * dI I u (C t))" by simp
    qed
    also have "\<dots> = (\<Sum>t\<in>T. dI I u (W t) * dI I u (C t))"
    proof -
      have r: "(\<Sum>k\<in>I. u k * (W t k * c)) = dI I u (W t) * c" for t c
        unfolding dI_def sum_distrib_right by (simp add: mult_ac)
      show ?thesis unfolding sum_distrib_left by (subst sum.swap) (simp add: r)
    qed
    finally show ?thesis .
  qed
  show "pX I u X i j = (\<Sum>t\<in>T. pv I u (W t) i * pv I u (C t) j)"
    unfolding pX_def pv_def e1 e2 e3 X[OF i j]
    by (simp add: algebra_simps sum.distrib sum_subtractf sum_distrib_left sum_distrib_right)
qed

text \<open>If $u=\sum_t\beta_tW_t$ is a unit vector with $\beta_s\neq0$, then $PW_s$ is a combination of the
  other $PW_t$, so $PXP$ factors through $T\setminus\{s\}$.\<close>
lemma factI_drop:
  assumes I: "finite I" and T: "finite T" and s: "s \<in> T" and bs: "\<beta> s \<noteq> 0"
    and F: "factI I T W C X" and u: "\<forall>i\<in>I. u i = (\<Sum>t\<in>T. \<beta> t * W t i)" and uu: "dI I u u = 1"
  shows "factI I (T - {s}) (\<lambda>t. pv I u (W t))
           (\<lambda>t j. pv I u (C t) j - \<beta> t / \<beta> s * pv I u (C s) j) (pX I u X)"
  unfolding factI_def
proof (intro ballI)
  fix i j assume i: "i \<in> I" and j: "j \<in> I"
  define W' where "W' t = pv I u (W t)" for t
  define C' where "C' t = pv I u (C t)" for t
  have Pu: "(\<Sum>t\<in>T. \<beta> t * W' t i) = 0"
  proof -
    have "(\<Sum>t\<in>T. \<beta> t * W' t i) = (\<Sum>t\<in>T. \<beta> t * W t i) - u i * (\<Sum>t\<in>T. \<beta> t * dI I u (W t))"
      unfolding W'_def pv_def by (simp add: algebra_simps sum_subtractf sum_distrib_left)
    also have "(\<Sum>t\<in>T. \<beta> t * dI I u (W t)) = dI I u u"
    proof -
      have "dI I u u = dI I (\<lambda>i. \<Sum>t\<in>T. \<beta> t * W t i) u" by (rule dI_cong) (use u in auto)
      also have "\<dots> = (\<Sum>t\<in>T. \<beta> t * dI I (W t) u)" by (rule dI_sum_left)
      finally show ?thesis by (simp add: dI_comm)
    qed
    finally show ?thesis using u i uu by simp
  qed
  have Ws: "W' s i = - (\<Sum>t\<in>T - {s}. \<beta> t / \<beta> s * W' t i)"
  proof -
    have rm: "(\<Sum>t\<in>T. \<beta> t * W' t i) = \<beta> s * W' s i + (\<Sum>t\<in>T - {s}. \<beta> t * W' t i)"
      using T s by (simp add: sum.remove)
    define S where "S = (\<Sum>t\<in>T - {s}. \<beta> t * W' t i)"
    have e: "\<beta> s * W' s i = - S" using Pu rm unfolding S_def by simp
    have d: "(\<Sum>t\<in>T - {s}. \<beta> t / \<beta> s * W' t i) = S / \<beta> s"
      unfolding S_def sum_divide_distrib by (intro sum.cong refl) simp
    have "W' s i = (\<beta> s * W' s i) / \<beta> s" using bs by simp
    also have "\<dots> = - (S / \<beta> s)" unfolding e by simp
    finally show ?thesis unfolding d .
  qed
  have "pX I u X i j = (\<Sum>t\<in>T. W' t i * C' t j)"
    using factI_pX[OF F, of u] i j unfolding factI_def W'_def C'_def by blast
  also have "\<dots> = W' s i * C' s j + (\<Sum>t\<in>T - {s}. W' t i * C' t j)"
    using T s by (simp add: sum.remove)
  also have "\<dots> = (\<Sum>t\<in>T - {s}. W' t i * (C' t j - \<beta> t / \<beta> s * C' s j))"
    unfolding Ws by (simp add: algebra_simps sum_subtractf sum_distrib_left sum_distrib_right)
  finally show "pX I u X i j = (\<Sum>t\<in>T - {s}. pv I u (W t) i * (pv I u (C t) j - \<beta> t / \<beta> s * pv I u (C s) j))"
    unfolding W'_def C'_def .
qed

section \<open>The trace bounds\<close>

lemma factI_zero:
  assumes "factI I T W C X" "\<forall>t\<in>T. \<forall>i\<in>I. W t i = 0" shows "trI I X = 0"
  using assms unfolding factI_def trI_def by simp

theorem trace_rank_le:
  assumes I: "finite I" and T: "finite T" and S: "symI I X" and L: "leI I X" and F: "factI I T W C X"
  shows "trI I X \<le> real (card T)"
  using T S L F
proof (induction "card T" arbitrary: T W C X)
  case 0
  have "T = {}" using "0.hyps" "0.prems"(1) by simp
  then show ?case using factI_zero[OF "0.prems"(4)] by simp
next
  case (Suc n)
  show ?case
  proof (cases "\<forall>t\<in>T. \<forall>i\<in>I. W t i = 0")
    case True then show ?thesis using factI_zero[OF Suc.prems(4)] by simp
  next
    case False
    then obtain s i0 where s: "s \<in> T" and i0: "i0 \<in> I" "W s i0 \<noteq> 0" by blast
    define \<nu> where "\<nu> = dI I (W s) (W s)"
    have \<nu>: "0 < \<nu>" unfolding \<nu>_def by (rule dI_pos[where u = "W s", OF I i0])
    define \<beta> where "\<beta> t = (if t = s then 1 / sqrt \<nu> else 0)" for t
    define u where "u i = W s i / sqrt \<nu>" for i
    have u: "\<forall>i\<in>I. u i = (\<Sum>t\<in>T. \<beta> t * W t i)"
    proof
      fix i assume "i \<in> I"
      have "(\<Sum>t\<in>T. \<beta> t * W t i) = (\<Sum>t\<in>T. if t = s then W s i / sqrt \<nu> else 0)"
        by (intro sum.cong refl) (simp add: \<beta>_def)
      also have "\<dots> = W s i / sqrt \<nu>" using Suc.prems(1) s by simp
      finally show "u i = (\<Sum>t\<in>T. \<beta> t * W t i)" unfolding u_def by simp
    qed
    have uu: "dI I u u = 1"
      unfolding u_def[abs_def] \<nu>_def by (rule dI_normalize) (use \<nu> \<nu>_def in simp)
    have bs: "\<beta> s \<noteq> 0" unfolding \<beta>_def using \<nu> by simp
    have F': "factI I (T - {s}) (\<lambda>t. pv I u (W t)) (\<lambda>t j. pv I u (C t) j - \<beta> t / \<beta> s * pv I u (C s) j) (pX I u X)"
      by (rule factI_drop[OF I Suc.prems(1) s bs Suc.prems(4) u uu])
    have c: "n = card (T - {s})" using Suc.hyps(2) Suc.prems(1) s by simp
    have IH: "trI I (pX I u X) \<le> real (card (T - {s}))"
      by (rule Suc.hyps(1)[OF c _ symI_pX[OF Suc.prems(2)] leI_pX[OF Suc.prems(3) uu] F']) (use Suc.prems(1) in simp)
    have q: "qI I X u \<le> 1" using Suc.prems(3) uu unfolding leI_def by metis
    have "trI I X = trI I (pX I u X) + qI I X u" by (rule trI_pX[OF uu])
    also have "\<dots> \<le> real (card (T - {s})) + 1" using IH q by simp
    also have "\<dots> = real (card T)" using Suc.prems(1) s Suc.hyps(2) by simp
    finally show ?thesis .
  qed
qed

lemma mulX_kernel:
  assumes S: "symI I X" and F: "factI I T W C X" and z: "\<forall>t\<in>T. dI I z (W t) = 0" and i: "i \<in> I"
  shows "(\<Sum>j\<in>I. X i j * z j) = 0"
proof -
  have "(\<Sum>j\<in>I. X i j * z j) = (\<Sum>j\<in>I. \<Sum>t\<in>T. C t i * (z j * W t j))"
  proof (rule sum.cong[OF refl])
    fix j assume j: "j \<in> I"
    have "X i j = X j i" using S i j unfolding symI_def by blast
    also have "\<dots> = (\<Sum>t\<in>T. W t j * C t i)" using F i j unfolding factI_def by blast
    finally show "X i j * z j = (\<Sum>t\<in>T. C t i * (z j * W t j))"
      by (simp add: sum_distrib_right sum_distrib_left mult_ac)
  qed
  also have "\<dots> = (\<Sum>t\<in>T. C t i * dI I z (W t))"
    unfolding dI_def by (subst sum.swap) (simp add: sum_distrib_left)
  also have "\<dots> = 0" using z by simp
  finally show ?thesis .
qed

theorem trace_rank_neg:
  assumes I: "finite I" and T: "finite T" and S: "symI I X" and L: "leI I X" and F: "factI I T W C X"
    and v: "qI I X v < 0"
  shows "trI I X + 1 < real (card T)"
proof -
  obtain \<beta> where b: "\<forall>t\<in>T. dI I (\<lambda>i. v i - (\<Sum>s\<in>T. \<beta> s * W s i)) (W t) = 0"
    using projection_exists[OF I T] by blast
  define p where "p i = (\<Sum>s\<in>T. \<beta> s * W s i)" for i
  define z where "z i = v i - p i" for i
  have zW: "\<forall>t\<in>T. dI I z (W t) = 0" using b unfolding z_def p_def .
  have Xz: "(\<Sum>j\<in>I. X i j * z j) = 0" if "i \<in> I" for i by (rule mulX_kernel[OF S F zW that])
  have Xz': "(\<Sum>i\<in>I. z i * X i j) = 0" if j: "j \<in> I" for j
  proof -
    have "(\<Sum>i\<in>I. z i * X i j) = (\<Sum>i\<in>I. X j i * z i)"
    proof (rule sum.cong[OF refl])
      fix i assume i: "i \<in> I"
      have "X i j = X j i" using S i j unfolding symI_def by blast
      then show "z i * X i j = X j i * z i" by (simp add: mult.commute)
    qed
    then show ?thesis using Xz[OF j] by simp
  qed
  have qv: "qI I X v = qI I X p"
  proof -
    have vv: "v i = p i + z i" for i unfolding z_def by simp
    have "qI I X v = bI I X p p + bI I X p z + bI I X z p + bI I X z z"
      unfolding qI_bI vv[abs_def] bI_add_left bI_add_right by simp
    moreover have "bI I X p z = 0" "bI I X z z = 0" unfolding bI_row using Xz by simp_all
    moreover have "bI I X z p = 0" unfolding bI_col using Xz' by simp
    ultimately show ?thesis by (simp add: qI_bI)
  qed
  have pneg: "qI I X p < 0" using v qv by simp
  have "\<exists>i\<in>I. p i \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>i\<in>I. p i \<noteq> 0)"
    then have "qI I X p = 0" unfolding qI_def by simp
    then show False using pneg by simp
  qed
  then obtain i0 where i0: "i0 \<in> I" "p i0 \<noteq> 0" by blast
  define \<nu> where "\<nu> = dI I p p"
  have \<nu>: "0 < \<nu>" unfolding \<nu>_def by (rule dI_pos[where u = p, OF I i0])
  define u where "u i = p i / sqrt \<nu>" for i
  define \<beta>' where "\<beta>' t = \<beta> t / sqrt \<nu>" for t
  have u: "\<forall>i\<in>I. u i = (\<Sum>t\<in>T. \<beta>' t * W t i)"
    unfolding u_def \<beta>'_def p_def by (simp add: sum_divide_distrib)
  have uu: "dI I u u = 1"
    unfolding u_def[abs_def] \<nu>_def by (rule dI_normalize) (use \<nu> \<nu>_def in simp)
  have qu: "qI I X u < 0"
  proof -
    have "qI I X u = qI I X p / (sqrt \<nu> * sqrt \<nu>)"
      unfolding qI_def u_def sum_divide_distrib by (intro sum.cong refl) (simp add: field_simps)
    also have "sqrt \<nu> * sqrt \<nu> = \<nu>" using \<nu> by simp
    finally have "qI I X u = qI I X p / \<nu>" .
    then show ?thesis using pneg \<nu> by (simp add: divide_neg_pos)
  qed
  have "\<exists>s\<in>T. \<beta>' s \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>s\<in>T. \<beta>' s \<noteq> 0)"
    then have "\<forall>i\<in>I. u i = 0" using u by simp
    then have "dI I u u = 0" unfolding dI_def by simp
    then show False using uu by simp
  qed
  then obtain s where s: "s \<in> T" and bs: "\<beta>' s \<noteq> 0" by blast
  have F': "factI I (T - {s}) (\<lambda>t. pv I u (W t)) (\<lambda>t j. pv I u (C t) j - \<beta>' t / \<beta>' s * pv I u (C s) j) (pX I u X)"
    by (rule factI_drop[OF I T s bs F u uu])
  have le: "trI I (pX I u X) \<le> real (card (T - {s}))"
    by (rule trace_rank_le[OF I _ symI_pX[OF S] leI_pX[OF L uu] F']) (use T in simp)
  have "trI I X = trI I (pX I u X) + qI I X u" by (rule trI_pX[OF uu])
  also have "\<dots> < real (card (T - {s}))" using le qu by simp
  also have "real (card (T - {s})) = real (card T) - 1"
  proof -
    have "1 \<le> card T" using T s card_gt_0_iff[of T] by auto
    then show ?thesis using T s by (simp add: card_Diff_singleton of_nat_diff)
  qed
  finally show ?thesis by simp
qed

end
