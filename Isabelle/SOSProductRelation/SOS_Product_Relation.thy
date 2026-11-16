(*  Title:      SOS_Product_Relation.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    A nonzero product relation among the forms of a sum of squares lowers its length: Gram version, and heredity from sub-lists
*)

theory SOS_Product_Relation
  imports "HOL-Analysis.Analysis"
begin

text \<open>Two lemmas on sums of squares (Loefberg and Qi). Heredity: if a sub-sum of
squares of some of the forms is a sum of one square fewer, so is the whole sum.
Product relation: a nonzero symmetric matrix annihilating the forms pointwise
lowers the number of squares of the full sum by one. The proof is elementary: no
spectral theorem is used, only compactness of the unit sphere (a maximiser of the
absolute value of the quadratic form) and completion of squares.\<close>

section \<open>Quadratic forms over a finite index set\<close>

definition qf :: "'n set \<Rightarrow> ('n \<Rightarrow> 'n \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real) \<Rightarrow> real" where
  "qf S G x y = (\<Sum>i\<in>S. \<Sum>l\<in>S. G i l * x i * y l)"

definition ebas :: "'n \<Rightarrow> 'n \<Rightarrow> real" where
  "ebas i = (\<lambda>k. if k = i then 1 else 0)"

lemma qf_sym:
  assumes sym: "\<And>i l. G i l = G l i"
  shows "qf S G x y = qf S G y x"
proof -
  have e: "\<And>i l. G i l * y i * x l = G l i * x l * y i"
    by (subst sym) (simp add: ac_simps)
  have "qf S G y x = (\<Sum>i\<in>S. \<Sum>l\<in>S. G l i * x l * y i)"
    unfolding qf_def by (simp add: e)
  also have "\<dots> = (\<Sum>l\<in>S. \<Sum>i\<in>S. G l i * x l * y i)" by (rule sum.swap)
  also have "\<dots> = qf S G x y" unfolding qf_def by simp
  finally show ?thesis by simp
qed

lemma qf_expand:
  assumes sym: "\<And>i l. G i l = G l i"
  shows "qf S G (\<lambda>i. u i + a * w i) (\<lambda>i. u i + a * w i)
       = qf S G u u + 2 * a * qf S G u w + a^2 * qf S G w w"
proof -
  have one: "qf S G (\<lambda>i. u i + a * w i) (\<lambda>i. u i + a * w i)
      = qf S G u u + a * qf S G u w + a * qf S G w u + a^2 * qf S G w w"
    unfolding qf_def
    by (simp add: algebra_simps sum.distrib sum_distrib_left power2_eq_square ac_simps)
  have two: "qf S G w u = qf S G u w" by (rule qf_sym[OF sym])
  have three: "qf S G (\<lambda>i. u i + a * w i) (\<lambda>i. u i + a * w i)
      = qf S G u u + a * qf S G u w + a * qf S G u w + a^2 * qf S G w w"
    using one two by simp
  show ?thesis using three by algebra
qed

lemma qf_cong:
  assumes "\<And>i. i \<in> S \<Longrightarrow> x i = x' i" and "\<And>i. i \<in> S \<Longrightarrow> y i = y' i"
  shows "qf S G x y = qf S G x' y'"
  unfolding qf_def using assms by (intro sum.cong refl) simp

lemma qf_scale:
  "qf S G (\<lambda>i. c * y i) (\<lambda>i. c * y i) = c^2 * qf S G y y"
  unfolding qf_def
  by (simp add: sum_distrib_left power2_eq_square ac_simps)

lemma qf_basis:
  assumes fin: "finite S" and i: "i \<in> S" and l: "l \<in> S"
  shows "qf S G (ebas i) (ebas l) = G i l"
proof -
  have inner: "(\<Sum>b\<in>S. G a b * ebas i a * ebas l b) = ebas i a * G a l" for a
  proof -
    have "(\<Sum>b\<in>S. G a b * ebas i a * ebas l b) = (\<Sum>b\<in>S. (if b = l then G a b * ebas i a else 0))"
      unfolding ebas_def by (intro sum.cong) simp_all
    also have "\<dots> = G a l * ebas i a" using fin l by (simp add: sum.delta)
    finally show "(\<Sum>b\<in>S. G a b * ebas i a * ebas l b) = ebas i a * G a l" by simp
  qed
  have "qf S G (ebas i) (ebas l) = (\<Sum>a\<in>S. ebas i a * G a l)"
    unfolding qf_def using inner by simp
  also have "\<dots> = (\<Sum>a\<in>S. (if a = i then G a l else 0))"
    unfolding ebas_def by (intro sum.cong) simp_all
  also have "\<dots> = G i l" using fin i by (simp add: sum.delta)
  finally show ?thesis .
qed

section \<open>A positive semidefinite form vanishing at a point vanishes against everything\<close>

lemma psd_null:
  assumes sym: "\<And>i l. G i l = G l i"
    and psd: "\<And>y. 0 \<le> qf S G y y" and z: "qf S G u u = 0"
  shows "qf S G u w = 0"
proof (rule ccontr)
  assume ne: "qf S G u w \<noteq> 0"
  define B where "B = qf S G u w"
  define Q where "Q = qf S G w w"
  have Q0: "0 \<le> Q" unfolding Q_def by (rule psd)
  define t where "t = 1 / (Q + 1)"
  have t0: "0 < t" unfolding t_def using Q0 by simp
  have tQ: "t * Q < 1" unfolding t_def using Q0 by (simp add: field_simps)
  have B0: "0 < B^2" using ne unfolding B_def by simp
  have "0 \<le> qf S G (\<lambda>i. u i + (- t * B) * w i) (\<lambda>i. u i + (- t * B) * w i)" by (rule psd)
  also have "\<dots> = qf S G u u + 2 * (- t * B) * qf S G u w + (- t * B)^2 * qf S G w w"
    by (rule qf_expand[OF sym])
  also have "\<dots> = B^2 * t * (t * Q - 2)"
    unfolding z B_def[symmetric] Q_def[symmetric] by algebra
  finally have "0 \<le> B^2 * t * (t * Q - 2)" .
  moreover have "B^2 * t * (t * Q - 2) < 0"
    by (rule mult_pos_neg) (use B0 t0 tQ in \<open>simp_all\<close>)
  ultimately show False by simp
qed

section \<open>Step 2b: a positive semidefinite form is a sum of squares of linear forms\<close>

lemma qf_insert:
  assumes fin: "finite S" and j: "j \<notin> S"
    and sym: "\<And>i l. G i l = G l i"
  shows "qf (insert j S) G y y
    = G j j * (y j)^2 + 2 * y j * (\<Sum>i\<in>S. G j i * y i) + qf S G y y"
proof -
  define F where "F i = (\<Sum>l\<in>insert j S. G i l * y i * y l)" for i
  have "qf (insert j S) G y y = (\<Sum>i\<in>insert j S. F i)" unfolding qf_def F_def by simp
  also have "\<dots> = F j + (\<Sum>i\<in>S. F i)" by (rule sum.insert[OF fin j])
  also have "F j = (\<Sum>l\<in>insert j S. G j l * y j * y l)" unfolding F_def by simp
  also have "(\<Sum>l\<in>insert j S. G j l * y j * y l) = G j j * (y j)^2 + y j * (\<Sum>l\<in>S. G j l * y l)"
    using fin j by (simp add: sum.insert sum_distrib_left power2_eq_square ac_simps)
  also have "(\<Sum>i\<in>S. F i) = (\<Sum>i\<in>S. G i j * y i * y j) + qf S G y y"
    unfolding qf_def F_def using fin j by (simp add: sum.insert sum.distrib)
  also have "(\<Sum>i\<in>S. G i j * y i * y j) = y j * (\<Sum>i\<in>S. G j i * y i)"
    by (simp add: sum_distrib_left sym ac_simps)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma qf_zero_at:
  assumes fin: "finite S" and j: "j \<notin> S" and sym: "\<And>i l. G i l = G l i" and yj: "y j = 0"
  shows "qf (insert j S) G y y = qf S G y y"
  using qf_insert[OF fin j sym, where y = y] yj by simp

lemma psd_sum_squares:
  fixes S :: "'n set"
  assumes "finite S"
  shows "\<And>G. (\<And>i l. G i l = G l i) \<Longrightarrow> (\<And>y. 0 \<le> qf S G y y) \<Longrightarrow>
    \<exists>b. \<forall>y. qf S G y y = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  show ?case by (intro exI[where x = "\<lambda>k i. 0"]) (simp add: qf_def)
next
  case (insert j S)
  note fin = \<open>finite S\<close> and jS = \<open>j \<notin> S\<close>
  have finI: "finite (insert j S)" using fin by simp
  fix G :: "'n \<Rightarrow> 'n \<Rightarrow> real"
  assume sym: "\<And>i l. G i l = G l i"
    and psd: "\<And>y. 0 \<le> qf (insert j S) G y y"
  have cardS: "card (insert j S) = Suc (card S)" using fin jS by simp
  have "0 \<le> G j j"
  proof -
    have "0 \<le> qf (insert j S) G (ebas j) (ebas j)" by (rule psd)
    also have "\<dots> = G j j" by (rule qf_basis) (use fin in simp_all)
    finally show ?thesis .
  qed
  show "\<exists>b. \<forall>y. qf (insert j S) G y y = (\<Sum>k<card (insert j S). (\<Sum>i\<in>insert j S. b k i * y i)^2)"
  proof (cases "G j j = 0")
    case True
    have gj: "G j l = 0" if l: "l \<in> insert j S" for l
    proof -
      have z: "qf (insert j S) G (ebas j) (ebas j) = 0"
        using True by (simp add: qf_basis[OF finI])
      have "qf (insert j S) G (ebas j) (ebas l) = 0"
        by (rule psd_null[OF sym psd z])
      then show "G j l = 0" using qf_basis[OF finI] l by simp
    qed
    have red: "qf (insert j S) G y y = qf S G y y" for y
    proof -
      have "qf (insert j S) G y y = G j j * (y j)^2 + 2 * y j * (\<Sum>i\<in>S. G j i * y i) + qf S G y y"
        by (rule qf_insert[OF fin jS sym])
      also have "\<dots> = qf S G y y" using True gj by simp
      finally show "qf (insert j S) G y y = qf S G y y" .
    qed
    have psdS: "\<And>y. 0 \<le> qf S G y y" using psd red by simp
    obtain b where b: "\<And>y. qf S G y y = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2)"
      using insert.IH[OF sym psdS] by blast
    define b' where "b' = (\<lambda>k i. if k = card S \<or> i = j then 0 else b k i)"
    have inner: "(\<Sum>i\<in>insert j S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)" if k: "k < card S" for y k
    proof -
      have "(\<Sum>i\<in>insert j S. b' k i * y i) = b' k j * y j + (\<Sum>i\<in>S. b' k i * y i)"
        by (rule sum.insert[OF fin jS])
      moreover have "b' k j = 0" unfolding b'_def by simp
      moreover have "(\<Sum>i\<in>S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)"
        unfolding b'_def using jS k by (intro sum.cong) auto
      ultimately show "(\<Sum>i\<in>insert j S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)" by simp
    qed
    show ?thesis
    proof (rule exI[where x = b'], rule allI)
      fix y
      have "(\<Sum>k<Suc (card S). (\<Sum>i\<in>insert j S. b' k i * y i)^2)
          = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2) + (\<Sum>i\<in>insert j S. b' (card S) i * y i)^2"
        by (simp add: sum.lessThan_Suc inner)
      moreover have "(\<Sum>i\<in>insert j S. b' (card S) i * y i) = 0" unfolding b'_def by simp
      ultimately show "qf (insert j S) G y y = (\<Sum>k<card (insert j S). (\<Sum>i\<in>insert j S. b' k i * y i)^2)"
        using red b cardS by simp
    qed
  next
    case False
    define a where "a = G j j"
    have a0: "0 < a" using False \<open>0 \<le> G j j\<close> unfolding a_def by simp
    define G' where "G' = (\<lambda>i l. G i l - G j i * G j l / a)"
    have sym': "\<And>i l. G' i l = G' l i" unfolding G'_def by (simp add: sym ac_simps)
    define s where "s y = (\<Sum>i\<in>S. G j i * y i)" for y
    have split: "qf (insert j S) G y y = a * (y j + s y / a)^2 + qf S G' y y" for y
    proof -
      have prod: "(\<Sum>i\<in>S. \<Sum>l\<in>S. G j i * G j l / a * y i * y l) = (s y)^2 / a"
      proof -
        have "(\<Sum>i\<in>S. \<Sum>l\<in>S. G j i * G j l / a * y i * y l)
            = (\<Sum>i\<in>S. \<Sum>l\<in>S. (G j i * y i) * (G j l * y l)) / a"
          by (simp add: sum_divide_distrib ac_simps)
        also have "\<dots> = (s y)^2 / a"
          unfolding s_def by (simp add: sum_product power2_eq_square)
        finally show ?thesis .
      qed
      have "qf S G' y y = qf S G y y - (s y)^2 / a"
        unfolding qf_def G'_def using prod
        by (simp add: algebra_simps sum_subtractf)
      moreover have "qf (insert j S) G y y = a * (y j)^2 + 2 * y j * s y + qf S G y y"
        unfolding a_def s_def by (rule qf_insert[OF fin jS sym])
      moreover have "a * (y j + s y / a)^2 = a * (y j)^2 + 2 * y j * s y + (s y)^2 / a"
        using a0 by (simp add: field_simps power2_eq_square)
      ultimately show "qf (insert j S) G y y = a * (y j + s y / a)^2 + qf S G' y y"
        by linarith
    qed
    have sfree: "\<And>y v. s (y(j := v)) = s y"
      unfolding s_def using jS by (intro sum.cong) auto
    have psd': "0 \<le> qf S G' y y" for y
    proof -
      define y' where "y' = y(j := - s y / a)"
      have "0 \<le> qf (insert j S) G y' y'" by (rule psd)
      also have "\<dots> = a * (y' j + s y' / a)^2 + qf S G' y' y'" by (rule split)
      also have "y' j + s y' / a = 0" unfolding y'_def sfree using a0 by simp
      also have "qf S G' y' y' = qf S G' y y"
        by (rule qf_cong) (use jS in \<open>auto simp: y'_def\<close>)
      finally show "0 \<le> qf S G' y y" by simp
    qed
    obtain b where b: "\<And>y. qf S G' y y = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2)"
      using insert.IH[OF sym' psd'] by blast
    define b' where "b' = (\<lambda>k i. if k = card S then G j i / sqrt a else if i = j then 0 else b k i)"
    have inner: "(\<Sum>i\<in>insert j S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)" if k: "k < card S" for y k
    proof -
      have "(\<Sum>i\<in>insert j S. b' k i * y i) = b' k j * y j + (\<Sum>i\<in>S. b' k i * y i)"
        by (rule sum.insert[OF fin jS])
      moreover have "b' k j = 0" unfolding b'_def using k by simp
      moreover have "(\<Sum>i\<in>S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)"
        unfolding b'_def using jS k by (intro sum.cong) auto
      ultimately show "(\<Sum>i\<in>insert j S. b' k i * y i) = (\<Sum>i\<in>S. b k i * y i)" by simp
    qed
    have top: "(\<Sum>i\<in>insert j S. b' (card S) i * y i)^2 = a * (y j + s y / a)^2" for y
    proof -
      have "(\<Sum>i\<in>insert j S. b' (card S) i * y i) = (a * y j + s y) / sqrt a"
        unfolding b'_def using fin jS
        by (simp add: sum.insert a_def[symmetric] s_def add_divide_distrib sum_divide_distrib)
      then have "(\<Sum>i\<in>insert j S. b' (card S) i * y i)^2 = (a * y j + s y)^2 / a"
        using a0 by (simp add: power_divide)
      also have "\<dots> = a * (y j + s y / a)^2" using a0 by (simp add: field_simps power2_eq_square)
      finally show "(\<Sum>i\<in>insert j S. b' (card S) i * y i)^2 = a * (y j + s y / a)^2" .
    qed
    show ?thesis
    proof (rule exI[where x = b'], rule allI)
      fix y
      have "(\<Sum>k<Suc (card S). (\<Sum>i\<in>insert j S. b' k i * y i)^2)
          = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2) + (\<Sum>i\<in>insert j S. b' (card S) i * y i)^2"
        by (simp add: sum.lessThan_Suc inner)
      then show "qf (insert j S) G y y = (\<Sum>k<card (insert j S). (\<Sum>i\<in>insert j S. b' k i * y i)^2)"
        using split b top cardS by simp
    qed
  qed
qed

section \<open>Lemma 4.17: heredity\<close>

lemma hered_step:
  fixes f :: "'n \<Rightarrow> 'x \<Rightarrow> real"
  assumes fin: "finite S" and ne: "S \<noteq> {}" and t: "t \<notin> S"
    and hyp: "\<exists>B. \<forall>x. (\<Sum>i\<in>S. (f i x)^2) = (\<Sum>k<card S - 1. (\<Sum>i\<in>S. B k i * f i x)^2)"
  shows "\<exists>B. \<forall>x. (\<Sum>i\<in>insert t S. (f i x)^2)
      = (\<Sum>k<card (insert t S) - 1. (\<Sum>i\<in>insert t S. B k i * f i x)^2)"
proof -
  obtain B where B: "\<And>x. (\<Sum>i\<in>S. (f i x)^2) = (\<Sum>k<card S - 1. (\<Sum>i\<in>S. B k i * f i x)^2)"
    using hyp by blast
  define m where "m = card S - 1"
  have cS: "card S = Suc m" using fin ne unfolding m_def by (simp add: card_gt_0_iff Suc_pred)
  have cI: "card (insert t S) - 1 = Suc m" using fin t cS by simp
  define B' where "B' = (\<lambda>k i. if k = m then (if i = t then 1 else 0)
                                else if i = t then 0 else B k i)"
  have inner: "(\<Sum>i\<in>insert t S. B' k i * f i x) = (\<Sum>i\<in>S. B k i * f i x)" if k: "k < m" for x k
  proof -
    have "(\<Sum>i\<in>insert t S. B' k i * f i x) = B' k t * f t x + (\<Sum>i\<in>S. B' k i * f i x)"
      by (rule sum.insert[OF fin t])
    moreover have "B' k t = 0" unfolding B'_def using k by simp
    moreover have "(\<Sum>i\<in>S. B' k i * f i x) = (\<Sum>i\<in>S. B k i * f i x)"
      unfolding B'_def using t k by (intro sum.cong) auto
    ultimately show "(\<Sum>i\<in>insert t S. B' k i * f i x) = (\<Sum>i\<in>S. B k i * f i x)" by simp
  qed
  have top: "(\<Sum>i\<in>insert t S. B' m i * f i x) = f t x" for x
  proof -
    have "(\<Sum>i\<in>insert t S. B' m i * f i x) = B' m t * f t x + (\<Sum>i\<in>S. B' m i * f i x)"
      by (rule sum.insert[OF fin t])
    moreover have "(\<Sum>i\<in>S. B' m i * f i x) = 0"
      unfolding B'_def using t by (intro sum.neutral) auto
    ultimately show "(\<Sum>i\<in>insert t S. B' m i * f i x) = f t x" unfolding B'_def by simp
  qed
  show ?thesis
  proof (rule exI[where x = B'], rule allI)
    fix x
    have "(\<Sum>k<Suc m. (\<Sum>i\<in>insert t S. B' k i * f i x)^2)
        = (\<Sum>k<m. (\<Sum>i\<in>S. B k i * f i x)^2) + (f t x)^2"
      by (simp add: sum.lessThan_Suc inner top)
    moreover have "(\<Sum>i\<in>insert t S. (f i x)^2) = (f t x)^2 + (\<Sum>i\<in>S. (f i x)^2)"
      by (rule sum.insert[OF fin t])
    ultimately show "(\<Sum>i\<in>insert t S. (f i x)^2)
        = (\<Sum>k<card (insert t S) - 1. (\<Sum>i\<in>insert t S. B' k i * f i x)^2)"
      using B[where x = x] cI unfolding m_def[symmetric] by simp
  qed
qed

theorem heredity:
  fixes f :: "'n \<Rightarrow> 'x \<Rightarrow> real"
  assumes fin: "finite A" and sub: "S \<subseteq> A" and ne: "S \<noteq> {}"
    and hyp: "\<exists>B. \<forall>x. (\<Sum>i\<in>S. (f i x)^2) = (\<Sum>k<card S - 1. (\<Sum>i\<in>S. B k i * f i x)^2)"
  shows "\<exists>B. \<forall>x. (\<Sum>i\<in>A. (f i x)^2) = (\<Sum>k<card A - 1. (\<Sum>i\<in>A. B k i * f i x)^2)"
proof -
  have finT: "finite (A - S)" using fin by simp
  have "\<And>T. finite T \<Longrightarrow> \<exists>B. \<forall>x. (\<Sum>i\<in>S \<union> T. (f i x)^2)
      = (\<Sum>k<card (S \<union> T) - 1. (\<Sum>i\<in>S \<union> T. B k i * f i x)^2)"
  proof -
    fix T :: "'n set" assume "finite T"
    then show "\<exists>B. \<forall>x. (\<Sum>i\<in>S \<union> T. (f i x)^2)
      = (\<Sum>k<card (S \<union> T) - 1. (\<Sum>i\<in>S \<union> T. B k i * f i x)^2)"
    proof (induction T rule: finite_induct)
      case empty
      show ?case using hyp by simp
    next
      case (insert t T)
      show ?case
      proof (cases "t \<in> S \<union> T")
        case True
        then have "S \<union> insert t T = S \<union> T" by auto
        then show ?thesis using insert.IH by simp
      next
        case False
        have fST: "finite (S \<union> T)" using fin sub \<open>finite T\<close> finite_subset by blast
        have "S \<union> insert t T = insert t (S \<union> T)" by auto
        moreover have "\<exists>B. \<forall>x. (\<Sum>i\<in>insert t (S \<union> T). (f i x)^2)
          = (\<Sum>k<card (insert t (S \<union> T)) - 1. (\<Sum>i\<in>insert t (S \<union> T). B k i * f i x)^2)"
          by (rule hered_step[OF fST _ False insert.IH]) (use ne in auto)
        ultimately show ?thesis by simp
      qed
    qed
  qed
  from this[OF finT] have "\<exists>B. \<forall>x. (\<Sum>i\<in>S \<union> (A - S). (f i x)^2)
      = (\<Sum>k<card (S \<union> (A - S)) - 1. (\<Sum>i\<in>S \<union> (A - S). B k i * f i x)^2)" .
  moreover have "S \<union> (A - S) = A" using sub by auto
  ultimately show ?thesis by simp
qed

section \<open>The extremal quadratic form (compactness of the unit sphere)\<close>

lemma qf_id:
  assumes "finite S"
  shows "qf S (\<lambda>i l. if i = l then 1 else 0) y y = (\<Sum>i\<in>S. (y i)^2)"
proof -
  have "(\<Sum>l\<in>S. (if i = l then 1 else 0) * y i * y l) = (y i)^2" if i: "i \<in> S" for i
  proof -
    have "(\<Sum>l\<in>S. (if i = l then 1 else 0) * y i * y l)
        = (\<Sum>l\<in>S. (if l = i then (y i)^2 else 0))"
      by (intro sum.cong) (auto simp: power2_eq_square)
    also have "\<dots> = (y i)^2" using assms i by (simp add: sum.delta)
    finally show "(\<Sum>l\<in>S. (if i = l then 1 else 0) * y i * y l) = (y i)^2" .
  qed
  then show ?thesis unfolding qf_def by (intro sum.cong) simp_all
qed

lemma sumsq_norm:
  fixes x :: "real^'n::finite"
  shows "(\<Sum>i\<in>UNIV. (x $ i)^2) = (norm x)^2"
proof -
  have "(\<Sum>i\<in>UNIV. (x $ i)^2) = x \<bullet> x" by (simp add: inner_vec_def power2_eq_square)
  also have "\<dots> = (norm x)^2" by (rule dot_square_norm)
  finally show ?thesis .
qed

lemma exists_extremal:
  fixes C :: "'n::finite \<Rightarrow> 'n \<Rightarrow> real"
  assumes sym: "\<And>i l. C i l = C l i" and ne: "\<exists>i l. C i l \<noteq> 0"
  shows "\<exists>t u. (\<exists>j. u j \<noteq> 0) \<and> (\<forall>y. t * qf UNIV C y y \<le> (\<Sum>i\<in>UNIV. (y i)^2))
      \<and> t * qf UNIV C u u = (\<Sum>i\<in>UNIV. (u i)^2)"
proof -
  obtain i0 l0 where il: "C i0 l0 \<noteq> 0" using ne by blast
  define phi where "phi x = \<bar>qf UNIV C (\<lambda>i. x $ i) (\<lambda>i. x $ i)\<bar>" for x :: "real^'n"
  have cont: "continuous_on (sphere (0::real^'n) 1) phi"
    unfolding phi_def qf_def by (intro continuous_intros)
  have comp: "compact (sphere (0::real^'n) 1)" by (rule compact_sphere)
  have nonempty: "sphere (0::real^'n) 1 \<noteq> {}"
  proof -
    have "axis i0 (1::real) \<in> sphere (0::real^'n) 1" by (simp add: norm_axis_1)
    then show ?thesis by blast
  qed
  obtain x0 where x0: "x0 \<in> sphere 0 1" and mx: "\<And>x. x \<in> sphere 0 1 \<Longrightarrow> phi x \<le> phi x0"
    using continuous_attains_sup[OF comp nonempty cont] by blast
  define m where "m = phi x0"
  define u where "u = (\<lambda>i. x0 $ i)"
  have m0: "0 \<le> m" unfolding m_def phi_def by simp
  have nx0: "norm x0 = 1" using x0 by simp
  have su: "(\<Sum>i\<in>UNIV. (u i)^2) = 1" unfolding u_def using sumsq_norm[where x = x0] nx0 by simp
  have bound: "\<And>y. \<bar>qf UNIV C y y\<bar> \<le> m * (\<Sum>i\<in>UNIV. (y i)^2)"
  proof -
    fix y :: "'n \<Rightarrow> real"
    define x where "x = (\<chi> i. y i)"
    have xy: "\<And>i. x $ i = y i" unfolding x_def by simp
    have sx: "(\<Sum>i\<in>UNIV. (y i)^2) = (norm x)^2" using sumsq_norm[where x = x] xy by simp
    show "\<bar>qf UNIV C y y\<bar> \<le> m * (\<Sum>i\<in>UNIV. (y i)^2)"
    proof (cases "x = 0")
      case True
      have "y i = 0" for i
      proof -
        have "y i = x $ i" by (simp add: xy)
        also have "\<dots> = 0" using True by simp
        finally show "y i = 0" .
      qed
      then show ?thesis by (simp add: qf_def)
    next
      case False
      define r where "r = norm x"
      have r0: "0 < r" unfolding r_def using False by simp
      define z where "z = (1 / r) *\<^sub>R x"
      have nz: "z \<in> sphere 0 1" unfolding z_def r_def using False by (simp add: norm_scaleR)
      have zc: "\<And>i. z $ i = (1 / r) * y i" unfolding z_def using xy by simp
      have "phi z = \<bar>qf UNIV C (\<lambda>i. (1 / r) * y i) (\<lambda>i. (1 / r) * y i)\<bar>"
        unfolding phi_def by (simp only: qf_cong[where x = "\<lambda>i. z $ i" and x' = "\<lambda>i. (1 / r) * y i"
              and y = "\<lambda>i. z $ i" and y' = "\<lambda>i. (1 / r) * y i", OF zc zc])
      also have "\<dots> = (1 / r)^2 * \<bar>qf UNIV C y y\<bar>"
        by (subst qf_scale) (simp add: abs_mult)
      finally have "(1 / r)^2 * \<bar>qf UNIV C y y\<bar> \<le> m" using mx[OF nz] unfolding m_def by simp
      then have "\<bar>qf UNIV C y y\<bar> \<le> m * r^2" using r0 by (simp add: field_simps power2_eq_square)
      then show ?thesis using sx unfolding r_def by simp
    qed
  qed
  have mpos: "0 < m"
  proof (rule ccontr)
    assume "\<not> 0 < m"
    with m0 have m00: "m = 0" by simp
    have z0: "qf UNIV C y y = 0" for y
    proof -
      have "\<bar>qf UNIV C y y\<bar> \<le> 0" using bound[where y = y] m00 by simp
      then show "qf UNIV C y y = 0" by simp
    qed
    have "qf UNIV C (\<lambda>i. ebas i0 i + 1 * ebas l0 i) (\<lambda>i. ebas i0 i + 1 * ebas l0 i)
        = qf UNIV C (ebas i0) (ebas i0) + 2 * 1 * qf UNIV C (ebas i0) (ebas l0)
          + 1^2 * qf UNIV C (ebas l0) (ebas l0)"
      by (rule qf_expand[OF sym])
    moreover have "qf UNIV C (ebas i0) (ebas l0) = C i0 l0" by (rule qf_basis) simp_all
    ultimately have "2 * C i0 l0 = 0" using z0 by simp
    with il show False by simp
  qed
  have ju: "\<exists>j. u j \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>j. u j \<noteq> 0)"
    then have "\<And>j. u j = 0" by simp
    then have "(\<Sum>i\<in>UNIV. (u i)^2) = 0" by simp
    with su show False by simp
  qed
  have qu: "\<bar>qf UNIV C u u\<bar> = m" unfolding m_def phi_def u_def by simp
  define t where "t = (if 0 \<le> qf UNIV C u u then 1 / m else - 1 / m)"
  have tabs: "\<bar>t\<bar> = 1 / m" unfolding t_def using mpos by simp
  have tu: "t * qf UNIV C u u = 1"
  proof (cases "0 \<le> qf UNIV C u u")
    case True
    then have "qf UNIV C u u = m" using qu by simp
    then show ?thesis unfolding t_def using True mpos by simp
  next
    case False
    then have "qf UNIV C u u = - m" using qu by simp
    then show ?thesis unfolding t_def using False mpos by simp
  qed
  have tb: "t * qf UNIV C y y \<le> (\<Sum>i\<in>UNIV. (y i)^2)" for y
  proof -
    have "t * qf UNIV C y y \<le> \<bar>t * qf UNIV C y y\<bar>" by (rule abs_ge_self)
    also have "\<dots> = (1 / m) * \<bar>qf UNIV C y y\<bar>" using tabs by (simp add: abs_mult)
    also have "\<dots> \<le> (1 / m) * (m * (\<Sum>i\<in>UNIV. (y i)^2))"
      using bound mpos by (intro mult_left_mono) simp_all
    also have "\<dots> = (\<Sum>i\<in>UNIV. (y i)^2)" using mpos by simp
    finally show "t * qf UNIV C y y \<le> (\<Sum>i\<in>UNIV. (y i)^2)" .
  qed
  show ?thesis using ju tb tu su by (intro exI[where x = t] exI[where x = u]) simp
qed

section \<open>A positive semidefinite form with a kernel vector has one square fewer\<close>

lemma kernel_reduction:
  fixes G :: "'n::finite \<Rightarrow> 'n \<Rightarrow> real"
  assumes sym: "\<And>i l. G i l = G l i" and psd: "\<And>y. 0 \<le> qf UNIV G y y"
    and uj: "u j \<noteq> 0" and z: "qf UNIV G u u = 0"
  shows "\<exists>B. \<forall>v. qf UNIV G v v
      = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * v i)^2)"
proof -
  define S where "S = UNIV - {j}"
  have finS: "finite S" by simp
  have jS: "j \<notin> S" unfolding S_def by simp
  have U: "UNIV = insert j S" unfolding S_def by auto
  have cardS: "card S = card (UNIV :: 'n set) - 1" unfolding S_def by (simp add: card_Diff_singleton)
  have hk: "\<And>w. qf UNIV G u w = 0" by (rule psd_null[OF sym psd z])
  have psdS: "\<And>y. 0 \<le> qf S G y y"
  proof -
    fix y :: "'n \<Rightarrow> real"
    define y0 where "y0 = y(j := (0::real))"
    have "0 \<le> qf UNIV G y0 y0" by (rule psd)
    also have "qf UNIV G y0 y0 = qf (insert j S) G y0 y0" by (simp only: U)
    also have "\<dots> = qf S G y0 y0" by (rule qf_zero_at[OF finS jS sym]) (simp add: y0_def)
    also have "\<dots> = qf S G y y" by (rule qf_cong) (use jS in \<open>auto simp: y0_def\<close>)
    finally show "0 \<le> qf S G y y" .
  qed
  obtain b where b: "\<And>y. qf S G y y = (\<Sum>k<card S. (\<Sum>i\<in>S. b k i * y i)^2)"
    using psd_sum_squares[OF finS sym psdS] by blast
  define B where "B = (\<lambda>k i. if i = j then - (\<Sum>l\<in>S. b k l * u l) / u j else b k i)"
  show ?thesis
  proof (rule exI[where x = B], rule allI)
    fix v :: "'n \<Rightarrow> real"
    define c where "c = v j / u j"
    define g where "g = (\<lambda>i. v i - c * u i)"
    have vg: "\<And>i. v i = g i + c * u i" unfolding g_def by simp
    have e1: "qf UNIV G v v = qf UNIV G (\<lambda>i. g i + c * u i) (\<lambda>i. g i + c * u i)"
      by (rule qf_cong) (simp_all add: vg)
    also have "\<dots> = qf UNIV G g g + 2 * c * qf UNIV G g u + c^2 * qf UNIV G u u"
      by (rule qf_expand[where u = g and w = u and a = c, OF sym])
    also have "qf UNIV G g u = 0" using qf_sym[OF sym, where x = g and y = u] hk by simp
    also have "qf UNIV G u u = 0" by (rule z)
    finally have e2: "qf UNIV G v v = qf UNIV G g g" by simp
    have gj: "g j = 0" unfolding g_def c_def using uj by simp
    have e3: "qf UNIV G g g = qf S G g g"
    proof -
      have "qf UNIV G g g = qf (insert j S) G g g" by (simp only: U)
      also have "\<dots> = qf S G g g" by (rule qf_zero_at[OF finS jS sym]) (rule gj)
      finally show ?thesis .
    qed
    have key: "(\<Sum>i\<in>UNIV. B k i * v i) = (\<Sum>i\<in>S. b k i * g i)" for k
    proof -
      have "(\<Sum>i\<in>UNIV. B k i * v i) = B k j * v j + (\<Sum>i\<in>S. B k i * v i)"
        unfolding U by (rule sum.insert[OF finS jS])
      moreover have "(\<Sum>i\<in>S. B k i * v i) = (\<Sum>i\<in>S. b k i * v i)"
        unfolding B_def using jS by (intro sum.cong) auto
      moreover have "(\<Sum>i\<in>S. b k i * g i) = (\<Sum>i\<in>S. b k i * v i) - c * (\<Sum>i\<in>S. b k i * u i)"
        unfolding g_def by (simp add: algebra_simps sum_subtractf sum_distrib_left)
      moreover have "B k j * v j = - c * (\<Sum>i\<in>S. b k i * u i)"
        unfolding B_def c_def by (simp add: field_simps)
      ultimately show "(\<Sum>i\<in>UNIV. B k i * v i) = (\<Sum>i\<in>S. b k i * g i)" by simp
    qed
    show "qf UNIV G v v = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * v i)^2)"
      unfolding e2 e3 b[where y = g] cardS[symmetric] by (simp add: key)
  qed
qed

section \<open>Lemma B.2: a product relation lowers the number of squares\<close>

lemma qf_sub:
  "qf S (\<lambda>i l. A i l - t * C i l) y y = qf S A y y - t * qf S C y y"
  unfolding qf_def by (simp add: algebra_simps sum_subtractf sum_distrib_left)

text \<open>Step 2a, the Gram version. Under a product relation there is a positive
semidefinite matrix with a kernel vector which represents the sum of squares
at every point.\<close>

theorem gram_version:
  fixes f :: "'n::finite \<Rightarrow> 'x \<Rightarrow> real" and C :: "'n \<Rightarrow> 'n \<Rightarrow> real"
  assumes sym: "\<And>i l. C i l = C l i" and ne: "\<exists>i l. C i l \<noteq> 0"
    and rel: "\<And>x. (\<Sum>i\<in>UNIV. \<Sum>l\<in>UNIV. C i l * f i x * f l x) = 0"
  shows "\<exists>G u j. (\<forall>i l. G i l = G l i) \<and> (\<forall>y. 0 \<le> qf UNIV G y y) \<and> u j \<noteq> 0
      \<and> (\<forall>w. qf UNIV G u w = 0)
      \<and> (\<forall>x. (\<Sum>i\<in>UNIV. (f i x)^2) = qf UNIV G (\<lambda>i. f i x) (\<lambda>i. f i x))"
proof -
  obtain t u where ex: "\<exists>j. u j \<noteq> 0"
    and tb: "\<And>y. t * qf UNIV C y y \<le> (\<Sum>i\<in>UNIV. (y i)^2)"
    and tu: "t * qf UNIV C u u = (\<Sum>i\<in>UNIV. (u i)^2)"
    using exists_extremal[OF sym ne] by blast
  obtain j where uj: "u j \<noteq> 0" using ex by blast
  define G where "G = (\<lambda>i l. (if i = l then 1 else 0) - t * C i l)"
  have qG: "\<And>y. qf UNIV G y y = (\<Sum>i\<in>UNIV. (y i)^2) - t * qf UNIV C y y"
    unfolding G_def by (simp add: qf_sub qf_id)
  have symG: "\<And>i l. G i l = G l i" unfolding G_def by (simp add: sym eq_commute)
  have psdG: "\<And>y. 0 \<le> qf UNIV G y y" using qG tb by simp
  have zG: "qf UNIV G u u = 0" using qG tu by simp
  have hk: "\<And>w. qf UNIV G u w = 0" by (rule psd_null[OF symG psdG zG])
  have rep: "(\<Sum>i\<in>UNIV. (f i x)^2) = qf UNIV G (\<lambda>i. f i x) (\<lambda>i. f i x)" for x
  proof -
    have "qf UNIV C (\<lambda>i. f i x) (\<lambda>i. f i x) = 0" using rel[where x = x] unfolding qf_def by simp
    then show "(\<Sum>i\<in>UNIV. (f i x)^2) = qf UNIV G (\<lambda>i. f i x) (\<lambda>i. f i x)" using qG by simp
  qed
  show ?thesis using symG psdG uj hk rep by blast
qed

theorem product_relation_reduces:
  fixes f :: "'n::finite \<Rightarrow> 'x \<Rightarrow> real" and C :: "'n \<Rightarrow> 'n \<Rightarrow> real"
  assumes sym: "\<And>i l. C i l = C l i" and ne: "\<exists>i l. C i l \<noteq> 0"
    and rel: "\<And>x. (\<Sum>i\<in>UNIV. \<Sum>l\<in>UNIV. C i l * f i x * f l x) = 0"
  shows "\<exists>B. \<forall>x. (\<Sum>i\<in>UNIV. (f i x)^2)
      = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * f i x)^2)"
proof -
  obtain G u j where symG: "\<And>i l. G i l = G l i" and psdG: "\<And>y. 0 \<le> qf UNIV G y y"
    and uj: "u j \<noteq> 0" and hk: "\<And>w. qf UNIV G u w = 0"
    and rep: "\<forall>x. (\<Sum>i\<in>UNIV. (f i x)^2) = qf UNIV G (\<lambda>i. f i x) (\<lambda>i. f i x)"
    using gram_version[where f = f and C = C, OF sym ne rel] by blast
  obtain B where B: "\<And>v. qf UNIV G v v = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * v i)^2)"
    using kernel_reduction[OF symG psdG uj hk[where w = u]] by blast
  show ?thesis
  proof (rule exI[where x = B], rule allI)
    fix x
    have "(\<Sum>i\<in>UNIV. (f i x)^2) = qf UNIV G (\<lambda>i. f i x) (\<lambda>i. f i x)" using rep by blast
    also have "\<dots> = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * f i x)^2)"
      by (rule B[where v = "\<lambda>i. f i x"])
    finally show "(\<Sum>i\<in>UNIV. (f i x)^2) = (\<Sum>k<card (UNIV :: 'n set) - 1. (\<Sum>i\<in>UNIV. B k i * f i x)^2)" .
  qed
qed

end
