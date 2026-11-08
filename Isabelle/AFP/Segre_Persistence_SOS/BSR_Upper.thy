(*  Title:      BSR_Upper.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: BSR(m,n) <= mn - max(m,n) + 1 from the width-two bound of BSSV (explicit hypothesis) *)
section \<open>An upper bound for the biquadratic SOS rank\<close>

theory BSR_Upper
  imports Coefficient_Vectors
begin

text \<open>Upper bound $\mathrm{BSR}(m,n)\le mn-\max(m,n)+1$ (Theorem 9 of the note @{cite Marin2026}).
  A sum of $r$ squares of bilinear forms in $x\in\mathbb{R}^m$,
  $y\in\mathbb{R}^n$ is given by coefficients \<open>c i j k\<close>: the coefficient of $x_iy_j$ in the $k$-th
  bilinear form, so \<open>c i j\<close> is the coefficient vector $v_{ij}\in\mathbb{R}^r$ of the note.

  The step ``a form of size $m\times 2$ is a sum of $m+1$ squares'' is Theorem 1.4 of Blekherman,
  Sinn, Smith and Velasco @{cite BSSV}. It is \emph{not} proved here: it enters the main theorem
  \<open>bsr_upper\<close> as the explicit hypothesis \<open>BSSV_1_4\<close>. The rest of the proof is formalized.

  Route: instead of an explicit orthogonal change of coordinates, the vectors $v_{ij}$ with
  $j\ge 2$ are removed one at a time by orthogonal projection (Gram--Schmidt). Projecting the
  whole representation away from a nonzero vector $u$ splits off exactly one square and leaves a
  representation with the same $r$ coordinates in which $u$'s own vector becomes $0$. After the
  $m(n-2)$ vectors with $j\ge2$ are removed, the remainder only involves $y_0,y_1$.\<close>

subsection \<open>Representations by sums of squares\<close>

definition bil :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "bil m n a x y = (\<Sum>i<m. \<Sum>j<n. a i j * x i * y j)"

text \<open>The biquadratic form $\sum_{k<r} b_k(x,y)^2$ with $b_k(x,y)=\sum_{i<m,j<n} c_{ijk}x_iy_j$.\<close>
definition sos_form :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow>
    (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "sos_form m n r c x y = (\<Sum>k<r. (bil m n (\<lambda>i j. c i j k) x y)\<^sup>2)"

text \<open>\<open>bsr_le m n N\<close>: every real sum of squares of bilinear forms of size $m\times n$ (with any number
  $r$ of squares) is the same form as a sum of at most $N$ squares; that is, $\mathrm{BSR}(m,n)\le N$.\<close>
definition bsr_le :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bsr_le m n N \<longleftrightarrow> (\<forall>r c. \<exists>s\<le>N. \<exists>c'. \<forall>x y. sos_form m n r c x y = sos_form m n s c' x y)"

subsection \<open>Algebra of bilinear forms\<close>

lemma bil_diff_scale:
  "bil m n (\<lambda>i j. p i j - q i j * t) x y = bil m n p x y - bil m n q x y * t"
proof -
  have "bil m n (\<lambda>i j. p i j - q i j * t) x y
      = (\<Sum>i<m. \<Sum>j<n. p i j * x i * y j - q i j * x i * y j * t)"
    unfolding bil_def by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i<m. \<Sum>j<n. p i j * x i * y j) - (\<Sum>i<m. \<Sum>j<n. q i j * x i * y j) * t"
    by (simp add: sum_subtractf sum_distrib_right)
  finally show ?thesis unfolding bil_def .
qed

lemma bil_div:
  "bil m n (\<lambda>i j. p i j / t) x y = bil m n p x y / t"
  unfolding bil_def by (simp add: sum_divide_distrib)

lemma bil_dot:
  "(\<Sum>k<r. bil m n (\<lambda>i j. c i j k) x y * u k) = bil m n (\<lambda>i j. dot_upto r (c i j) u) x y"
proof -
  have "(\<Sum>k<r. bil m n (\<lambda>i j. c i j k) x y * u k)
      = (\<Sum>k<r. \<Sum>i<m. \<Sum>j<n. c i j k * x i * y j * u k)"
    unfolding bil_def by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<r. \<Sum>j<n. c i j k * x i * y j * u k)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i<m. \<Sum>j<n. \<Sum>k<r. c i j k * x i * y j * u k)"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = bil m n (\<lambda>i j. dot_upto r (c i j) u) x y"
    unfolding bil_def dot_on_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  finally show ?thesis .
qed

lemma bil_swap:
  "bil m n (\<lambda>i j. c i j) x y = bil n m (\<lambda>j i. c i j) y x"
  unfolding bil_def by (subst sum.swap) (simp add: mult_ac)

lemma sos_form_swap:
  "sos_form m n r c x y = sos_form n m r (\<lambda>j i. c i j) y x"
  unfolding sos_form_def by (simp add: bil_swap[of m n])

lemma bsr_le_swap:
  assumes "bsr_le n m N" shows "bsr_le m n N"
  unfolding bsr_le_def
proof (intro allI)
  fix r c
  obtain s c' where s: "s \<le> N" and e: "\<forall>x y. sos_form n m r (\<lambda>j i. c i j) x y = sos_form n m s c' x y"
    using assms unfolding bsr_le_def by blast
  have "\<forall>x y. sos_form m n r c x y = sos_form m n s (\<lambda>i j. c' j i) x y"
    using e by (simp add: sos_form_swap[of m n r c] sos_form_swap[of m n s "\<lambda>i j. c' j i"])
  with s show "\<exists>s\<le>N. \<exists>c'. \<forall>x y. sos_form m n r c x y = sos_form m n s c' x y" by blast
qed

lemma bsr_le_mono:
  assumes "bsr_le m n N" "N \<le> N'" shows "bsr_le m n N'"
  using assms unfolding bsr_le_def by (meson order_trans)

subsection \<open>One projection step\<close>

lemma sum_sq_expand:
  fixes B u :: "nat \<Rightarrow> real"
  shows "(\<Sum>k<r. (B k - u k * t)\<^sup>2)
       = (\<Sum>k<r. (B k)\<^sup>2) - 2 * t * (\<Sum>k<r. B k * u k) + t\<^sup>2 * (\<Sum>k<r. u k * u k)"
proof -
  have e: "\<And>k. (B k - u k * t)\<^sup>2 = (B k)\<^sup>2 - 2 * t * (B k * u k) + t\<^sup>2 * (u k * u k)"
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis unfolding e by (simp add: sum.distrib sum_subtractf sum_distrib_left)
qed

text \<open>Projecting the coefficient vectors away from a nonzero $u\in\mathbb{R}^r$ splits off one square.\<close>
lemma project_step:
  fixes c :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" and u :: "nat \<Rightarrow> real"
  assumes uu: "dot_upto r u u \<noteq> 0"
  shows "sos_form m n r c x y
       = (bil m n (\<lambda>i j. dot_upto r (c i j) u / sqrt (dot_upto r u u)) x y)\<^sup>2
         + sos_form m n r (\<lambda>i j k. c i j k - u k * (dot_upto r (c i j) u / dot_upto r u u)) x y"
proof -
  define B where "B k = bil m n (\<lambda>i j. c i j k) x y" for k
  define \<beta> where "\<beta> = (\<Sum>k<r. B k * u k)"
  define \<gamma> where "\<gamma> = (\<Sum>k<r. u k * u k)"
  have g: "\<gamma> = dot_upto r u u" unfolding \<gamma>_def dot_on_def ..
  have g0: "\<gamma> \<noteq> 0" "0 \<le> \<gamma>" using uu dot_on_self_nonneg[of "{..<r}" u] g by auto
  have b: "\<beta> = bil m n (\<lambda>i j. dot_upto r (c i j) u) x y"
    unfolding \<beta>_def B_def by (rule bil_dot)
  have proj: "bil m n (\<lambda>i j. c i j k - u k * (dot_upto r (c i j) u / dot_upto r u u)) x y
      = B k - u k * (\<beta> / \<gamma>)" for k
  proof -
    have "bil m n (\<lambda>i j. c i j k - u k * (dot_upto r (c i j) u / dot_upto r u u)) x y
        = bil m n (\<lambda>i j. c i j k - (dot_upto r (c i j) u / dot_upto r u u) * u k) x y"
      by (simp add: mult.commute)
    also have "\<dots> = B k - bil m n (\<lambda>i j. dot_upto r (c i j) u / dot_upto r u u) x y * u k"
      unfolding B_def by (rule bil_diff_scale)
    also have "\<dots> = B k - u k * (\<beta> / \<gamma>)"
      by (simp add: bil_div b g)
    finally show ?thesis .
  qed
  have sq: "(bil m n (\<lambda>i j. dot_upto r (c i j) u / sqrt (dot_upto r u u)) x y)\<^sup>2 = \<beta>\<^sup>2 / \<gamma>"
    using g0 by (simp add: bil_div b[symmetric] g[symmetric] power_divide)
  have "sos_form m n r (\<lambda>i j k. c i j k - u k * (dot_upto r (c i j) u / dot_upto r u u)) x y
      = (\<Sum>k<r. (B k - u k * (\<beta> / \<gamma>))\<^sup>2)"
    unfolding sos_form_def by (rule sum.cong[OF refl], simp only: proj)
  also have "\<dots> = (\<Sum>k<r. (B k)\<^sup>2) - 2 * (\<beta> / \<gamma>) * \<beta> + (\<beta> / \<gamma>)\<^sup>2 * \<gamma>"
    unfolding sum_sq_expand \<beta>_def \<gamma>_def ..
  also have "\<dots> = (\<Sum>k<r. (B k)\<^sup>2) - \<beta>\<^sup>2 / \<gamma>"
    using g0 by (simp add: power2_eq_square field_simps)
  also have "\<dots> = sos_form m n r c x y - \<beta>\<^sup>2 / \<gamma>"
    unfolding sos_form_def B_def ..
  finally show ?thesis using sq by simp
qed

subsection \<open>Removing a finite set of coefficient vectors\<close>

text \<open>For any finite set $S$ of index pairs, the form splits as at most $|S|$ squares plus a
  representation, with the same $r$ coordinates, whose vectors $v_{ij}$, $(i,j)\in S$, vanish.\<close>
lemma remove_vectors:
  assumes "finite S"
  shows "\<exists>p a c'. p \<le> card S \<and> (\<forall>(i, j)\<in>S. \<forall>k<r. c' i j k = 0) \<and>
           (\<forall>x y. sos_form m n r c x y = sos_form m n p a x y + sos_form m n r c' x y)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  have "\<forall>x y. sos_form m n r c x y = sos_form m n 0 (\<lambda>i j k. 0) x y + sos_form m n r c x y"
    by (simp add: sos_form_def)
  then show ?case by blast
next
  case (insert ij S)
  obtain i0 j0 where ij: "ij = (i0, j0)" by (cases ij)
  from insert.IH obtain p a c'' where p: "p \<le> card S"
    and z: "\<forall>(i, j)\<in>S. \<forall>k<r. c'' i j k = 0"
    and e: "\<forall>x y. sos_form m n r c x y = sos_form m n p a x y + sos_form m n r c'' x y"
    by blast
  have cardI: "card (insert ij S) = Suc (card S)" using insert.hyps by simp
  define u where "u = c'' i0 j0"
  show ?case
  proof (cases "dot_upto r u u = 0")
    case True
    have "\<forall>(i, j)\<in>insert ij S. \<forall>k<r. c'' i j k = 0"
      using z dot_upto_self_zero[OF True] unfolding ij u_def by auto
    moreover have "p \<le> card (insert ij S)" using p cardI by simp
    ultimately show ?thesis using e by blast
  next
    case False
    define c' where "c' i j k = c'' i j k - u k * (dot_upto r (c'' i j) u / dot_upto r u u)" for i j k
    define a' where "a' i j k = (if k < p then a i j k else dot_upto r (c'' i j) u / sqrt (dot_upto r u u))" for i j k
    have zS0: "c' i j k = 0" if q: "(i, j) \<in> insert ij S" and k: "k < r" for i j k
    proof (cases "(i, j) = ij")
      case True
      then have "i = i0" "j = j0" using ij by auto
      then show ?thesis using False unfolding c'_def u_def by simp
    next
      case F: False
      then have "(i, j) \<in> S" using q by simp
      then have v0: "\<forall>k<r. c'' i j k = 0" using z by auto
      then have "dot_upto r (c'' i j) u = 0" unfolding dot_on_def by simp
      then show ?thesis using v0 k unfolding c'_def by simp
    qed
    have zS: "\<forall>(i, j)\<in>insert ij S. \<forall>k<r. c' i j k = 0"
      using zS0 by blast
    have ea: "sos_form m n (Suc p) a' x y
        = sos_form m n p a x y + (bil m n (\<lambda>i j. dot_upto r (c'' i j) u / sqrt (dot_upto r u u)) x y)\<^sup>2" for x y
    proof -
      have "sos_form m n p a' x y = sos_form m n p a x y"
        unfolding sos_form_def a'_def by (rule sum.cong) auto
      then show ?thesis unfolding sos_form_def by (simp add: a'_def)
    qed
    have "\<forall>x y. sos_form m n r c x y = sos_form m n (Suc p) a' x y + sos_form m n r c' x y"
      using e project_step[OF False, of m n c''] ea unfolding c'_def by simp
    moreover have "Suc p \<le> card (insert ij S)" using p cardI by simp
    ultimately show ?thesis using zS by blast
  qed
qed

subsection \<open>The bound for $m\ge n$\<close>

lemma sum_lessThan_add: "(\<Sum>k<p + s. f k) = (\<Sum>k<p. f k) + (\<Sum>t<s. f (p + t))"
  for f :: "nat \<Rightarrow> real"
  by (induct s) simp_all

lemma bil_width_two:
  assumes n: "2 \<le> n" and z: "\<forall>i<m. \<forall>j. 2 \<le> j \<longrightarrow> j < n \<longrightarrow> a i j = 0"
  shows "bil m n a x y = bil m 2 a x y"
proof -
  have split: "{..<n} = {..<2} \<union> {2..<n}" using n by auto
  have "(\<Sum>j<n. a i j * x i * y j) = (\<Sum>j<2. a i j * x i * y j)" if i: "i < m" for i
  proof -
    have "(\<Sum>j<n. a i j * x i * y j) = (\<Sum>j<2. a i j * x i * y j) + (\<Sum>j\<in>{2..<n}. a i j * x i * y j)"
      unfolding split by (rule sum.union_disjoint) auto
    also have "(\<Sum>j\<in>{2..<n}. a i j * x i * y j) = 0"
      using z i by (intro sum.neutral) auto
    finally show ?thesis by simp
  qed
  then show ?thesis unfolding bil_def by (rule sum.cong[OF refl]) simp
qed

text \<open>The core of the proof: given the width-two bound $\mathrm{BSR}(m,2)\le m+1$, every
  $m\times n$ sum of squares is a sum of at most $m(n-2)+(m+1)$ squares.\<close>
theorem bsr_le_from_width_two:
  assumes H: "bsr_le m 2 (m + 1)" and n: "2 \<le> n"
  shows "bsr_le m n (m * (n - 2) + (m + 1))"
  unfolding bsr_le_def
proof (intro allI)
  fix r c
  define S where "S = {..<m} \<times> {2..<n}"
  have fS: "finite S" and cS: "card S = m * (n - 2)" unfolding S_def by auto
  obtain p a c' where p: "p \<le> m * (n - 2)" and z: "\<forall>(i, j)\<in>S. \<forall>k<r. c' i j k = 0"
    and e: "\<forall>x y. sos_form m n r c x y = sos_form m n p a x y + sos_form m n r c' x y"
    using remove_vectors[OF fS, of r m n c] cS by auto
  have w2: "sos_form m n r c' x y = sos_form m 2 r c' x y" for x y
    unfolding sos_form_def
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<r}"
    then have "\<forall>i<m. \<forall>j. 2 \<le> j \<longrightarrow> j < n \<longrightarrow> c' i j k = 0" using z unfolding S_def by auto
    then show "(bil m n (\<lambda>i j. c' i j k) x y)\<^sup>2 = (bil m 2 (\<lambda>i j. c' i j k) x y)\<^sup>2"
      using bil_width_two[OF n, of m "\<lambda>i j. c' i j k"] by simp
  qed
  obtain s c3 where s: "s \<le> m + 1" and e3: "\<forall>x y. sos_form m 2 r c' x y = sos_form m 2 s c3 x y"
    using H unfolding bsr_le_def by blast
  define d where "d i j k = (if k < p then a i j k else if j < 2 then c3 i j (k - p) else 0)" for i j k
  have ed: "sos_form m n (p + s) d x y = sos_form m n p a x y + sos_form m 2 s c3 x y" for x y
  proof -
    have lo: "(\<Sum>k<p. (bil m n (\<lambda>i j. d i j k) x y)\<^sup>2) = sos_form m n p a x y"
      unfolding sos_form_def d_def by (rule sum.cong) auto
    have hi: "bil m n (\<lambda>i j. d i j (p + t)) x y = bil m 2 (\<lambda>i j. c3 i j t) x y" for t
    proof -
      have "bil m n (\<lambda>i j. d i j (p + t)) x y = bil m 2 (\<lambda>i j. d i j (p + t)) x y"
        by (rule bil_width_two[OF n]) (simp add: d_def)
      also have "\<dots> = bil m 2 (\<lambda>i j. c3 i j t) x y"
        unfolding bil_def d_def by (intro sum.cong) auto
      finally show ?thesis .
    qed
    show ?thesis
      unfolding sos_form_def[of m n "p + s"] sum_lessThan_add lo
      by (simp add: hi sos_form_def)
  qed
  have "\<forall>x y. sos_form m n r c x y = sos_form m n (p + s) d x y"
    using e e3 w2 ed by simp
  moreover have "p + s \<le> m * (n - 2) + (m + 1)" using p s by simp
  ultimately show "\<exists>s'\<le>m * (n - 2) + (m + 1). \<exists>c''. \<forall>x y. sos_form m n r c x y = sos_form m n s' c'' x y"
    by blast
qed

subsection \<open>The upper bound\<close>

text \<open>Hypothesis \<open>BSSV_1_4\<close> (Theorem 1.4 of @{cite BSSV}, used and not proved here): for every
  $p\ge2$, every real sum of squares of bilinear forms of size $p\times 2$ is a sum of at most
  $p+1$ squares.\<close>
theorem bsr_upper:
  assumes BSSV_1_4: "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)"
    and m: "2 \<le> m" and n: "2 \<le> n"
  shows "bsr_le m n (m * n - max m n + 1)"
proof (cases "n \<le> m")
  case True
  have b: "bsr_le m n (m * (n - 2) + (m + 1))"
    by (rule bsr_le_from_width_two[OF BSSV_1_4[OF m] n])
  obtain q where q: "n = q + 2" using n by (metis add.commute le_Suc_ex)
  have "m * (n - 2) + (m + 1) = m * n - max m n + 1"
    using True unfolding q by (simp add: max_def algebra_simps)
  with b show ?thesis by simp
next
  case False
  have b: "bsr_le n m (n * (m - 2) + (n + 1))"
    by (rule bsr_le_from_width_two[OF BSSV_1_4[OF n] m])
  obtain q where q: "m = q + 2" using m by (metis add.commute le_Suc_ex)
  have "n * (m - 2) + (n + 1) = m * n - max m n + 1"
    using False unfolding q by (simp add: max_def algebra_simps)
  with b show ?thesis by (simp add: bsr_le_swap)
qed

corollary bsr_upper_width_three:
  assumes "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)" and "3 \<le> m"
  shows "bsr_le m 3 (2 * m + 1)"
proof -
  have "bsr_le m 3 (m * 3 - max m 3 + 1)" by (rule bsr_upper) (use assms in auto)
  moreover have "m * 3 - max m 3 + 1 = 2 * m + 1" using assms(2) by (simp add: max_def)
  ultimately show ?thesis by simp
qed

corollary bsr_upper_4_3:
  assumes "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)"
  shows "bsr_le 4 3 9"
  using bsr_upper_width_three[OF assms, of 4] by simp

end
