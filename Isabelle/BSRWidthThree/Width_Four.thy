(* encaje: BSR(m,3) = 2m, section 7 (Corollary 7): from width three to width four by the projection argument of
   BSR_Upper (thm:up of the earlier note), and the identity comparing mn - max(m,n) with BSSV Theorem 2.1 *)
theory Width_Four
  imports Segre_Width3.BSR_Upper
begin

text \<open>Section 7 of the note ``For $m\ge2$, every $m\times3$ biquadratic sum of squares is a sum of $2m$
  squares''. Theorem 1 of the note ($\mathrm{BSR}(m,3)\le 2m$) enters as an explicit hypothesis: its proof is
  only partly formalized (see \<open>BSR_Width3_Lower\<close>, \<open>Regular_Point\<close>, \<open>Width3_Final\<close>). Everything else is
  proved here: the projection of \<open>remove_vectors\<close> removes the $m(n-3)$ coefficient vectors of
  $y_3,\dots,y_{n-1}$, and the remainder is an $m\times3$ form.

  The second part is the arithmetic behind the paragraph after Corollary 7: with $s=\min(m,n)$,
  $M=\max(m,n)$, $C=M(s-1)$, the bound $\binom{p+1}2<\binom{M+1}2\binom{s+1}2$ of BSSV Theorem 2.1 allows
  $p=C+1$ exactly when $s=4$ (among $s\ge4$).\<close>

section \<open>From width three\<close>

lemma bil_width_three:
  assumes n: "3 \<le> n" and z: "\<forall>i<m. \<forall>j. 3 \<le> j \<longrightarrow> j < n \<longrightarrow> a i j = 0"
  shows "bil m n a x y = bil m 3 a x y"
proof -
  have split: "{..<n} = {..<3} \<union> {3..<n}" using n by auto
  have "(\<Sum>j<n. a i j * x i * y j) = (\<Sum>j<3. a i j * x i * y j)" if i: "i < m" for i
  proof -
    have "(\<Sum>j<n. a i j * x i * y j) = (\<Sum>j<3. a i j * x i * y j) + (\<Sum>j\<in>{3..<n}. a i j * x i * y j)"
      unfolding split by (rule sum.union_disjoint) auto
    also have "(\<Sum>j\<in>{3..<n}. a i j * x i * y j) = 0"
      using z i by (intro sum.neutral) auto
    finally show ?thesis by simp
  qed
  then show ?thesis unfolding bil_def by (rule sum.cong[OF refl]) simp
qed

text \<open>Given $\mathrm{BSR}(m,3)\le 2m$, every $m\times n$ sum of squares is a sum of at most $m(n-3)+2m$
  squares (the proof of Corollary 7).\<close>
theorem bsr_le_from_width_three:
  assumes H: "bsr_le m 3 (2 * m)" and n: "3 \<le> n"
  shows "bsr_le m n (m * (n - 3) + 2 * m)"
  unfolding bsr_le_def
proof (intro allI)
  fix r c
  define S where "S = {..<m} \<times> {3..<n}"
  have fS: "finite S" and cS: "card S = m * (n - 3)" unfolding S_def by auto
  obtain p a c' where p: "p \<le> m * (n - 3)" and z: "\<forall>(i, j)\<in>S. \<forall>k<r. c' i j k = 0"
    and e: "\<forall>x y. sos_form m n r c x y = sos_form m n p a x y + sos_form m n r c' x y"
    using remove_vectors[OF fS, of r m n c] cS by auto
  have w3: "sos_form m n r c' x y = sos_form m 3 r c' x y" for x y
    unfolding sos_form_def
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<r}"
    then have "\<forall>i<m. \<forall>j. 3 \<le> j \<longrightarrow> j < n \<longrightarrow> c' i j k = 0" using z unfolding S_def by auto
    then show "(bil m n (\<lambda>i j. c' i j k) x y)\<^sup>2 = (bil m 3 (\<lambda>i j. c' i j k) x y)\<^sup>2"
      using bil_width_three[OF n, of m "\<lambda>i j. c' i j k"] by simp
  qed
  obtain s c3 where s: "s \<le> 2 * m" and e3: "\<forall>x y. sos_form m 3 r c' x y = sos_form m 3 s c3 x y"
    using H unfolding bsr_le_def by blast
  define d where "d i j k = (if k < p then a i j k else if j < 3 then c3 i j (k - p) else 0)" for i j k
  have ed: "sos_form m n (p + s) d x y = sos_form m n p a x y + sos_form m 3 s c3 x y" for x y
  proof -
    have lo: "(\<Sum>k<p. (bil m n (\<lambda>i j. d i j k) x y)\<^sup>2) = sos_form m n p a x y"
      unfolding sos_form_def d_def by (rule sum.cong) auto
    have hi: "bil m n (\<lambda>i j. d i j (p + t)) x y = bil m 3 (\<lambda>i j. c3 i j t) x y" for t
    proof -
      have "bil m n (\<lambda>i j. d i j (p + t)) x y = bil m 3 (\<lambda>i j. d i j (p + t)) x y"
        by (rule bil_width_three[OF n]) (simp add: d_def)
      also have "\<dots> = bil m 3 (\<lambda>i j. c3 i j t) x y"
        unfolding bil_def d_def by (intro sum.cong) auto
      finally show ?thesis .
    qed
    show ?thesis
      unfolding sos_form_def[of m n "p + s"] sum_lessThan_add lo
      by (simp add: hi sos_form_def)
  qed
  have "\<forall>x y. sos_form m n r c x y = sos_form m n (p + s) d x y"
    using e e3 w3 ed by simp
  moreover have "p + s \<le> m * (n - 3) + 2 * m" using p s by simp
  ultimately show "\<exists>s'\<le>m * (n - 3) + 2 * m. \<exists>c''. \<forall>x y. sos_form m n r c x y = sos_form m n s' c'' x y"
    by blast
qed

text \<open>Corollary 7: with Theorem 1 for $m$ rows, $\mathrm{BSR}(m,4)\le 3m$.\<close>
corollary bsr_width_four:
  assumes Theorem_1: "bsr_le m 3 (2 * m)"
  shows "bsr_le m 4 (3 * m)"
  using bsr_le_from_width_three[OF Theorem_1, of 4] by simp

text \<open>The general bound of the proof: with Theorem 1 for every number of rows $p\ge3$,
  $\mathrm{BSR}(m,n)\le mn-\max(m,n)$ for $m,n\ge3$.\<close>
theorem bsr_upper_three:
  assumes Theorem_1: "\<And>p. 3 \<le> p \<Longrightarrow> bsr_le p 3 (2 * p)"
    and m: "3 \<le> m" and n: "3 \<le> n"
  shows "bsr_le m n (m * n - max m n)"
proof (cases "n \<le> m")
  case True
  have b: "bsr_le m n (m * (n - 3) + 2 * m)"
    by (rule bsr_le_from_width_three[OF Theorem_1[OF m] n])
  obtain q where q: "n = q + 3" using n by (metis add.commute le_Suc_ex)
  have "m * (n - 3) + 2 * m = m * n - max m n"
    using True unfolding q by (simp add: max_def algebra_simps)
  with b show ?thesis by simp
next
  case False
  have b: "bsr_le n m (n * (m - 3) + 2 * n)"
    by (rule bsr_le_from_width_three[OF Theorem_1[OF n] m])
  obtain q where q: "m = q + 3" using m by (metis add.commute le_Suc_ex)
  have "n * (m - 3) + 2 * n = m * n - max m n"
    using False unfolding q by (simp add: max_def algebra_simps)
  with b show ?thesis by (simp add: bsr_le_swap)
qed

section \<open>Comparison with BSSV Theorem 2.1\<close>

text \<open>With $T_j=j(j+1)/2$, $D=T_MT_s$ and $C=M(s-1)$:
  $4(T_{C+1}-D)=2(C+1)(C+2)-M(M+1)s(s+1)=(M-1)\bigl(M(s^2-5s+2)-4\bigr)$.\<close>
lemma bssv_identity:
  fixes M s :: int
  defines "C \<equiv> M * (s - 1)"
  shows "2 * (C + 1) * (C + 2) - M * (M + 1) * s * (s + 1) = (M - 1) * (M * (s\<^sup>2 - 5 * s + 2) - 4)"
  unfolding C_def by (simp add: power2_eq_square algebra_simps)

text \<open>For $s\ge5$ (and $M\ge3$): $T_{C+1}>D$, so BSSV Theorem 2.1 already gives a bound at most $C$.\<close>
lemma bssv_wins_from_five:
  fixes M s :: int
  assumes s: "5 \<le> s" and M: "3 \<le> M"
  shows "M * (M + 1) * s * (s + 1) < 2 * (M * (s - 1) + 1) * (M * (s - 1) + 2)"
proof -
  have q: "2 \<le> s\<^sup>2 - 5 * s + 2"
  proof -
    have "s\<^sup>2 - 5 * s = s * (s - 5)" by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> \<ge> 0" using s by simp
    finally show ?thesis by simp
  qed
  have "M * (s\<^sup>2 - 5 * s + 2) \<ge> M * 2" using q M by (intro mult_left_mono) auto
  then have pos: "0 < M * (s\<^sup>2 - 5 * s + 2) - 4" using M by linarith
  have "0 < (M - 1) * (M * (s\<^sup>2 - 5 * s + 2) - 4)" using pos M by simp
  then show ?thesis using bssv_identity[of M s] by linarith
qed

text \<open>For $s=4$ (and $M\ge2$): $T_{C+1}<D$, so BSSV Theorem 2.1 allows $C+1=3M+1$ and Corollary 7 is better.\<close>
lemma width_four_wins:
  fixes M :: int
  assumes M: "2 \<le> M"
  shows "2 * (3 * M + 1) * (3 * M + 2) < M * (M + 1) * 4 * 5"
proof -
  have "2 * (M * (4 - 1) + 1) * (M * (4 - 1) + 2) - M * (M + 1) * 4 * (4 + 1) = (M - 1) * (- 2 * M - 4)"
    using bssv_identity[of M 4] by (simp add: power2_eq_square)
  moreover have "(M - 1) * (- 2 * M - 4) < 0" using M by (simp add: mult_pos_neg)
  ultimately show ?thesis by (simp add: algebra_simps)
qed

end
