(* encaje: zero filter for BSR: a biquadratic SOS with a real zero (x0,y0), x0,y0 nonzero, is a sum of
   (m-1) + BSR(m,n-1) squares; corollaries m x 3 (2m) and 4 x 3 (8) from BSSV Thm 1.4 *)
theory BSR_Zero
  imports BSR_Upper
begin

text \<open>Zero filter. Let $F=\sum_{k<r} b_k(x,y)^2$ be a sum of squares of bilinear forms of size
  $m\times n$ with $n\ge1$. If $F(x_0,y_0)=0$ for real $x_0\neq0$, $y_0\neq0$, then $F$ is a sum of at
  most $(m-1)+\mathrm{BSR}(m,n-1)$ squares.

  Proof. A linear change of the $y$ variables takes $y_0$ to $e_{n-1}$ (a transposition of two
  coordinates followed by a shear). Then every $b_k$ vanishes at $(x_0,e_{n-1})$, so the vectors
  $v_i=c_{i,n-1}\in\mathbb{R}^r$ satisfy $\sum_i x_{0,i}v_i=0$. With $x_{0,i_0}\neq0$, the $m-1$ vectors
  $v_i$, $i\neq i_0$, are removed by projection (\<open>remove_vectors\<close>), splitting off at most $m-1$
  squares. The remainder still vanishes at $(x_0,e_{n-1})$ (it is bounded by $F$), so its vector
  $v_{i_0}$ is $0$ as well: the remainder does not involve $y_{n-1}$ and is a form of size
  $m\times(n-1)$.\<close>

section \<open>Auxiliary facts\<close>

definition rep_le :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "rep_le m n r c N \<longleftrightarrow> (\<exists>s\<le>N. \<exists>c'. \<forall>x y. sos_form m n r c x y = sos_form m n s c' x y)"

lemma sos_form_nonneg: "0 \<le> sos_form m n r c x y"
  unfolding sos_form_def by (rule sum_nonneg) simp

lemma sos_form_zero_term:
  assumes "sos_form m n r c x y = 0" "k < r"
  shows "bil m n (\<lambda>i j. c i j k) x y = 0"
proof -
  have "\<forall>k\<in>{..<r}. (bil m n (\<lambda>i j. c i j k) x y)\<^sup>2 = 0"
    using assms(1) unfolding sos_form_def by (subst sum_nonneg_eq_0_iff[symmetric]) auto
  with assms(2) show ?thesis by simp
qed

lemma bil_cong_y:
  assumes "\<forall>j<n. y j = y' j" shows "bil m n a x y = bil m n a x y'"
  unfolding bil_def using assms by (intro sum.cong refl) auto

lemma sos_form_cong_y:
  assumes "\<forall>j<n. y j = y' j" shows "sos_form m n r c x y = sos_form m n r c x y'"
  unfolding sos_form_def using bil_cong_y[OF assms] by simp

lemma bil_width_last:
  assumes "\<forall>i<m. a i n = 0" shows "bil m (Suc n) a x y = bil m n a x y"
  unfolding bil_def using assms by (simp add: sum.distrib)

lemma bil_last_unit:
  "bil m (Suc n) a x (\<lambda>j. if j = n then 1 else 0) = (\<Sum>i<m. a i n * x i)"
proof -
  have "(\<Sum>j<Suc n. a i j * x i * (if j = n then 1 else 0)) = a i n * x i" for i
  proof -
    have "(\<Sum>j<Suc n. a i j * x i * (if j = n then 1 else 0)) = (\<Sum>j<Suc n. if j = n then a i n * x i else 0)"
      by (rule sum.cong) auto
    then show ?thesis by simp
  qed
  then show ?thesis unfolding bil_def by simp
qed

section \<open>Linear change of the $y$ variables\<close>

definition ymul :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "ymul n A y = (\<lambda>j. \<Sum>l<n. A j l * y l)"

definition csub :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "csub n c A = (\<lambda>i l k. \<Sum>j<n. c i j k * A j l)"

lemma bil_subst:
  "bil m n a x (ymul n A y) = bil m n (\<lambda>i l. \<Sum>j<n. a i j * A j l) x y"
proof -
  have "bil m n a x (ymul n A y) = (\<Sum>i<m. \<Sum>j<n. \<Sum>l<n. a i j * x i * (A j l * y l))"
    unfolding bil_def ymul_def by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<m. \<Sum>l<n. \<Sum>j<n. a i j * x i * (A j l * y l))"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = bil m n (\<lambda>i l. \<Sum>j<n. a i j * A j l) x y"
    unfolding bil_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  finally show ?thesis .
qed

lemma sos_form_subst:
  "sos_form m n r c x (ymul n A y) = sos_form m n r (csub n c A) x y"
  unfolding sos_form_def csub_def by (simp add: bil_subst)

text \<open>If $A B = I$, a representation of the substituted form gives one of the original form.\<close>
lemma rep_le_transfer:
  assumes inv: "\<And>y j. j < n \<Longrightarrow> ymul n A (ymul n B y) j = y j"
    and R: "rep_le m n r (csub n c A) N"
  shows "rep_le m n r c N"
proof -
  obtain s d where s: "s \<le> N" and e: "\<forall>x y. sos_form m n r (csub n c A) x y = sos_form m n s d x y"
    using R unfolding rep_le_def by blast
  have "sos_form m n r c x y = sos_form m n s (csub n d B) x y" for x y
  proof -
    have "sos_form m n r c x y = sos_form m n r c x (ymul n A (ymul n B y))"
      by (rule sos_form_cong_y) (simp add: inv)
    also have "\<dots> = sos_form m n r (csub n c A) x (ymul n B y)" by (rule sos_form_subst)
    also have "\<dots> = sos_form m n s d x (ymul n B y)" using e by simp
    also have "\<dots> = sos_form m n s (csub n d B) x y" by (rule sos_form_subst)
    finally show ?thesis .
  qed
  with s show ?thesis unfolding rep_le_def by blast
qed

lemma sum_unit_col:
  fixes n :: nat
  assumes "a < n" shows "(\<Sum>l<n. (if l = a then 1 else 0) * z l) = (z a :: real)"
proof -
  have "(\<Sum>l<n. (if l = a then 1 else 0) * z l) = (\<Sum>l<n. if l = a then z a else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = z a" using assms by (subst sum.delta) auto
  finally show ?thesis .
qed

lemma sum_shear_row:
  fixes n :: nat
  assumes j: "j < n" and q: "q < n"
  shows "(\<Sum>l<n. (if l = q then a else if l = j then 1 else 0) * z l)
       = (if j = q then a * z q else z j + a * (z q :: real))"
proof (cases "j = q")
  case True
  have "(\<Sum>l<n. (if l = q then a else if l = j then 1 else 0) * z l) = (\<Sum>l<n. if l = q then a * z q else 0)"
    using True by (intro sum.cong) auto
  also have "\<dots> = a * z q" using q by (subst sum.delta) auto
  finally show ?thesis using True by simp
next
  case False
  have "(\<Sum>l<n. (if l = q then a else if l = j then 1 else 0) * z l)
      = (\<Sum>l<n. (if l = q then a * z q else 0) + (if l = j then z j else 0))"
    using False by (intro sum.cong) auto
  then show ?thesis using False j q by (simp add: sum.distrib sum.delta)
qed

section \<open>The case $y_0=e_{n-1}$\<close>

lemma zero_filter_unit:
  assumes H: "bsr_le m n N" and i0: "i0 < m" "x0 i0 \<noteq> 0"
    and Z: "sos_form m (Suc n) r c x0 (\<lambda>j. if j = n then 1 else 0) = 0"
  shows "rep_le m (Suc n) r c ((m - 1) + N)"
proof -
  define e :: "nat \<Rightarrow> real" where "e = (\<lambda>j. if j = n then 1 else 0)"
  define S where "S = (\<lambda>i. (i, n)) ` ({..<m} - {i0})"
  have fS: "finite S" unfolding S_def by simp
  have cS: "card S \<le> m - 1"
  proof -
    have "card S \<le> card ({..<m} - {i0})" unfolding S_def by (rule card_image_le) simp
    also have "\<dots> = m - 1" using i0 by simp
    finally show ?thesis .
  qed
  obtain p a c' where p: "p \<le> card S" and z: "\<forall>(i, j)\<in>S. \<forall>k<r. c' i j k = 0"
    and eq: "\<forall>x y. sos_form m (Suc n) r c x y = sos_form m (Suc n) p a x y + sos_form m (Suc n) r c' x y"
    using remove_vectors[OF fS, of r m "Suc n" c] by blast
  have Z': "sos_form m (Suc n) r c' x0 e = 0"
  proof -
    have "sos_form m (Suc n) p a x0 e + sos_form m (Suc n) r c' x0 e = 0"
      using eq Z unfolding e_def by simp
    then show ?thesis using sos_form_nonneg[of m "Suc n" p a x0 e] sos_form_nonneg[of m "Suc n" r c' x0 e]
      by linarith
  qed
  have zi: "c' i n k = 0" if "i < m" "i \<noteq> i0" "k < r" for i k
    using z that unfolding S_def by auto
  have zall: "\<forall>i<m. c' i n k = 0" if k: "k < r" for k
  proof -
    have "0 = (\<Sum>i<m. c' i n k * x0 i)"
      using sos_form_zero_term[OF Z' k] unfolding e_def bil_last_unit by simp
    also have "\<dots> = (\<Sum>i<m. if i = i0 then c' i0 n k * x0 i0 else 0)"
      using zi k by (intro sum.cong) auto
    also have "\<dots> = c' i0 n k * x0 i0" using i0 by (simp add: sum.delta)
    finally have "c' i0 n k = 0" using i0 by simp
    then show ?thesis using zi k by (metis)
  qed
  have w: "sos_form m (Suc n) r c' x y = sos_form m n r c' x y" for x y
    unfolding sos_form_def using zall bil_width_last by (intro sum.cong refl) simp
  obtain s c3 where s: "s \<le> N" and e3: "\<forall>x y. sos_form m n r c' x y = sos_form m n s c3 x y"
    using H unfolding bsr_le_def by blast
  define d where "d i j k = (if k < p then a i j k else if j < n then c3 i j (k - p) else 0)" for i j k
  have ed: "sos_form m (Suc n) (p + s) d x y = sos_form m (Suc n) p a x y + sos_form m n s c3 x y" for x y
  proof -
    have lo: "(\<Sum>k<p. (bil m (Suc n) (\<lambda>i j. d i j k) x y)\<^sup>2) = sos_form m (Suc n) p a x y"
      unfolding sos_form_def d_def by (rule sum.cong) auto
    have hi: "bil m (Suc n) (\<lambda>i j. d i j (p + t)) x y = bil m n (\<lambda>i j. c3 i j t) x y" for t
    proof -
      have "bil m (Suc n) (\<lambda>i j. d i j (p + t)) x y = bil m n (\<lambda>i j. d i j (p + t)) x y"
        by (rule bil_width_last) (simp add: d_def)
      also have "\<dots> = bil m n (\<lambda>i j. c3 i j t) x y"
        unfolding bil_def d_def by (intro sum.cong) auto
      finally show ?thesis .
    qed
    show ?thesis
      unfolding sos_form_def[of m "Suc n" "p + s"] sum_lessThan_add lo
      by (simp add: hi sos_form_def)
  qed
  have "\<forall>x y. sos_form m (Suc n) r c x y = sos_form m (Suc n) (p + s) d x y"
    using eq e3 w ed by simp
  moreover have "p + s \<le> (m - 1) + N" using p cS s by simp
  ultimately show ?thesis unfolding rep_le_def by blast
qed

section \<open>The case $y_{0,n-1}\neq0$: a shear\<close>

lemma zero_filter_shear:
  assumes H: "bsr_le m n N" and i0: "i0 < m" "x0 i0 \<noteq> 0" and yq: "y0 n \<noteq> 0"
    and Z: "sos_form m (Suc n) r c x0 y0 = 0"
  shows "rep_le m (Suc n) r c ((m - 1) + N)"
proof -
  define A where "A j l = (if l = n then y0 j else if l = j then 1 else 0)" for j l
  define B where "B j l = (if l = n then (if j = n then 1 / y0 n else - (y0 j / y0 n))
                           else if l = j then 1 else 0)" for j l
  have Bz: "ymul (Suc n) B z j = (if j = n then z n / y0 n else z j - y0 j / y0 n * z n)"
    if "j < Suc n" for z j
    unfolding ymul_def B_def using sum_shear_row[OF that, of n "if j = n then 1 / y0 n else - (y0 j / y0 n)" z]
    by auto
  have Az: "ymul (Suc n) A z j = (if j = n then y0 n * z n else z j + y0 j * z n)"
    if "j < Suc n" for z j
    unfolding ymul_def A_def using sum_shear_row[OF that, of n "y0 j" z] by auto
  have inv: "ymul (Suc n) A (ymul (Suc n) B z) j = z j" if "j < Suc n" for z j
    using that yq by (simp add: Az Bz field_simps)
  have Ae: "ymul (Suc n) A (\<lambda>j. if j = n then 1 else 0) j = y0 j" if "j < Suc n" for j
    using that by (simp add: Az)
  have Z1: "sos_form m (Suc n) r (csub (Suc n) c A) x0 (\<lambda>j. if j = n then 1 else 0) = 0"
  proof -
    have "sos_form m (Suc n) r (csub (Suc n) c A) x0 (\<lambda>j. if j = n then 1 else 0)
        = sos_form m (Suc n) r c x0 (ymul (Suc n) A (\<lambda>j. if j = n then 1 else 0))"
      by (rule sos_form_subst[symmetric])
    also have "\<dots> = sos_form m (Suc n) r c x0 y0"
      by (rule sos_form_cong_y) (simp add: Ae)
    finally show ?thesis using Z by simp
  qed
  show ?thesis
    by (rule rep_le_transfer[OF inv zero_filter_unit[OF H i0 Z1]])
qed

section \<open>The general case\<close>

theorem bsr_zero_filter:
  assumes n: "1 \<le> n" and H: "bsr_le m (n - 1) N"
    and x0: "\<exists>i<m. x0 i \<noteq> 0" and y0: "\<exists>j<n. y0 j \<noteq> 0"
    and Z: "sos_form m n r c x0 y0 = 0"
  shows "\<exists>s\<le>(m - 1) + N. \<exists>c'. \<forall>x y. sos_form m n r c x y = sos_form m n s c' x y"
proof -
  obtain q where q: "n = Suc q" using n by (cases n) auto
  obtain i0 where i0: "i0 < m" "x0 i0 \<noteq> 0" using x0 by blast
  obtain j0 where j0: "j0 < Suc q" "y0 j0 \<noteq> 0" using y0 q by blast
  have H': "bsr_le m q N" using H q by simp
  have Z': "sos_form m (Suc q) r c x0 y0 = 0" using Z q by simp
  have "rep_le m (Suc q) r c ((m - 1) + N)"
  proof (cases "y0 q = 0")
    case False
    then show ?thesis by (rule zero_filter_shear[OF H' i0 _ Z'])
  next
    case True
    define sw where "sw j = (if j = j0 then q else if j = q then j0 else j)" for j
    define P :: "nat \<Rightarrow> nat \<Rightarrow> real" where "P j l = (if l = sw j then 1 else 0)" for j l
    have swn: "sw j < Suc q" if "j < Suc q" for j using that j0 unfolding sw_def by auto
    have sws: "sw (sw j) = j" for j unfolding sw_def by auto
    have Pz: "ymul (Suc q) P z j = z (sw j)" if "j < Suc q" for z j
      unfolding ymul_def P_def by (rule sum_unit_col[OF swn[OF that]])
    have inv: "ymul (Suc q) P (ymul (Suc q) P z) j = z j" if "j < Suc q" for z j
      using that by (simp add: Pz swn sws)
    define y1 where "y1 = ymul (Suc q) P y0"
    have y1q: "y1 q \<noteq> 0" unfolding y1_def using j0 by (simp add: Pz sw_def)
    have Z1: "sos_form m (Suc q) r (csub (Suc q) c P) x0 y1 = 0"
    proof -
      have "sos_form m (Suc q) r (csub (Suc q) c P) x0 y1 = sos_form m (Suc q) r c x0 (ymul (Suc q) P y1)"
        by (rule sos_form_subst[symmetric])
      also have "\<dots> = sos_form m (Suc q) r c x0 y0"
        by (rule sos_form_cong_y) (simp add: y1_def inv)
      finally show ?thesis using Z' by simp
    qed
    show ?thesis
      by (rule rep_le_transfer[OF inv zero_filter_shear[OF H' i0 y1q Z1]])
  qed
  then show ?thesis using q unfolding rep_le_def by simp
qed

section \<open>Width three\<close>

text \<open>With BSSV Theorem 1.4 (hypothesis, as in \<open>BSR_Upper\<close>): an $m\times 3$ sum of squares of
  bilinear forms with a real zero $(x_0,y_0)$, $x_0\neq0\neq y_0$, is a sum of at most $2m$ squares.\<close>
corollary bsr_zero_width_three:
  assumes BSSV_1_4: "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)" and m: "2 \<le> m"
    and x0: "\<exists>i<m. x0 i \<noteq> 0" and y0: "\<exists>j<3. y0 j \<noteq> 0"
    and Z: "sos_form m 3 r c x0 y0 = 0"
  shows "\<exists>s\<le>2 * m. \<exists>c'. \<forall>x y. sos_form m 3 r c x y = sos_form m 3 s c' x y"
proof -
  have "\<exists>s\<le>(m - 1) + (m + 1). \<exists>c'. \<forall>x y. sos_form m 3 r c x y = sos_form m 3 s c' x y"
    by (rule bsr_zero_filter[OF _ _ x0 y0 Z]) (use BSSV_1_4[OF m] in simp_all)
  moreover have "(m - 1) + (m + 1) = 2 * m" using m by simp
  ultimately show ?thesis by (simp add: mult_2)
qed

corollary bsr_zero_4_3:
  assumes BSSV_1_4: "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)"
    and x0: "\<exists>i<4. x0 i \<noteq> 0" and y0: "\<exists>j<3. y0 j \<noteq> 0"
    and Z: "sos_form 4 3 r c x0 y0 = 0"
  shows "\<exists>s\<le>8. \<exists>c'. \<forall>x y. sos_form 4 3 r c x y = sos_form 4 3 s c' x y"
  using bsr_zero_width_three[OF BSSV_1_4 _ x0 y0 Z] by simp

end
