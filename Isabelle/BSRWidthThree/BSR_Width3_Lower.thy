(* encaje: lower bound BSR(m,3) >= 2m (V236, section 5): the witness
   F_m = sum_i x_i^2 ((y_1 - i y_0)^2 + y_2^2) is a sum of 2m squares and of no fewer;
   reuses bil, sos_form, bsr_le, dot, dot_self_zero (BSR_Upper) and antisym3_two_kernel_zero (Segre_Width3) *)
theory BSR_Width3_Lower
  imports Segre_Width3.BSR_Upper Segre_Width3.Segre_Width3
begin

text \<open>Section 5 of the note on the SOS length of biquadratic forms of width three. Rows are indexed
  by $i<m$ and the vectors are $b_i=(1,i,0)$ (the note uses $i=1,\dots,m$; only distinctness matters).
  The witness is
  \[ F_m(x,y)=\sum_{i<m} x_i^2\bigl((y_1-i\,y_0)^2+y_2^2\bigr), \]
  a sum of $2m$ squares (\<open>wit3_sos\<close>). In a representation $F_m=\sum_{k<s}b_k^2$ write
  $M_i$ for the $s\times3$ matrix with columns $w_{ij}=(c_{ijk})_{k<s}$. Evaluating at
  $x=e_i$ and $x=e_i+e_{i'}$ gives $|M_iy|^2=q_i(y)$ and $\langle M_iy,M_{i'}y\rangle=0$
  (no coefficient extraction is needed). Then $M_ib_i=0$, the columns $w_{i1},w_{i2}$ are orthonormal,
  and for $i\neq i'$ the matrix $K=M_i^{\mathsf T}M_{i'}$ is antisymmetric and kills $b_i$ and $b_{i'}$,
  hence is zero by \<open>antisym3_two_kernel_zero\<close>. The $2m$ vectors $w_{i1},w_{i2}$ are orthonormal in
  $\mathbb{R}^s$, so $s\ge 2m$ (Bessel's inequality, \<open>orthonormal_le\<close>).\<close>

section \<open>Small facts\<close>

lemma sum3: "(\<Sum>j<(3::nat). f j) = f 0 + f 1 + (f 2 :: 'a::comm_monoid_add)"
  by (simp add: lessThan3 add.assoc)

lemma even_ne_odd [simp]: "2 * a \<noteq> Suc (2 * b)" "Suc (2 * b) \<noteq> 2 * a"
  by presburger+

lemma sum_double: "(\<Sum>k<2 * m. f k) = (\<Sum>i<m. f (2 * i) + f (Suc (2 * i)))"
  for f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  by (induct m) (simp_all add: add.assoc)

lemma dot_add_left: "dot r (\<lambda>k. u k + v k) w = dot r u w + dot r v w"
  unfolding dot_def by (simp add: distrib_right sum.distrib)

lemma dot_add_right: "dot r w (\<lambda>k. u k + v k) = dot r w u + dot r w v"
  unfolding dot_def by (simp add: distrib_left sum.distrib)

lemma dot_scale_left: "dot r (\<lambda>k. u k * a) w = dot r u w * a"
  unfolding dot_def by (simp add: sum_distrib_right sum_distrib_left mult_ac)

lemma dot_scale_right: "dot r w (\<lambda>k. u k * a) = dot r w u * a"
  unfolding dot_def by (simp add: sum_distrib_right sum_distrib_left mult_ac)

lemma dot_zero_left: "dot r (\<lambda>k. 0) w = 0" and dot_zero_right: "dot r w (\<lambda>k. 0) = 0"
  unfolding dot_def by simp_all

lemma dot_comm: "dot r u w = dot r w u"
  unfolding dot_def by (simp add: mult.commute)

lemma dot_cong_zero_right:
  assumes "\<forall>k<r. v k = 0" shows "dot r w v = 0"
  unfolding dot_def using assms by simp

lemma dot_cong_zero_left:
  assumes "\<forall>k<r. v k = 0" shows "dot r v w = 0"
  unfolding dot_def using assms by simp

section \<open>The witness\<close>

definition wit3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "wit3 i j k = (if k = 2 * i then (if j = 0 then - of_nat i else if j = 1 then 1 else 0)
                 else if k = Suc (2 * i) then (if j = 2 then 1 else 0) else 0)"

definition qform :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "qform i y = (y 1 - of_nat i * y 0)\<^sup>2 + (y 2)\<^sup>2"

definition F_wit :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "F_wit m x y = (\<Sum>i<m. (x i)\<^sup>2 * qform i y)"

lemma bil_wit_even:
  assumes "i0 < m" shows "bil m 3 (\<lambda>i j. wit3 i j (2 * i0)) x y = x i0 * (y 1 - of_nat i0 * y 0)"
proof -
  have "(\<Sum>j<3. wit3 i j (2 * i0) * x i * y j) = (if i = i0 then x i0 * (y 1 - of_nat i0 * y 0) else 0)" for i
    by (cases "i = i0") (simp_all add: sum3 wit3_def algebra_simps)
  then show ?thesis unfolding bil_def using assms by simp
qed

lemma bil_wit_odd:
  assumes "i0 < m" shows "bil m 3 (\<lambda>i j. wit3 i j (Suc (2 * i0))) x y = x i0 * y 2"
proof -
  have "(\<Sum>j<3. wit3 i j (Suc (2 * i0)) * x i * y j) = (if i = i0 then x i0 * y 2 else 0)" for i
    by (cases "i = i0") (simp_all add: sum3 wit3_def)
  then show ?thesis unfolding bil_def using assms by simp
qed

text \<open>$F_m$ is a sum of $2m$ squares of bilinear forms: $x_i(y_1-iy_0)$ and $x_iy_2$.\<close>
theorem wit3_sos: "sos_form m 3 (2 * m) wit3 x y = F_wit m x y"
proof -
  have "sos_form m 3 (2 * m) wit3 x y
      = (\<Sum>i<m. (x i * (y 1 - of_nat i * y 0))\<^sup>2 + (x i * y 2)\<^sup>2)"
    unfolding sos_form_def sum_double by (rule sum.cong) (simp_all add: bil_wit_even bil_wit_odd)
  also have "\<dots> = F_wit m x y"
    unfolding F_wit_def qform_def by (rule sum.cong) (simp_all add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

section \<open>Evaluations of a representation\<close>

definition colv :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "colv c i y k = (\<Sum>j<3. c i j k * y j)"

definition ue :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "ue i = (\<lambda>l. if l = i then 1 else 0)"

lemma bil_ue:
  assumes "i0 < m" shows "bil m 3 (\<lambda>i j. c i j k) (ue i0) y = colv c i0 y k"
proof -
  have "(\<Sum>j<3. c i j k * ue i0 i * y j) = (if i = i0 then colv c i0 y k else 0)" for i
    by (cases "i = i0") (simp_all add: ue_def colv_def)
  then show ?thesis unfolding bil_def using assms by simp
qed

lemma bil_add_x: "bil m n a (\<lambda>l. x l + x' l) y = bil m n a x y + bil m n a x' y"
  unfolding bil_def by (simp add: distrib_left distrib_right sum.distrib)

lemma sos_form_ue:
  assumes "i < m" shows "sos_form m 3 s c (ue i) y = dot s (colv c i y) (colv c i y)"
  unfolding sos_form_def dot_def using bil_ue[OF assms] by (simp add: power2_eq_square)

lemma sos_form_ue2:
  assumes "i < m" "i' < m"
  shows "sos_form m 3 s c (\<lambda>l. ue i l + ue i' l) y
       = dot s (\<lambda>k. colv c i y k + colv c i' y k) (\<lambda>k. colv c i y k + colv c i' y k)"
  unfolding sos_form_def dot_def bil_add_x using bil_ue[OF assms(1)] bil_ue[OF assms(2)]
  by (simp add: power2_eq_square)

lemma F_wit_ue:
  assumes "i < m" shows "F_wit m (ue i) y = qform i y"
proof -
  have "(\<Sum>l<m. (ue i l)\<^sup>2 * qform l y) = (\<Sum>l<m. if l = i then qform i y else 0)"
    by (rule sum.cong) (simp_all add: ue_def)
  then show ?thesis unfolding F_wit_def using assms by simp
qed

lemma F_wit_ue2:
  assumes "i < m" "i' < m" "i \<noteq> i'"
  shows "F_wit m (\<lambda>l. ue i l + ue i' l) y = qform i y + qform i' y"
proof -
  have "(\<Sum>l<m. (ue i l + ue i' l)\<^sup>2 * qform l y)
      = (\<Sum>l<m. (if l = i then qform i y else 0) + (if l = i' then qform i' y else 0))"
    by (rule sum.cong) (use assms(3) in \<open>auto simp: ue_def\<close>)
  then show ?thesis unfolding F_wit_def using assms by (simp add: sum.distrib)
qed

text \<open>The column $w_{ij}=(c_{ijk})_{k}$ of $M_i$.\<close>
definition col :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "col c i j = (\<lambda>k. c i j k)"

lemma colv_expand: "colv c i y = (\<lambda>k. col c i 0 k * y 0 + col c i 1 k * y 1 + col c i 2 k * y 2)"
  unfolding colv_def col_def by (simp add: sum3)

section \<open>Orthonormal families\<close>

lemma sum_delta_less:
  fixes g :: real and N :: nat
  assumes "a < N" shows "(\<Sum>b<N. if b = a then g else 0) = g"
proof -
  have "(\<Sum>b<N. if b = a then g else 0) = (if a \<in> {..<N} then g else 0)"
    by (rule sum.delta[OF finite_lessThan])
  then show ?thesis using assms by simp
qed

text \<open>Bessel's inequality for the unit vector $e_k$: $\sum_{a<N}u_{a,k}^2\le1$.\<close>
lemma bessel_unit:
  fixes N :: nat
  assumes on: "\<forall>a<N. \<forall>b<N. dot s (u a) (u b) = (if a = b then 1 else 0)" and k: "k < s"
  shows "(\<Sum>a<N. (u a k)\<^sup>2) \<le> 1"
proof -
  define e :: "nat \<Rightarrow> real" where "e = (\<lambda>l. if l = k then 1 else 0)"
  define p where "p = (\<lambda>l. \<Sum>a<N. u a k * u a l)"
  define t where "t = (\<Sum>a<N. (u a k)\<^sup>2)"
  have ee: "dot s e e = 1" unfolding dot_def e_def using k by (simp add: if_distrib cong: if_cong)
  have ep: "dot s e p = t"
  proof -
    have "dot s e p = (\<Sum>l<s. if l = k then p k else 0)"
      unfolding dot_def e_def by (rule sum.cong) auto
    also have "\<dots> = p k" using k by simp
    finally show ?thesis unfolding p_def t_def by (simp add: power2_eq_square)
  qed
  have pp: "dot s p p = t"
  proof -
    have "dot s p p = (\<Sum>l<s. \<Sum>a<N. \<Sum>b<N. u a k * u b k * (u a l * u b l))"
      unfolding dot_def p_def by (simp add: sum_product mult_ac)
    also have "\<dots> = (\<Sum>a<N. \<Sum>l<s. \<Sum>b<N. u a k * u b k * (u a l * u b l))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. \<Sum>l<s. u a k * u b k * (u a l * u b l))"
      by (rule sum.cong[OF refl], rule sum.swap)
    also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. u a k * u b k * dot s (u a) (u b))"
      unfolding dot_def by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. if b = a then u a k * u a k else 0)"
      using on by (intro sum.cong refl) auto
    also have "\<dots> = t" unfolding t_def power2_eq_square by (intro sum.cong refl) (simp add: sum_delta_less)
    finally show ?thesis .
  qed
  have "0 \<le> dot s (\<lambda>l. e l - p l) (\<lambda>l. e l - p l)" by (rule dot_self_nonneg)
  also have "dot s (\<lambda>l. e l - p l) (\<lambda>l. e l - p l) = dot s e e - 2 * dot s e p + dot s p p"
    unfolding dot_def by (simp add: algebra_simps sum_subtractf sum.distrib sum_distrib_left)
  finally show ?thesis using ee ep pp unfolding t_def by simp
qed

text \<open>$N$ orthonormal vectors in $\mathbb{R}^s$ force $N\le s$.\<close>
lemma orthonormal_le:
  assumes on: "\<forall>a<N. \<forall>b<N. dot s (u a) (u b) = (if a = b then 1 else 0)"
  shows "N \<le> s"
proof -
  have "real N = (\<Sum>a<N. dot s (u a) (u a))" using on by simp
  also have "\<dots> = (\<Sum>l<s. \<Sum>a<N. (u a l)\<^sup>2)"
    unfolding dot_def by (subst sum.swap) (simp add: power2_eq_square)
  also have "\<dots> \<le> (\<Sum>l<s. 1)" by (rule sum_mono) (use bessel_unit[OF on] in simp)
  also have "\<dots> = real s" by simp
  finally show ?thesis by simp
qed

section \<open>The lower bound\<close>

definition bw :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "bw i = (\<lambda>j. if j = 0 then 1 else if j = 1 then of_nat i else 0)"

lemma bw_indep:
  assumes "i \<noteq> i'" shows "indep2 (bw i) (bw i')"
  unfolding indep2_def
proof (intro allI impI)
  fix a b :: real
  assume h: "\<forall>k<3. a * bw i k + b * bw i' k = 0"
  have e0: "a + b = 0" using h[rule_format, of 0] by (simp add: bw_def)
  have e1: "a * of_nat i + b * of_nat i' = 0" using h[rule_format, of 1] by (simp add: bw_def)
  have bb: "b = - a" using e0 by (simp add: eq_neg_iff_add_eq_0 add.commute)
  have "a * (of_nat i - of_nat i') = 0" using e1 bb by (simp add: algebra_simps)
  moreover have "(of_nat i :: real) - of_nat i' \<noteq> 0" using assms by simp
  ultimately have "a = 0" by simp
  with bb show "a = 0 \<and> b = 0" by simp
qed

text \<open>Main lemma of section 5: every representation of $F_m$ by $s$ squares has $s\ge2m$.\<close>
theorem wit3_length:
  assumes rep: "\<forall>x y. sos_form m 3 s c x y = F_wit m x y"
  shows "2 * m \<le> s"
proof -
  have N: "dot s (colv c i y) (colv c i y) = qform i y" if "i < m" for i y
    using rep sos_form_ue[OF that] F_wit_ue[OF that] by metis
  have O: "dot s (colv c i y) (colv c i' y) = 0" if "i < m" "i' < m" "i \<noteq> i'" for i i' y
  proof -
    have "dot s (\<lambda>k. colv c i y k + colv c i' y k) (\<lambda>k. colv c i y k + colv c i' y k) = qform i y + qform i' y"
      using rep sos_form_ue2[OF that(1,2)] F_wit_ue2[OF that] by metis
    then have "dot s (colv c i y) (colv c i y) + 2 * dot s (colv c i y) (colv c i' y)
        + dot s (colv c i' y) (colv c i' y) = qform i y + qform i' y"
      by (simp add: dot_add_left dot_add_right dot_comm)
    then show ?thesis using N that by simp
  qed
  \<comment> \<open>$M_ib_i=0$.\<close>
  have Mb: "\<forall>k<s. colv c i (bw i) k = 0" if "i < m" for i
  proof -
    have "dot s (colv c i (bw i)) (colv c i (bw i)) = 0" using N[OF that] by (simp add: qform_def bw_def)
    then show ?thesis using dot_self_zero by blast
  qed
  have Mb': "\<forall>k<s. col c i 0 k + col c i 1 k * of_nat i = 0" if "i < m" for i
    using Mb[OF that] by (simp add: colv_expand bw_def)
  \<comment> \<open>the columns $w_{i1},w_{i2}$ are orthonormal.\<close>
  have n11: "dot s (col c i 1) (col c i 1) = 1" if "i < m" for i
    using N[OF that, of "ue 1"] by (simp add: colv_expand ue_def qform_def)
  have n22: "dot s (col c i 2) (col c i 2) = 1" if "i < m" for i
    using N[OF that, of "ue 2"] by (simp add: colv_expand ue_def qform_def)
  have n12: "dot s (col c i 1) (col c i 2) = 0" if "i < m" for i
  proof -
    have "dot s (\<lambda>k. col c i 1 k + col c i 2 k) (\<lambda>k. col c i 1 k + col c i 2 k) = 2"
      using N[OF that, of "\<lambda>l. ue 1 l + ue 2 l"] by (simp add: colv_expand ue_def qform_def)
    then show ?thesis using n11[OF that] n22[OF that]
      by (simp add: dot_add_left dot_add_right dot_comm)
  qed
  \<comment> \<open>for $i\neq i'$, $K=M_i^{\mathsf T}M_{i'}$ vanishes.\<close>
  have cross: "dot s (col c i j) (col c i' l) = 0"
    if ii: "i < m" "i' < m" "i \<noteq> i'" and jl: "j < 3" "l < 3" for i i' j l
  proof -
    define K where "K = (\<lambda>j l. dot s (col c i j) (col c i' l))"
    have Kd: "K j j = 0" if "j < 3" for j
    proof -
      have "colv c i (ue j) = col c i j" "colv c i' (ue j) = col c i' j"
        using less3_cases[OF that] by (auto simp: colv_expand ue_def)
      then show ?thesis using O[OF ii, of "ue j"] unfolding K_def by simp
    qed
    have Ka: "K l j = - K j l" if "j < 3" "l < 3" for j l
    proof (cases "j = l")
      case True then show ?thesis using Kd that by simp
    next
      case False
      have "colv c i (\<lambda>q. ue j q + ue l q) = (\<lambda>k. col c i j k + col c i l k)"
           "colv c i' (\<lambda>q. ue j q + ue l q) = (\<lambda>k. col c i' j k + col c i' l k)"
        using less3_cases[OF that(1)] less3_cases[OF that(2)] False by (auto simp: colv_expand ue_def)
      then have "K j j + K j l + K l j + K l l = 0"
        using O[OF ii, of "\<lambda>q. ue j q + ue l q"] unfolding K_def
        by (simp add: dot_add_left dot_add_right)
      then show ?thesis using Kd that by simp
    qed
    have anti: "antisym3 K" unfolding antisym3_def using Ka by blast
    have k2: "kills3 K (bw i')"
      unfolding kills3_def
    proof (intro allI impI)
      fix j :: nat assume "j < 3"
      have "mulv3 K (bw i') j = dot s (col c i j) (\<lambda>k. col c i' 0 k + col c i' 1 k * of_nat i')"
        unfolding mulv3_expand K_def bw_def by (simp add: dot_add_right dot_scale_right)
      also have "\<dots> = 0" by (rule dot_cong_zero_right) (use Mb'[OF ii(2)] in simp)
      finally show "mulv3 K (bw i') j = 0" .
    qed
    have k1: "kills3 K (bw i)"
      unfolding kills3_def
    proof (intro allI impI)
      fix l :: nat assume l: "l < 3"
      have "dot s (\<lambda>k. col c i 0 k + col c i 1 k * of_nat i) (col c i' l) = 0"
        by (rule dot_cong_zero_left) (use Mb'[OF ii(1)] in simp)
      then have "K 0 l + K 1 l * of_nat i = 0"
        unfolding K_def by (simp add: dot_add_left dot_scale_left)
      moreover have "mulv3 K (bw i) l = K l 0 + K l 1 * of_nat i"
        unfolding mulv3_expand bw_def by simp
      ultimately show "mulv3 K (bw i) l = 0" using Ka[of 0 l] Ka[of 1 l] l by simp
    qed
    have "zero3 K" by (rule antisym3_two_kernel_zero[OF anti k1 k2 bw_indep[OF ii(3)]])
    then show ?thesis using jl unfolding zero3_def K_def by blast
  qed
  \<comment> \<open>the $2m$ vectors $u_{2i}=w_{i1}$, $u_{2i+1}=w_{i2}$.\<close>
  define u where "u a = col c (a div 2) (Suc (a mod 2))" for a
  have on: "\<forall>a<2 * m. \<forall>b<2 * m. dot s (u a) (u b) = (if a = b then 1 else 0)"
  proof (intro allI impI)
    fix a b assume a: "a < 2 * m" and b: "b < 2 * m"
    have am: "a div 2 < m" and bm: "b div 2 < m" using a b by auto
    have ar: "a mod 2 = 0 \<or> a mod 2 = 1" and br: "b mod 2 = 0 \<or> b mod 2 = 1" by auto
    show "dot s (u a) (u b) = (if a = b then 1 else 0)"
    proof (cases "a div 2 = b div 2")
      case True
      then have e: "a = b \<longleftrightarrow> a mod 2 = b mod 2" by (metis div_mult_mod_eq)
      show ?thesis
        using ar br n11[OF am] n22[OF am] n12[OF am] True e
        unfolding u_def by (auto simp: dot_comm numeral_2_eq_2)
    next
      case False
      then have "a \<noteq> b" by auto
      moreover have "dot s (u a) (u b) = 0"
        unfolding u_def by (rule cross[OF am bm False]) (use ar br in auto)
      ultimately show ?thesis by simp
    qed
  qed
  show ?thesis by (rule orthonormal_le[OF on])
qed

text \<open>Lower bound $\mathrm{BSR}(m,3)\ge 2m$: if every $m\times3$ sum of squares of bilinear forms is a
  sum of at most $N$ squares, then $N\ge2m$ (apply the hypothesis to the witness $F_m$).\<close>
theorem bsr_width_three_lower:
  assumes "bsr_le m 3 N" shows "2 * m \<le> N"
proof -
  obtain s c where s: "s \<le> N" and e: "\<forall>x y. sos_form m 3 (2 * m) wit3 x y = sos_form m 3 s c x y"
    using assms unfolding bsr_le_def by blast
  have "\<forall>x y. sos_form m 3 s c x y = F_wit m x y" using e wit3_sos by metis
  then have "2 * m \<le> s" by (rule wit3_length)
  with s show ?thesis by simp
qed

text \<open>With BSSV Theorem 1.4 (hypothesis of \<open>bsr_upper_width_three\<close>) the value lies in $\{2m,2m+1\}$.\<close>
corollary bsr_width_three_bracket:
  assumes BSSV_1_4: "\<And>p. 2 \<le> p \<Longrightarrow> bsr_le p 2 (p + 1)" and m: "3 \<le> m"
  shows "bsr_le m 3 (2 * m + 1)" and "\<And>N. bsr_le m 3 N \<Longrightarrow> 2 * m \<le> N"
  using bsr_upper_width_three[OF BSSV_1_4 m] bsr_width_three_lower by auto

end
