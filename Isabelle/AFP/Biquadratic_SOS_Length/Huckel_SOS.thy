theory Huckel_SOS
  imports "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Polynomial"
begin

text \<open>Sums of squares of bilinear forms attached to a symmetric matrix \<open>H\<close>.
The form is \<open>(x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2) |y|\<^sup>2 + 2 x\<^sub>1 x\<^sub>2 y\<^sup>T H y\<close>. A representation by \<open>r\<close> squares
is a pair of \<open>r \<times> n\<close> matrices \<open>A\<close>, \<open>B\<close>: the squares are the coordinates of
\<open>x\<^sub>1 A y + x\<^sub>2 B y\<close>.\<close>

section \<open>Representations and isometries\<close>

definition form :: "real^'n^'n \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real" where
  "form H x1 x2 y = (x1\<^sup>2 + x2\<^sup>2) * (y \<bullet> y) + 2 * x1 * x2 * (y \<bullet> (H *v y))"

definition represents :: "real^'n^'r \<Rightarrow> real^'n^'r \<Rightarrow> real^'n^'n \<Rightarrow> bool" where
  "represents A B H \<longleftrightarrow>
    (\<forall>x1 x2 y. (norm (x1 *\<^sub>R (A *v y) + x2 *\<^sub>R (B *v y)))\<^sup>2 = form H x1 x2 y)"

definition sym_mat :: "real^'n^'n \<Rightarrow> bool" where
  "sym_mat S \<longleftrightarrow> transpose S = S"

lemma norm_sq_comb:
  fixes u v :: "'a::real_inner"
  shows "(norm (a *\<^sub>R u + b *\<^sub>R v))\<^sup>2 =
    a\<^sup>2 * (u \<bullet> u) + b\<^sup>2 * (v \<bullet> v) + 2 * a * b * (u \<bullet> v)"
  unfolding power2_norm_eq_inner
  by (simp add: inner_add_left inner_add_right inner_commute[of v u] power2_eq_square algebra_simps)

lemma mat_mul_add_left: "(A + B) ** C = A ** C + B ** C"
  for A B :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib algebra_simps)

lemma mat_mul_scale_left: "(c *\<^sub>R A) ** C = c *\<^sub>R (A ** C)"
  for A :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left algebra_simps)

lemma mat_mul_scale_right: "A ** (c *\<^sub>R C) = c *\<^sub>R (A ** C)"
  for A :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left algebra_simps)

lemma adjoint_dot: "(A *v y) \<bullet> w = y \<bullet> (transpose A *v w)"
  for A :: "real^'n^'m"
  by (metis dot_lmul_matrix vector_transpose_matrix)

lemma dot_mul_mul: "(A *v y) \<bullet> (B *v z) = y \<bullet> ((transpose A ** B) *v z)"
  for A B :: "real^'n^'m"
  by (simp add: adjoint_dot matrix_vector_mul_assoc)

lemma quad_zero_imp_zero:
  fixes S :: "real^'n^'n"
  assumes sym: "sym_mat S" and q: "\<And>y. y \<bullet> (S *v y) = 0"
  shows "S = 0"
proof -
  have swap: "y \<bullet> (S *v z) = z \<bullet> (S *v y)" for y z
  proof -
    have "y \<bullet> (S *v z) = (transpose S *v y) \<bullet> z"
      using adjoint_dot[of "transpose S" y z] by (simp add: inner_commute)
    also have "\<dots> = z \<bullet> (S *v y)"
      using sym by (simp add: sym_mat_def inner_commute)
    finally show ?thesis .
  qed
  have bil: "y \<bullet> (S *v z) = 0" for y z
  proof -
    have "(y + z) \<bullet> (S *v (y + z)) = 0" by (rule q)
    hence "y \<bullet> (S *v y) + y \<bullet> (S *v z) + z \<bullet> (S *v y) + z \<bullet> (S *v z) = 0"
      by (simp add: matrix_vector_right_distrib inner_add_left inner_add_right)
    thus ?thesis using q[of y] q[of z] swap[of y z] by simp
  qed
  have "S *v z = 0" for z
    using bil[of "S *v z" z] by simp
  thus ?thesis
    by (simp add: matrix_eq[where A = S and B = 0] matrix_vector_mul_lid)
qed

lemma sym_gram: "sym_mat (transpose A ** A)"
  for A :: "real^'n^'m"
  by (simp add: sym_mat_def matrix_transpose_mul)

theorem represents_iff:
  fixes A B :: "real^'n^'r" and H :: "real^'n^'n"
  assumes symH: "sym_mat H"
  shows "represents A B H \<longleftrightarrow>
    transpose A ** A = mat 1 \<and> transpose B ** B = mat 1 \<and>
    transpose A ** B + transpose B ** A = H + H"
proof
  assume r: "represents A B H"
  have val: "x1\<^sup>2 * ((A *v y) \<bullet> (A *v y)) + x2\<^sup>2 * ((B *v y) \<bullet> (B *v y))
      + 2 * x1 * x2 * ((A *v y) \<bullet> (B *v y)) = form H x1 x2 y" for x1 x2 y
  proof -
    have "(norm (x1 *\<^sub>R (A *v y) + x2 *\<^sub>R (B *v y)))\<^sup>2 = form H x1 x2 y"
      using r by (simp add: represents_def)
    thus ?thesis by (simp add: norm_sq_comb)
  qed
  have a: "(A *v y) \<bullet> (A *v y) = y \<bullet> y" for y
    using val[of 1 y 0] by (simp add: form_def)
  have b: "(B *v y) \<bullet> (B *v y) = y \<bullet> y" for y
    using val[of 0 y 1] by (simp add: form_def)
  have c: "(A *v y) \<bullet> (B *v y) = y \<bullet> (H *v y)" for y
    using val[of 1 y 1] a[of y] b[of y] by (simp add: form_def)
  have idq: "y \<bullet> ((mat 1 :: real^'n^'n) *v y) = y \<bullet> y" for y :: "real^'n"
    by (simp add: matrix_vector_mul_lid)
  have one_sym: "sym_mat (mat 1 :: real^'n^'n)"
    by (simp add: sym_mat_def transpose_mat)
  have diff_sym: "sym_mat (S - T)" if "sym_mat S" "sym_mat T" for S T :: "real^'n^'n"
    using that by (simp add: sym_mat_def transpose_def vec_eq_iff)
  have add_sym: "sym_mat (S + T)" if "sym_mat S" "sym_mat T" for S T :: "real^'n^'n"
    using that by (simp add: sym_mat_def transpose_def vec_eq_iff)
  have "transpose A ** A - mat 1 = 0"
    by (rule quad_zero_imp_zero)
      (use sym_gram[of A] one_sym diff_sym in \<open>auto simp: matrix_vector_mult_diff_rdistrib inner_diff_right
        idq dot_mul_mul[symmetric] a\<close>)
  moreover have "transpose B ** B - mat 1 = 0"
    by (rule quad_zero_imp_zero)
      (use sym_gram[of B] one_sym diff_sym in \<open>auto simp: matrix_vector_mult_diff_rdistrib inner_diff_right
        idq dot_mul_mul[symmetric] b\<close>)
  moreover have "transpose A ** B + transpose B ** A - (H + H) = 0"
  proof (rule quad_zero_imp_zero)
    show "sym_mat (transpose A ** B + transpose B ** A - (H + H))"
      by (rule diff_sym) (use symH add_sym in \<open>auto simp: sym_mat_def transpose_def vec_eq_iff
        matrix_matrix_mult_def ac_simps\<close>)
    show "y \<bullet> ((transpose A ** B + transpose B ** A - (H + H)) *v y) = 0" for y
    proof -
      have e1: "y \<bullet> ((transpose A ** B) *v y) = y \<bullet> (H *v y)"
        using c[of y] dot_mul_mul[of A y B y] by simp
      have e2: "y \<bullet> ((transpose B ** A) *v y) = y \<bullet> (H *v y)"
        using c[of y] dot_mul_mul[of B y A y] by (simp add: inner_commute[of "B *v y" "A *v y"])
      have dist: "(S + T - U) *v y = S *v y + T *v y - U *v y" for S T U :: "real^'n^'n"
        by (simp add: matrix_vector_mult_diff_rdistrib matrix_vector_mult_add_rdistrib)
      have dH: "(H + H) *v y = H *v y + H *v y"
        by (rule matrix_vector_mult_add_rdistrib)
      show ?thesis
        by (simp only: dist dH inner_diff_right inner_add_right e1 e2)
    qed
  qed
  ultimately show "transpose A ** A = mat 1 \<and> transpose B ** B = mat 1 \<and>
      transpose A ** B + transpose B ** A = H + H"
    by simp
next
  assume h: "transpose A ** A = mat 1 \<and> transpose B ** B = mat 1 \<and>
      transpose A ** B + transpose B ** A = H + H"
  have a: "(A *v y) \<bullet> (A *v y) = y \<bullet> y" for y
    using h by (simp add: dot_mul_mul matrix_vector_mul_lid)
  have b: "(B *v y) \<bullet> (B *v y) = y \<bullet> y" for y
    using h by (simp add: dot_mul_mul matrix_vector_mul_lid)
  have hh: "transpose A ** B + transpose B ** A = H + H"
    using h by blast
  have c: "2 * ((A *v y) \<bullet> (B *v y)) = 2 * (y \<bullet> (H *v y))" for y
  proof -
    have m: "(transpose A ** B + transpose B ** A) *v y = (H + H) *v y"
      by (simp only: hh)
    have "y \<bullet> ((transpose A ** B) *v y) + y \<bullet> ((transpose B ** A) *v y) =
        y \<bullet> (H *v y) + y \<bullet> (H *v y)"
      using arg_cong[OF m, of "\<lambda>v. y \<bullet> v"]
      by (simp only: matrix_vector_mult_add_rdistrib inner_add_right)
    hence "(A *v y) \<bullet> (B *v y) + (B *v y) \<bullet> (A *v y) = y \<bullet> (H *v y) + y \<bullet> (H *v y)"
      by (simp only: dot_mul_mul)
    thus ?thesis by (simp add: inner_commute[of "B *v y" "A *v y"])
  qed
  show "represents A B H"
    unfolding represents_def form_def
  proof (intro allI)
    fix x1 x2 and y :: "real^'n"
    have "(norm (x1 *\<^sub>R (A *v y) + x2 *\<^sub>R (B *v y)))\<^sup>2 =
        x1\<^sup>2 * ((A *v y) \<bullet> (A *v y)) + x2\<^sup>2 * ((B *v y) \<bullet> (B *v y))
        + x1 * x2 * (2 * ((A *v y) \<bullet> (B *v y)))"
      by (simp add: norm_sq_comb algebra_simps)
    also have "\<dots> = (x1\<^sup>2 + x2\<^sup>2) * (y \<bullet> y) + 2 * x1 * x2 * (y \<bullet> (H *v y))"
      by (simp add: a b c algebra_simps)
    finally show "(norm (x1 *\<^sub>R (A *v y) + x2 *\<^sub>R (B *v y)))\<^sup>2 =
        (x1\<^sup>2 + x2\<^sup>2) * (y \<bullet> y) + 2 * x1 * x2 * (y \<bullet> (H *v y))" .
  qed
qed

section \<open>The determinant criterion: necessity\<close>

definition pencil :: "real^'n^'n \<Rightarrow> real \<Rightarrow> real^'n^'n" where
  "pencil H t = (1 + t\<^sup>2) *\<^sub>R mat 1 + (2 * t) *\<^sub>R H"

lemma det_poly_entries:
  fixes P :: "real poly^'n^'n"
  shows "poly (Determinants.det P) t = Determinants.det (\<chi> i j. poly (P $ i $ j) t)"
proof -
  have "poly (of_int (sign p) * (\<Prod>i\<in>UNIV. P $ i $ p i)) t =
      of_int (sign p) * (\<Prod>i\<in>UNIV. poly (P $ i $ p i) t)" for p :: "'n \<Rightarrow> 'n"
    by (simp add: poly_prod sign_def)
  thus ?thesis
    by (simp add: Determinants.det_def poly_sum)
qed

theorem det_pencil_square:
  fixes A B H :: "real^'n^'n"
  assumes sym: "sym_mat H" and r: "represents A B H"
  shows "\<exists>p :: real poly. \<forall>t. Determinants.det (pencil H t) = (poly p t)\<^sup>2"
proof -
  have h: "transpose A ** A = mat 1" "transpose B ** B = mat 1"
    "transpose A ** B + transpose B ** A = H + H"
    using r represents_iff[OF sym] by auto
  define P :: "real poly^'n^'n" where "P = (\<chi> i j. [:A $ i $ j, B $ i $ j:])"
  have ent: "(\<chi> i j. poly (P $ i $ j) t) = A + t *\<^sub>R B" for t
    by (simp add: P_def vec_eq_iff algebra_simps)
  have fact: "pencil H t = transpose (A + t *\<^sub>R B) ** (A + t *\<^sub>R B)" for t
  proof -
    have tr: "transpose (A + t *\<^sub>R B) = transpose A + t *\<^sub>R transpose B"
      by (simp add: transpose_def vec_eq_iff)
    have "transpose (A + t *\<^sub>R B) ** (A + t *\<^sub>R B) =
        transpose A ** A + t *\<^sub>R (transpose A ** B + transpose B ** A) + t\<^sup>2 *\<^sub>R (transpose B ** B)"
      unfolding tr
      by (simp add: matrix_add_ldistrib mat_mul_add_left mat_mul_scale_left mat_mul_scale_right
          power2_eq_square algebra_simps scaleR_add_right)
    also have "\<dots> = pencil H t"
      using h by (simp add: pencil_def algebra_simps scaleR_add_right scaleR_add_left
          flip: scaleR_2)
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (intro exI allI)
    fix t
    have "Determinants.det (pencil H t) = Determinants.det (A + t *\<^sub>R B) * Determinants.det (A + t *\<^sub>R B)"
      by (simp add: fact det_mul det_transpose)
    also have "\<dots> = (poly (Determinants.det P) t)\<^sup>2"
      by (simp add: det_poly_entries ent power2_eq_square)
    finally show "Determinants.det (pencil H t) = (poly (Determinants.det P) t)\<^sup>2" .
  qed
qed

section \<open>Rings and chains\<close>

text \<open>A ring of \<open>n\<close> sites needs only \<open>n\<close> squares; a chain is the ring of \<open>n + 1\<close> sites
with one site removed.\<close>

lemma ring_identity:
  fixes y :: "nat \<Rightarrow> real"
  assumes n: "0 < n"
  shows "(\<Sum>i<n. (x1 * y i + x2 * y (Suc i mod n))\<^sup>2) =
    (x1\<^sup>2 + x2\<^sup>2) * (\<Sum>i<n. (y i)\<^sup>2) + 2 * x1 * x2 * (\<Sum>i<n. y i * y (Suc i mod n))"
proof -
  have fm: "Suc i mod n = (if Suc i = n then 0 else Suc i)" if "i < n" for i
    using that by (auto simp: Suc_le_eq le_neq_implies_less)
  have inj: "inj_on (\<lambda>i. Suc i mod n) {..<n}"
    by (rule inj_onI) (auto simp: fm split: if_splits)
  have sub: "(\<lambda>i. Suc i mod n) ` {..<n} \<subseteq> {..<n}"
    using n by auto
  have bij: "bij_betw (\<lambda>i. Suc i mod n) {..<n} {..<n}"
    using endo_inj_surj[OF finite_lessThan sub inj] inj by (simp add: bij_betw_def)
  have shift: "(\<Sum>i<n. (y (Suc i mod n))\<^sup>2) = (\<Sum>i<n. (y i)\<^sup>2)"
    using sum.reindex_bij_betw[OF bij, of "\<lambda>i. (y i)\<^sup>2"] by simp
  have "(\<Sum>i<n. (x1 * y i + x2 * y (Suc i mod n))\<^sup>2) =
      x1\<^sup>2 * (\<Sum>i<n. (y i)\<^sup>2) + x2\<^sup>2 * (\<Sum>i<n. (y (Suc i mod n))\<^sup>2)
      + 2 * x1 * x2 * (\<Sum>i<n. y i * y (Suc i mod n))"
    by (simp add: sum_distrib_left sum.distrib[symmetric] power2_sum power_mult_distrib algebra_simps)
  thus ?thesis by (simp add: shift algebra_simps)
qed

lemma chain_identity:
  fixes z :: "nat \<Rightarrow> real"
  assumes z0: "z 0 = 0" and zn: "z (Suc n) = 0"
  shows "(\<Sum>i\<le>n. (x1 * z i + x2 * z (Suc i))\<^sup>2) =
    (x1\<^sup>2 + x2\<^sup>2) * (\<Sum>i\<le>n. (z i)\<^sup>2) + 2 * x1 * x2 * (\<Sum>i\<le>n. z i * z (Suc i))"
proof -
  have shift: "(\<Sum>i\<le>n. (z (Suc i))\<^sup>2) = (\<Sum>i\<le>n. (z i)\<^sup>2)"
  proof -
    have "(\<Sum>i\<le>n. (z (Suc i))\<^sup>2) + (z 0)\<^sup>2 = (\<Sum>i\<le>Suc n. (z i)\<^sup>2)"
      by (simp only: sum.atMost_Suc_shift)
    also have "\<dots> = (\<Sum>i\<le>n. (z i)\<^sup>2) + (z (Suc n))\<^sup>2" by simp
    finally show ?thesis using z0 zn by simp
  qed
  have "(\<Sum>i\<le>n. (x1 * z i + x2 * z (Suc i))\<^sup>2) =
      x1\<^sup>2 * (\<Sum>i\<le>n. (z i)\<^sup>2) + x2\<^sup>2 * (\<Sum>i\<le>n. (z (Suc i))\<^sup>2)
      + 2 * x1 * x2 * (\<Sum>i\<le>n. z i * z (Suc i))"
    by (simp add: sum_distrib_left sum.distrib[symmetric] power2_sum power_mult_distrib algebra_simps)
  thus ?thesis by (simp add: shift algebra_simps)
qed

section \<open>The chain determinant is not a square\<close>

text \<open>The polynomial \<open>1 + t\<^sup>2 + \<dots> + t\<^sup>2\<^sup>n\<close>, determinant of the pencil of a chain of \<open>n\<close> sites,
is never a square for \<open>n \<ge> 1\<close>: a square factor of \<open>t\<^sup>2\<^sup>n\<^sup>+\<^sup>2 - 1\<close> would divide its derivative.\<close>

lemma geometric_values:
  "poly (\<Sum>j\<le>m. [:0, 0, 1:] ^ j :: real poly) 0 = 1 \<and>
   poly (\<Sum>j\<le>m. [:0, 0, 1:] ^ j :: real poly) 1 = real m + 1"
  by (induction m) (simp_all add: poly_power)

theorem geometric_not_square:
  fixes p :: "real poly"
  assumes n: "0 < n"
  shows "(\<Sum>j\<le>n. [:0, 0, 1:] ^ j) \<noteq> p\<^sup>2"
proof
  define X :: "real poly" where "X = [:0, 1:]"
  assume sq: "(\<Sum>j\<le>n. [:0, 0, 1:] ^ j) = p\<^sup>2"
  have X2: "[:0, 0, 1:] = X\<^sup>2"
    by (simp add: X_def power2_eq_square)
  have s: "(\<Sum>j\<le>n. (X\<^sup>2) ^ j) = p\<^sup>2"
    using sq by (simp only: X2)
  have geo: "(X\<^sup>2 - 1) * (\<Sum>j\<le>n. (X\<^sup>2) ^ j) = (X\<^sup>2) ^ Suc n - 1"
    by (metis lessThan_Suc_atMost power_diff_1_eq mult.commute)
  define G where "G = X ^ (2 * n + 2) - 1"
  have pw: "X ^ (2 * n + 2) = (X\<^sup>2) ^ Suc n"
    by (simp only: power_mult[symmetric]) simp
  have Geq: "G = (X\<^sup>2 - 1) * p\<^sup>2"
  proof -
    have "G = (X\<^sup>2) ^ Suc n - 1" by (simp only: G_def pw)
    also have "\<dots> = (X\<^sup>2 - 1) * (\<Sum>j\<le>n. (X\<^sup>2) ^ j)" by (rule geo[symmetric])
    also have "\<dots> = (X\<^sup>2 - 1) * p\<^sup>2" by (simp only: s)
    finally show ?thesis .
  qed
  have dX: "pderiv X = 1"
    by (simp add: X_def pderiv_pCons one_pCons)
  have dG: "pderiv G = smult (of_nat (2 * n + 2)) (X ^ (2 * n + 1))"
  proof -
    have "pderiv (X ^ Suc (2 * n + 1)) = smult (of_nat (Suc (2 * n + 1))) (X ^ (2 * n + 1)) * pderiv X"
      by (rule pderiv_power_Suc)
    thus ?thesis by (simp add: G_def pderiv_diff dX pderiv_1)
  qed
  have dvdG: "p dvd G"
    using Geq by (simp add: power2_eq_square)
  have dvddG: "p dvd pderiv G"
  proof -
    have "pderiv G = pderiv (X\<^sup>2 - 1) * (p * p) + (X\<^sup>2 - 1) * (p * pderiv p + pderiv p * p)"
      by (simp add: Geq pderiv_mult power2_eq_square)
    also have "\<dots> = p * (pderiv (X\<^sup>2 - 1) * p + (X\<^sup>2 - 1) * (pderiv p + pderiv p))"
      by (simp add: algebra_simps)
    finally show ?thesis by simp
  qed
  have comb: "X * pderiv G - smult (of_nat (2 * n + 2)) G = [:of_nat (2 * n + 2):]"
  proof -
    have e: "X * X ^ (2 * n + 1) = X ^ (2 * n + 2)"
    proof -
      have "X ^ Suc (2 * n + 1) = X * X ^ (2 * n + 1)" by (rule power_Suc)
      moreover have "Suc (2 * n + 1) = 2 * n + 2" by simp
      ultimately show ?thesis by simp
    qed
    have x: "X * pderiv G = smult (of_nat (2 * n + 2)) (X ^ (2 * n + 2))"
      unfolding dG mult_smult_right e ..
    have g: "smult (of_nat (2 * n + 2)) G =
        smult (of_nat (2 * n + 2)) (X ^ (2 * n + 2)) - [:of_nat (2 * n + 2):]"
      unfolding G_def smult_diff_right by (simp add: smult_one)
    show ?thesis by (simp only: x g)
  qed
  have "p dvd X * pderiv G - smult (of_nat (2 * n + 2)) G"
    using dvdG dvddG by (intro dvd_diff dvd_mult dvd_smult)
  hence "p dvd [:of_nat (2 * n + 2) :: real:]"
    by (simp only: comb)
  hence "degree p \<le> degree [:of_nat (2 * n + 2) :: real:]"
    by (rule dvd_imp_degree_le) simp
  hence "degree p = 0" by simp
  hence pc: "poly p 0 = poly p 1"
    by (subst (1 2) degree_0_id[symmetric]) (use \<open>degree p = 0\<close> in \<open>auto simp: degree_eq_zeroE\<close>)
  have "1 = (poly p 0)\<^sup>2"
    using arg_cong[OF sq, of "\<lambda>q. poly q 0"] geometric_values[of n] by (simp add: poly_power)
  moreover have "real n + 1 = (poly p 1)\<^sup>2"
    using arg_cong[OF sq, of "\<lambda>q. poly q 1"] geometric_values[of n] by (simp add: poly_power)
  ultimately show False using pc n by simp
qed

section \<open>A closed bond with weight \<open>a\<close>\<close>

text \<open>Weight \<open>a\<close> on the closing bond of a ring. The expression is the sum of \<open>n\<close> squares of the
ring with that weight plus one further square, of size \<open>\<surd>(1 - a\<^sup>2)\<close>, which vanishes exactly for
the two perfect closures \<open>a = 1\<close> and \<open>a = -1\<close>.\<close>

lemma weighted_ring_identity:
  fixes y :: "nat \<Rightarrow> real"
  assumes a: "\<bar>a\<bar> \<le> 1"
  shows "(x1 * y 0 + x2 * a * y (Suc m))\<^sup>2 + (\<Sum>i\<le>m. (x1 * y (Suc i) + x2 * y i)\<^sup>2)
      + (sqrt (1 - a\<^sup>2) * x2 * y (Suc m))\<^sup>2 =
    (x1\<^sup>2 + x2\<^sup>2) * (\<Sum>i\<le>Suc m. (y i)\<^sup>2)
      + 2 * x1 * x2 * (a * y 0 * y (Suc m) + (\<Sum>i\<le>m. y i * y (Suc i)))"
proof -
  have s: "(sqrt (1 - a\<^sup>2))\<^sup>2 = 1 - a\<^sup>2"
    using a by (intro real_sqrt_pow2) (simp add: abs_square_le_1)
  have sh: "(\<Sum>i\<le>Suc m. (y i)\<^sup>2) = (y 0)\<^sup>2 + (\<Sum>i\<le>m. (y (Suc i))\<^sup>2)"
    by (simp only: sum.atMost_Suc_shift)
  have sh2: "(\<Sum>i\<le>Suc m. (y i)\<^sup>2) = (\<Sum>i\<le>m. (y i)\<^sup>2) + (y (Suc m))\<^sup>2"
    by simp
  have e: "(\<Sum>i\<le>m. (x1 * y (Suc i) + x2 * y i)\<^sup>2) =
      x1\<^sup>2 * (\<Sum>i\<le>m. (y (Suc i))\<^sup>2) + x2\<^sup>2 * (\<Sum>i\<le>m. (y i)\<^sup>2)
      + 2 * x1 * x2 * (\<Sum>i\<le>m. y i * y (Suc i))"
    by (simp add: sum_distrib_left sum.distrib[symmetric] power2_sum power_mult_distrib algebra_simps)
  have q: "(sqrt (1 - a\<^sup>2) * x2 * y (Suc m))\<^sup>2 = (1 - a\<^sup>2) * x2\<^sup>2 * (y (Suc m))\<^sup>2"
    by (simp add: power_mult_distrib s)
  have "(x1\<^sup>2 + x2\<^sup>2) * (\<Sum>i\<le>Suc m. (y i)\<^sup>2) =
      x1\<^sup>2 * ((y 0)\<^sup>2 + (\<Sum>i\<le>m. (y (Suc i))\<^sup>2)) + x2\<^sup>2 * ((\<Sum>i\<le>m. (y i)\<^sup>2) + (y (Suc m))\<^sup>2)"
    by (simp only: distrib_right flip: sh sh2)
  thus ?thesis
    by (simp only: e q) (simp add: power2_sum power_mult_distrib algebra_simps)
qed

section \<open>A cyclic vector forbids \<open>n\<close> squares\<close>

text \<open>If \<open>H\<close> has a cyclic vector and is the symmetric part of an orthogonal matrix \<open>T\<close>, then the
skew part of \<open>T\<close> commutes with \<open>H\<close>, so its values on the Krylov basis are symmetric and skew at
once. Hence \<open>T = H\<close> and \<open>H\<^sup>2 = I\<close>. No determinant or spectral theorem is needed.\<close>

theorem cyclic_square_rep_involution:
  fixes A B H :: "real^'n^'n" and e :: "real^'n"
  assumes symH: "sym_mat H" and r: "represents A B H"
    and cyc: "span (range (\<lambda>k. (((*v) (H + H)) ^^ k) e)) = UNIV"
  shows "(H + H) *v ((H + H) *v y) = (4::real) *\<^sub>R y"
proof -
  have h3: "transpose A ** A = mat 1" "transpose B ** B = mat 1"
    "transpose A ** B + transpose B ** A = H + H"
    using r represents_iff[OF symH] by auto
  define T where "T = transpose A ** B"
  have tT: "transpose T = transpose B ** A"
    by (simp add: T_def matrix_transpose_mul)
  have AA: "A ** transpose A = mat 1"
    using h3(1) matrix_left_right_inverse by blast
  have BB: "B ** transpose B = mat 1"
    using h3(2) matrix_left_right_inverse by blast
  have TtT: "transpose T ** T = mat 1"
  proof -
    have "transpose T ** T = (transpose B ** A) ** T"
      by (simp only: tT)
    also have "\<dots> = transpose B ** (A ** transpose A) ** B"
      by (simp add: T_def matrix_mul_assoc)
    finally show ?thesis by (simp add: AA h3(2) matrix_mul_rid)
  qed
  have TTt: "T ** transpose T = mat 1"
    using TtT matrix_left_right_inverse by blast
  define f where "f = (\<lambda>x. T *v x)"
  define g where "g = (\<lambda>x. transpose T *v x)"
  define h where "h = (\<lambda>x. (H + H) *v x)"
  define k where "k = (\<lambda>x. f x - g x)"
  have fg: "f (g x) = x" for x
    by (simp only: f_def g_def matrix_vector_mul_assoc TTt matrix_vector_mul_lid)
  have gf: "g (f x) = x" for x
    by (simp only: f_def g_def matrix_vector_mul_assoc TtT matrix_vector_mul_lid)
  have TH: "T + transpose T = H + H"
    by (simp only: tT) (simp only: T_def h3(3))
  have hfg: "h x = f x + g x" for x
  proof -
    have "h x = (T + transpose T) *v x" by (simp only: h_def TH)
    thus ?thesis by (simp only: matrix_vector_mult_add_rdistrib f_def g_def)
  qed
  have fadd: "f (x + y) = f x + f y" and gadd: "g (x + y) = g x + g y" for x y
    by (simp_all only: f_def g_def matrix_vector_right_distrib)
  have fsub: "f (x - y) = f x - f y" and gsub: "g (x - y) = g x - g y" for x y
    by (simp_all only: f_def g_def matrix_vector_mult_diff_distrib)
  have fsc: "f (c *\<^sub>R x) = c *\<^sub>R f x" and gsc: "g (c *\<^sub>R x) = c *\<^sub>R g x" for c x
    by (simp_all only: f_def g_def matrix_vector_mult_scaleR)
  have f0: "f 0 = 0" and g0: "g 0 = 0"
    by (simp_all only: f_def g_def matrix_vector_mult_0_right)
  have kadd: "k (x + y) = k x + k y" for x y
    by (simp add: k_def fadd gadd algebra_simps)
  have ksc: "k (c *\<^sub>R x) = c *\<^sub>R k x" for c x
    by (simp add: k_def fsc gsc scaleR_right_diff_distrib)
  have kz: "k 0 = 0"
    by (simp add: k_def f0 g0)
  have comm: "k (h x) = h (k x)" for x
    by (simp add: k_def hfg fadd gadd fsub gsub fg gf algebra_simps)
  have adj: "x \<bullet> f y = g x \<bullet> y" for x y
    using adjoint_dot[of "transpose T" x y] by (simp add: f_def g_def inner_commute)
  have adj2: "x \<bullet> g y = f x \<bullet> y" for x y
    by (metis adj inner_commute)
  have skew: "x \<bullet> k y = - (k x \<bullet> y)" for x y
    by (simp only: k_def inner_diff_left inner_diff_right adj adj2)
  have selfadj: "x \<bullet> h y = h x \<bullet> y" for x y
    by (simp only: hfg inner_add_left inner_add_right adj adj2 add.commute)
  define p where "p = (\<lambda>j. (h ^^ j) e)"
  have psuc: "p (Suc j) = h (p j)" for j
    by (simp add: p_def)
  have kp: "k (p (Suc j)) = h (k (p j))" for j
    by (simp add: psuc comm)
  have shift: "p a \<bullet> k (p (Suc b)) = p (Suc a) \<bullet> k (p b)" for a b
  proof -
    have "p a \<bullet> k (p (Suc b)) = p a \<bullet> h (k (p b))" by (simp only: kp)
    also have "\<dots> = h (p a) \<bullet> k (p b)" by (rule selfadj)
    also have "\<dots> = p (Suc a) \<bullet> k (p b)" by (simp only: psuc)
    finally show ?thesis .
  qed
  have move: "p a \<bullet> k (p b) = p (a + b) \<bullet> k (p 0)" for a b
  proof (induction b arbitrary: a)
    case 0 show ?case by simp
  next
    case (Suc b)
    have "p a \<bullet> k (p (Suc b)) = p (Suc a) \<bullet> k (p b)" by (rule shift)
    also have "\<dots> = p (Suc a + b) \<bullet> k (p 0)" by (rule Suc.IH)
    finally show ?case by simp
  qed
  have zero: "p a \<bullet> k (p b) = 0" for a b
  proof -
    have "p a \<bullet> k (p b) = p b \<bullet> k (p a)"
      using move[of a b] move[of b a] by (simp add: add.commute)
    moreover have "p a \<bullet> k (p b) = - (p b \<bullet> k (p a))"
      using skew[of "p a" "p b"] by (simp add: inner_commute)
    ultimately show ?thesis by simp
  qed
  have sp: "span (range p) = UNIV"
    using cyc by (simp add: p_def h_def[abs_def])
  have kb: "k (p b) = 0" for b
  proof -
    have sub: "subspace {x. x \<bullet> k (p b) = 0}"
      by (auto simp: subspace_def inner_add_left)
    have "range p \<subseteq> {x. x \<bullet> k (p b) = 0}"
      using zero by auto
    hence "span (range p) \<subseteq> {x. x \<bullet> k (p b) = 0}"
      using sub by (rule span_minimal)
    hence all: "UNIV \<subseteq> {x. x \<bullet> k (p b) = 0}"
      by (simp only: sp)
    have "k (p b) \<in> {x. x \<bullet> k (p b) = 0}"
      using all by (rule subsetD) (rule UNIV_I)
    hence "k (p b) \<bullet> k (p b) = 0"
      by (rule CollectD)
    thus ?thesis by (simp only: inner_eq_zero_iff)
  qed
  have k0: "k x = 0" for x
  proof -
    have sub: "subspace {x. k x = 0}"
      by (auto simp: subspace_def kadd ksc kz)
    have "range p \<subseteq> {x. k x = 0}"
      using kb by auto
    hence "span (range p) \<subseteq> {x. k x = 0}"
      using sub by (rule span_minimal)
    hence all: "UNIV \<subseteq> {x. k x = 0}"
      by (simp only: sp)
    have "x \<in> {x. k x = 0}"
      using all by (rule subsetD) (rule UNIV_I)
    thus ?thesis by (rule CollectD)
  qed
  have fgeq: "f x = g x" for x
    using k0[of x] by (simp add: k_def)
  have gx: "g z = f z" for z
    using fgeq[of z] by simp
  have h1: "h z = f z + f z" for z
    by (simp only: hfg gx)
  have ff: "f (f x) = x" for x
    using fg[of x] by (simp only: gx)
  have hh: "h (h x) = (4::real) *\<^sub>R x" for x
  proof -
    have "h (h x) = f (f x + f x) + f (f x + f x)" by (simp only: h1)
    also have "\<dots> = (f (f x) + f (f x)) + (f (f x) + f (f x))" by (simp only: fadd)
    also have "\<dots> = (x + x) + (x + x)" by (simp only: ff)
    also have "\<dots> = (4::real) *\<^sub>R x" by (simp add: vec_eq_iff)
    finally show ?thesis .
  qed
  show ?thesis using hh[of y] by (simp add: h_def)
qed

theorem chain_needs_more_than_n_squares:
  fixes A B H :: "real^'n^'n" and v :: "nat \<Rightarrow> real^'n"
  assumes symH: "sym_mat H" and n: "2 \<le> n"
    and orth: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> v i \<bullet> v j = (if i = j then 1 else 0)"
    and sp: "span (v ` {..<n}) = UNIV"
    and first: "(H + H) *v v 0 = v 1"
    and mid: "\<And>i. 0 < i \<Longrightarrow> i + 1 < n \<Longrightarrow> (H + H) *v v i = v (i - 1) + v (i + 1)"
    and last: "(H + H) *v v (n - 1) = v (n - 2)"
  shows "\<not> represents A B H"
proof
  assume r: "represents A B H"
  define S where "S = span (range (\<lambda>k. (((*v) (H + H)) ^^ k) (v 0)))"
  have Sinv: "(H + H) *v x \<in> S" if "x \<in> S" for x
    using that unfolding S_def
  proof (induction rule: span_induct_alt)
    case base show ?case by (simp add: span_zero)
  next
    case (step c g x)
    have gs: "(H + H) *v g \<in> span (range (\<lambda>k. (((*v) (H + H)) ^^ k) (v 0)))"
    proof -
      obtain j where gj: "g = (((*v) (H + H)) ^^ j) (v 0)" using step(1) by auto
      have e: "(((*v) (H + H)) ^^ Suc j) (v 0) = (H + H) *v ((((*v) (H + H)) ^^ j) (v 0))"
        by (simp only: funpow.simps comp_def)
      have m: "(H + H) *v g = (((*v) (H + H)) ^^ Suc j) (v 0)"
        by (simp only: gj e)
      show ?thesis
        by (subst m) (intro span_base range_eqI[where x = "Suc j"] refl)
    qed
    have d: "(H + H) *v (c *\<^sub>R g + x) = c *\<^sub>R ((H + H) *v g) + (H + H) *v x"
      by (simp only: matrix_vector_right_distrib matrix_vector_mult_scaleR)
    show ?case
      unfolding d by (intro span_add span_scale gs step(2))
  qed
  have v0: "v 0 \<in> S"
    unfolding S_def by (rule span_base) (auto intro: range_eqI[where x = 0])
  have allv: "v i \<in> S \<and> v (Suc i) \<in> S" if "i + 1 < n" for i
    using that
  proof (induction i)
    case 0
    have "v 1 \<in> S" using Sinv[OF v0] first by simp
    thus ?case using v0 by simp
  next
    case (Suc i)
    have a: "v i \<in> S" "v (Suc i) \<in> S" using Suc by auto
    have "(H + H) *v v (Suc i) = v i + v (Suc (Suc i))"
      using mid[of "Suc i"] Suc.prems by simp
    hence "v (Suc (Suc i)) = (H + H) *v v (Suc i) - v i" by simp
    hence "v (Suc (Suc i)) \<in> S"
      using Sinv[OF a(2)] a(1) unfolding S_def by (simp add: span_diff)
    thus ?case using a by simp
  qed
  have cover: "v ` {..<n} \<subseteq> S"
  proof
    fix x assume "x \<in> v ` {..<n}"
    then obtain i where i: "i < n" "x = v i" by auto
    show "x \<in> S"
    proof (cases "i + 1 < n")
      case True thus ?thesis using allv i by blast
    next
      case False
      hence "i = (i - 1) + 1" "(i - 1) + 1 < n" using i n by auto
      thus ?thesis using allv[of "i - 1"] i by (metis Suc_eq_plus1)
    qed
  qed
  have Sall: "S = UNIV"
  proof -
    have "span (v ` {..<n}) \<subseteq> S"
      by (rule span_minimal[OF cover]) (simp add: S_def subspace_span)
    thus ?thesis using sp by auto
  qed
  have inv: "(H + H) *v ((H + H) *v v 0) = (4::real) *\<^sub>R v 0"
    by (rule cyclic_square_rep_involution[OF symH r, where e = "v 0"]) (use Sall in \<open>simp add: S_def\<close>)
  have "v 0 \<bullet> ((H + H) *v v 1) = 1"
  proof (cases "n = 2")
    case True
    hence "(H + H) *v v 1 = v 0" using last by simp
    thus ?thesis using orth[of 0 0] n by simp
  next
    case False
    have n3: "1 + 1 < n" using n False by simp
    have m: "(H + H) *v v 1 = v (1 - 1) + v (1 + 1)"
      by (rule mid) (use n3 in auto)
    have m2: "(H + H) *v v 1 = v 0 + v 2"
      using m by (simp only: diff_self_eq_0 one_add_one)
    have o: "v 0 \<bullet> v 0 = 1" "v 0 \<bullet> v 2 = 0"
      using orth[of 0 0] orth[of 0 2] n n3 by auto
    show ?thesis by (simp only: m2 inner_add_right o add_0_right)
  qed
  moreover have "v 0 \<bullet> ((H + H) *v v 1) = 4"
    using inv first orth[of 0 0] n by simp
  ultimately show False by simp
qed

section \<open>Integer coefficients\<close>

text \<open>A rigid list with integer coefficients can only send each site to one coordinate, with a
sign. Hence each row of \<open>H + H\<close> has at most two nonzero entries: integer sums of squares exist
only for rings and chains. A star with four leaves has the spectrum of a square plus an isolated
site, but admits no integer representation of any length.\<close>

definition integer_mat :: "real^'n^'r \<Rightarrow> bool" where
  "integer_mat A \<longleftrightarrow> (\<forall>i j. A $ i $ j \<in> \<int>)"

lemma integer_unit_column:
  fixes c :: "'r::finite \<Rightarrow> real"
  assumes int: "\<And>k. c k \<in> \<int>" and one: "(\<Sum>k\<in>UNIV. c k * c k) = 1"
  shows "\<exists>k. c k \<noteq> 0 \<and> (\<forall>l. l \<noteq> k \<longrightarrow> c l = 0)"
proof -
  have sq: "1 \<le> c k * c k" if "c k \<noteq> 0" for k
  proof -
    obtain m :: int where m: "c k = of_int m" using int[of k] Ints_cases by blast
    hence "m \<noteq> 0" using that by auto
    hence "1 \<le> m * m"
      by (metis abs_ge_self abs_mult_self_eq abs_zmult_eq_1 dual_order.trans int_one_le_iff_zero_less
          less_le mult_pos_pos not_less zero_less_abs_iff zero_less_mult_iff)
    hence "(1::real) \<le> of_int (m * m)" by linarith
    thus ?thesis by (simp add: m)
  qed
  have ex: "\<exists>k. c k \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "(\<Sum>k\<in>UNIV. c k * c k) = 0" by simp
    thus False using one by simp
  qed
  then obtain k where k: "c k \<noteq> 0" by blast
  have "c l = 0" if lk: "l \<noteq> k" for l
  proof (rule ccontr)
    assume nz: "c l \<noteq> 0"
    have "(\<Sum>x\<in>{k, l}. c x * c x) \<le> (\<Sum>x\<in>UNIV. c x * c x)"
      by (rule sum_mono2) auto
    moreover have "(\<Sum>x\<in>{k, l}. c x * c x) = c k * c k + c l * c l"
      using lk by simp
    ultimately show False using sq[OF k] sq[OF nz] one by simp
  qed
  thus ?thesis using k by blast
qed

lemma gram_entry: "(transpose A ** B) $ i $ j = (\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j)"
  for A B :: "real^'n^'r"
  by (simp add: matrix_matrix_mult_def transpose_def)

lemma integer_isometry_support:
  fixes A :: "real^'n^'r"
  assumes int: "integer_mat A" and iso: "transpose A ** A = mat 1"
  obtains s :: "'n \<Rightarrow> 'r" where "inj s" "\<And>j k. k \<noteq> s j \<Longrightarrow> A $ k $ j = 0" "\<And>j. A $ s j $ j \<noteq> 0"
proof -
  have col: "\<exists>k. A $ k $ j \<noteq> 0 \<and> (\<forall>l. l \<noteq> k \<longrightarrow> A $ l $ j = 0)" for j
  proof -
    have "(\<Sum>k\<in>UNIV. A $ k $ j * A $ k $ j) = 1"
      using gram_entry[of A A j j] iso by (simp add: mat_def)
    thus ?thesis
      by (intro integer_unit_column[of "\<lambda>k. A $ k $ j"]) (use int in \<open>auto simp: integer_mat_def\<close>)
  qed
  then obtain s where s: "A $ s j $ j \<noteq> 0" "\<And>l. l \<noteq> s j \<Longrightarrow> A $ l $ j = 0" for j
    by metis
  have "inj s"
  proof (rule injI)
    fix a b assume e: "s a = s b"
    show "a = b"
    proof (rule ccontr)
      assume ne: "a \<noteq> b"
      have "(\<Sum>k\<in>UNIV. A $ k $ a * A $ k $ b) = 0"
        using gram_entry[of A A a b] iso ne by (simp add: mat_def)
      moreover have "(\<Sum>k\<in>UNIV. A $ k $ a * A $ k $ b) = A $ s a $ a * A $ s a $ b"
      proof -
        have "(\<Sum>k\<in>UNIV. A $ k $ a * A $ k $ b) = (\<Sum>k\<in>{s a}. A $ k $ a * A $ k $ b)"
          by (rule sum.mono_neutral_right) (use s(2) in auto)
        thus ?thesis by simp
      qed

      ultimately show False using s(1)[of a] s(1)[of b] e by simp
    qed
  qed
  thus ?thesis using that s by blast
qed

theorem integer_representation_degree:
  fixes A B :: "real^'n^'r" and H :: "real^'n^'n"
  assumes symH: "sym_mat H" and r: "represents A B H"
    and iA: "integer_mat A" and iB: "integer_mat B"
  shows "card {j. (H + H) $ i $ j \<noteq> 0} \<le> 2"
proof -
  have h3: "transpose A ** A = mat 1" "transpose B ** B = mat 1"
    "transpose A ** B + transpose B ** A = H + H"
    using r represents_iff[OF symH] by auto
  obtain a :: "'n \<Rightarrow> 'r" where a: "inj a" "\<And>j k. k \<noteq> a j \<Longrightarrow> A $ k $ j = 0"
    using integer_isometry_support[OF iA h3(1)] by metis
  obtain b :: "'n \<Rightarrow> 'r" where b: "inj b" "\<And>j k. k \<noteq> b j \<Longrightarrow> B $ k $ j = 0"
    using integer_isometry_support[OF iB h3(2)] by metis
  have t1: "(transpose A ** B) $ i $ j \<noteq> 0 \<Longrightarrow> a i = b j" for i j
  proof (rule ccontr)
    assume nz: "(transpose A ** B) $ i $ j \<noteq> 0" and ne: "a i \<noteq> b j"
    have z: "A $ k $ i * B $ k $ j = 0" for k
      using a(2)[of k i] b(2)[of k j] ne by (cases "k = a i") auto
    have "(transpose A ** B) $ i $ j = 0"
      unfolding gram_entry by (rule sum.neutral) (use z in blast)
    thus False using nz by simp
  qed
  have t2: "(transpose B ** A) $ i $ j \<noteq> 0 \<Longrightarrow> b i = a j" for i j
  proof (rule ccontr)
    assume nz: "(transpose B ** A) $ i $ j \<noteq> 0" and ne: "b i \<noteq> a j"
    have z: "B $ k $ i * A $ k $ j = 0" for k
      using a(2)[of k j] b(2)[of k i] ne by (cases "k = b i") auto
    have "(transpose B ** A) $ i $ j = 0"
      unfolding gram_entry by (rule sum.neutral) (use z in blast)
    thus False using nz by simp
  qed
  have sub: "{j. (H + H) $ i $ j \<noteq> 0} \<subseteq> {j. b j = a i} \<union> {j. a j = b i}"
  proof
    fix j assume "j \<in> {j. (H + H) $ i $ j \<noteq> 0}"
    hence jj: "(H + H) $ i $ j \<noteq> 0" by (rule CollectD)
    have s0: "(transpose A ** B + transpose B ** A) $ i $ j \<noteq> 0"
      unfolding h3(3) by (rule jj)
    hence "(transpose A ** B) $ i $ j + (transpose B ** A) $ i $ j \<noteq> 0"
      by (metis vector_add_component)
    hence "(transpose A ** B) $ i $ j \<noteq> 0 \<or> (transpose B ** A) $ i $ j \<noteq> 0"
      by (metis add.right_neutral)
    thus "j \<in> {j. b j = a i} \<union> {j. a j = b i}"
      using t1 t2 by auto
  qed
  have c1: "card {j. b j = a i} \<le> 1"
    using b(1) by (auto simp: card_le_Suc0_iff_eq inj_def)
  have c2: "card {j. a j = b i} \<le> 1"
    using a(1) by (auto simp: card_le_Suc0_iff_eq inj_def)
  have "card {j. (H + H) $ i $ j \<noteq> 0} \<le> card ({j. b j = a i} \<union> {j. a j = b i})"
    by (rule card_mono[OF _ sub]) simp
  also have "\<dots> \<le> card {j. b j = a i} + card {j. a j = b i}"
    by (rule card_Un_le)
  finally show ?thesis using c1 c2 by simp
qed

section \<open>Paired levels give \<open>n\<close> squares\<close>

text \<open>If the diagonal \<open>d\<close> comes in pairs under an involution \<open>\<sigma>\<close>, with fixed points only at
\<open>\<plusminus>1\<close>, the rotation blocks of angle \<open>arccos d\<close> give an orthogonal matrix with symmetric part
\<open>diag d\<close>. Conjugating by an orthogonal \<open>V\<close> gives the sufficiency of the parity rule, for any
matrix presented by its orthonormal eigenbasis.\<close>

definition kron :: "'a \<Rightarrow> 'a \<Rightarrow> real" where
  "kron u v = (if u = v then 1 else 0)"

lemma kron_refl: "kron u u = 1"
  by (simp add: kron_def)

lemma kron_ne: "u \<noteq> v \<Longrightarrow> kron u v = 0"
  by (simp add: kron_def)

lemma kron_comm: "kron u v = kron v u"
proof (cases "u = v")
  case True
  thus ?thesis by simp
next
  case False
  hence "v \<noteq> u" by (rule not_sym)
  thus ?thesis using False by (simp add: kron_ne)
qed

lemma kron_sum: "(\<Sum>k\<in>UNIV. kron k u * kron k v) = kron u v"
  for u v :: "'a::finite"
proof -
  have pt: "kron k u * kron k v = (if k = u then kron u v else 0)" for k
  proof (cases "k = u")
    case True
    thus ?thesis unfolding True by (simp add: kron_refl)
  next
    case False
    thus ?thesis by (simp add: kron_ne)
  qed
  have "(\<Sum>k\<in>UNIV. kron k u * kron k v) = (\<Sum>k\<in>UNIV. if k = u then kron u v else 0)"
    by (rule sum.cong[OF refl]) (rule pt)
  also have "\<dots> = (if u \<in> UNIV then kron u v else 0)"
    by (rule sum.delta[OF finite])
  finally show ?thesis by simp
qed

definition blocks :: "('n \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> 'n) \<Rightarrow> real^'n^'n" where
  "blocks d s \<sigma> = (\<chi> i j. kron i j * d j + kron i (\<sigma> j) * s j)"

lemma blocks_entry: "blocks d s \<sigma> $ i $ j = kron i j * d j + kron i (\<sigma> j) * s j"
  by (simp only: blocks_def vec_lambda_beta)

lemma mat1_entry: "(mat 1 :: real^'n^'n) $ a $ b = kron a b"
proof (cases "a = b")
  case True
  thus ?thesis by (simp add: mat_def kron_refl)
next
  case False
  thus ?thesis by (simp add: mat_def kron_ne)
qed

lemma blocks_orthogonal:
  fixes d s :: "'n::finite \<Rightarrow> real" and \<sigma> :: "'n \<Rightarrow> 'n"
  assumes inv: "\<And>i. \<sigma> (\<sigma> i) = i"
    and dsig: "\<And>i. d (\<sigma> i) = d i"
    and ssig: "\<And>i. \<sigma> i \<noteq> i \<Longrightarrow> s (\<sigma> i) = - s i"
    and sfix: "\<And>i. \<sigma> i = i \<Longrightarrow> s i = 0"
    and norm: "\<And>i. (d i)\<^sup>2 + (s i)\<^sup>2 = 1"
  shows "transpose (blocks d s \<sigma>) ** blocks d s \<sigma> = mat 1"
proof -
  have ent: "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b =
      d a * d b * kron a b + d a * s b * kron a (\<sigma> b) + s a * d b * kron (\<sigma> a) b
      + s a * s b * kron (\<sigma> a) (\<sigma> b)" for a b
  proof -
    have "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b =
        (\<Sum>k\<in>UNIV. (kron k a * d a + kron k (\<sigma> a) * s a) * (kron k b * d b + kron k (\<sigma> b) * s b))"
      by (simp only: gram_entry blocks_entry)
    also have "\<dots> = (\<Sum>k\<in>UNIV. d a * d b * (kron k a * kron k b) + d a * s b * (kron k a * kron k (\<sigma> b))
          + s a * d b * (kron k (\<sigma> a) * kron k b) + s a * s b * (kron k (\<sigma> a) * kron k (\<sigma> b)))"
      by (rule sum.cong[OF refl]) algebra
    also have "\<dots> = d a * d b * (\<Sum>k\<in>UNIV. kron k a * kron k b)
        + d a * s b * (\<Sum>k\<in>UNIV. kron k a * kron k (\<sigma> b))
        + s a * d b * (\<Sum>k\<in>UNIV. kron k (\<sigma> a) * kron k b)
        + s a * s b * (\<Sum>k\<in>UNIV. kron k (\<sigma> a) * kron k (\<sigma> b))"
      by (simp only: sum.distrib sum_distrib_left)
    finally show ?thesis by (simp only: kron_sum)
  qed
  have case_eq: "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ a = 1" for a
  proof (cases "\<sigma> a = a")
    case True
    have z: "s a = 0" by (rule sfix[OF True])
    have n: "(d a)\<^sup>2 = 1" using norm[of a] z by simp
    show ?thesis
      unfolding ent True z kron_refl using n by (simp add: power2_eq_square)
  next
    case False
    have k1: "kron a (\<sigma> a) = 0" using False by (intro kron_ne) (rule not_sym)
    have k2: "kron (\<sigma> a) a = 0" using False by (intro kron_ne)
    show ?thesis
      unfolding ent kron_refl k1 k2 using norm[of a] by (simp add: power2_eq_square)
  qed
  have case_pair: "b = \<sigma> a \<Longrightarrow> a \<noteq> b \<Longrightarrow>
      (transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b = 0" for a b
  proof -
    assume bs: "b = \<sigma> a" and ab: "a \<noteq> b"
    have ne: "\<sigma> a \<noteq> a" using bs ab by simp
    have sb: "s b = - s a" using ssig[OF ne] bs by simp
    have db: "d b = d a" using dsig[of a] bs by simp
    have sb2: "\<sigma> b = a" using bs inv by simp
    have k0: "kron a b = 0" using ab by (rule kron_ne)
    have k1: "kron a (\<sigma> b) = 1" using sb2 kron_refl by simp
    have k2: "kron (\<sigma> a) b = 1" using bs kron_refl by simp
    have k3: "kron (\<sigma> a) (\<sigma> b) = 0"
    proof (rule kron_ne)
      show "\<sigma> a \<noteq> \<sigma> b" using ab by (metis inv)
    qed
    show "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b = 0"
      unfolding ent k0 k1 k2 k3 sb db by simp
  qed
  have case_other: "a \<noteq> b \<Longrightarrow> b \<noteq> \<sigma> a \<Longrightarrow>
      (transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b = 0" for a b
  proof -
    assume ab: "a \<noteq> b" and bs: "b \<noteq> \<sigma> a"
    have k0: "kron a b = 0" using ab by (rule kron_ne)
    have k1: "kron a (\<sigma> b) = 0"
    proof (rule kron_ne)
      show "a \<noteq> \<sigma> b" using bs inv by metis
    qed
    have k2: "kron (\<sigma> a) b = 0" using bs by (intro kron_ne) (rule not_sym)
    have k3: "kron (\<sigma> a) (\<sigma> b) = 0"
    proof (rule kron_ne)
      show "\<sigma> a \<noteq> \<sigma> b" using ab by (metis inv)
    qed
    show "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b = 0"
      unfolding ent k0 k1 k2 k3 by simp
  qed
  show ?thesis
  proof (rule iffD2[OF vec_eq_iff], rule allI, rule iffD2[OF vec_eq_iff], rule allI)
    fix a b
    show "(transpose (blocks d s \<sigma>) ** blocks d s \<sigma>) $ a $ b = mat 1 $ a $ b"
    proof (cases "a = b")
      case True
      thus ?thesis by (simp only: case_eq mat1_entry kron_refl)
    next
      case False
      hence m: "mat 1 $ a $ b = 0" using False by (simp add: mat_def)
      show ?thesis
      proof (cases "b = \<sigma> a")
        case True
        thus ?thesis using case_pair False m by simp
      next
        case nb: False
        thus ?thesis using case_other False m by simp
      qed
    qed
  qed
qed

lemma blocks_symmetric_part:
  fixes d s :: "'n::finite \<Rightarrow> real" and \<sigma> :: "'n \<Rightarrow> 'n"
  assumes inv: "\<And>i. \<sigma> (\<sigma> i) = i"
    and ssig: "\<And>i. \<sigma> i \<noteq> i \<Longrightarrow> s (\<sigma> i) = - s i"
    and sfix: "\<And>i. \<sigma> i = i \<Longrightarrow> s i = 0"
  shows "blocks d s \<sigma> + transpose (blocks d s \<sigma>) =
    (\<chi> i j. kron i j * d j) + (\<chi> i j. kron i j * d j)"
proof (rule iffD2[OF vec_eq_iff], rule allI, rule iffD2[OF vec_eq_iff], rule allI)
  fix i j
  have sum0: "kron i (\<sigma> j) * s j + kron j (\<sigma> i) * s i = 0"
  proof (cases "i = \<sigma> j")
    case True
    have ji: "j = \<sigma> i" using True inv by simp
    show ?thesis
    proof (cases "\<sigma> j = j")
      case fx: True
      have "s j = 0" by (rule sfix[OF fx])
      moreover have "s i = 0" using sfix[of i] fx True by simp
      ultimately show ?thesis by simp
    next
      case nfx: False
      have sj: "s (\<sigma> j) = - s j" by (rule ssig[OF nfx])
      have si: "s i = - s j" using sj True by simp
      show ?thesis
        unfolding True[symmetric] ji[symmetric] si by (simp add: kron_refl)
    qed
  next
    case False
    have k1: "kron i (\<sigma> j) = 0" using False by (rule kron_ne)
    have k2: "kron j (\<sigma> i) = 0"
    proof (rule kron_ne)
      show "j \<noteq> \<sigma> i" using False inv by metis
    qed
    show ?thesis unfolding k1 k2 by simp
  qed
  have cm: "kron j i * d i = kron i j * d j"
  proof (cases "i = j")
    case True
    thus ?thesis by simp
  next
    case False
    hence "j \<noteq> i" by (rule not_sym)
    thus ?thesis using False by (simp add: kron_ne)
  qed
  have lhs: "(blocks d s \<sigma> + transpose (blocks d s \<sigma>)) $ i $ j =
      (kron i j * d j + kron i (\<sigma> j) * s j) + (kron j i * d i + kron j (\<sigma> i) * s i)"
    by (simp only: vector_add_component transpose_def vec_lambda_beta blocks_entry)
  have rhs: "((\<chi> i j. kron i j * d j) + (\<chi> i j. kron i j * d j) :: real^'n^'n) $ i $ j =
      kron i j * d j + kron i j * d j"
    by (simp only: vector_add_component vec_lambda_beta)
  show "(blocks d s \<sigma> + transpose (blocks d s \<sigma>)) $ i $ j =
      ((\<chi> i j. kron i j * d j) + (\<chi> i j. kron i j * d j)) $ i $ j"
    unfolding lhs rhs using sum0 cm by linarith
qed

end
