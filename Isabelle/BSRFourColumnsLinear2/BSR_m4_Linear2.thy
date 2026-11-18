(*  Title:      BSR_m4_Linear2.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   More linear-algebra pieces of the paper "Boundary inertia and sums of squares of biquadratic forms" (C. Marín,
   2026, in preparation).

   (1) line_decomposable: Lemma "line" (the covector <e,T_c y> factors as beta(c) times a fixed covector).
   (2) rank_one_sum_minor: the two-member step "two rank-one maps with independent image lines and independent
       covector lines have a rank-two sum" used in Lemmas "Small tableaux" and "low-index-four".
   (3) common_line_step: key step of Lemma "Common-line commutators".
   (4) pencil_core: last step of Lemma "pencil" (homogeneous binary form of positive degree has a nontrivial zero,
       by the fundamental theorem of algebra).
   Not formalized: the induction on dim S (simultaneous triangularization), the quotient/restriction bookkeeping,
   and the passage from a rank-one linear space to a common image line / kernel hyperplane (only the two-member
   step is proved). *)
theory BSR_m4_Linear2
  imports Complex_Main "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

section \<open>(1) Lemma line\<close>

text \<open>E is an abstract space ('e) over a field ('k) with scalar action sm. J is a bilinear form, linear in the
  first argument; T c is a map 'a -> 'e. Flatness identity (F): J (T b x) (T c y) = J (T c x) (T b y).\<close>

theorem line_decomposable:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> 'k::field"
    and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e" and beta :: "'c \<Rightarrow> 'k"
  assumes Jsm: "\<And>a u w. J (sm a u) w = a * J u w"
    and sm1: "\<And>u. sm 1 u = u"
    and flat: "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and Tx: "\<And>c. T c x = sm (beta c) e"
    and bd: "beta d = 1"
  shows "J e (T c y) = beta c * J e (T d y)"
proof -
  have h1: "J (T d x) (T c y) = J (T c x) (T d y)" by (rule flat)
  have Tdx: "T d x = e" using Tx[of d] bd sm1 by simp
  have "J e (T c y) = J (T c x) (T d y)" using h1 unfolding Tdx .
  also have "\<dots> = J (sm (beta c) e) (T d y)" by (simp only: Tx)
  also have "\<dots> = beta c * J e (T d y)" by (rule Jsm)
  finally show ?thesis .
qed

text \<open>Decomposability is the statement that the covector (c,y) -> J e (T c y) is the product beta(c) * phi(y) with
  phi(y) = J e (T d y); it is nonzero as soon as phi is.\<close>

corollary line_decomposable_nonzero:
  fixes J :: "'e::ab_group_add \<Rightarrow> 'e \<Rightarrow> 'k::field"
    and sm :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and T :: "'c \<Rightarrow> 'a \<Rightarrow> 'e" and beta :: "'c \<Rightarrow> 'k"
  assumes "\<And>a u w. J (sm a u) w = a * J u w" "\<And>u. sm 1 u = u"
    and "\<And>b c x y. J (T b x) (T c y) = J (T c x) (T b y)"
    and "\<And>c. T c x = sm (beta c) e" "beta d = 1" and "J e (T d y0) \<noteq> 0"
  shows "\<exists>phi. (\<forall>c y. J e (T c y) = beta c * phi y) \<and> phi y0 \<noteq> 0"
proof -
  have key: "\<And>c y. J e (T c y) = beta c * J e (T d y)"
    by (rule line_decomposable[where x=x and e=e and d=d]) (use assms in auto)
  show ?thesis
  proof (rule exI[of _ "\<lambda>y. J e (T d y)"], rule conjI)
    show "\<forall>c y. J e (T c y) = beta c * J e (T d y)" using key by blast
    show "J e (T d y0) \<noteq> 0" by (rule assms(6))
  qed
qed

section \<open>(2) Two rank-one matrices with independent lines have a rank-two sum\<close>

text \<open>An n x k matrix is a function M i l (i < n, l < k); rank <= 1 iff all 2 x 2 minors vanish. The rank-one matrix
  u (x) a is (\<lambda>i l. u i * a l). Independence of u, v: some 2 x 2 minor of (u v) is nonzero.\<close>

definition minors_zero :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "minors_zero M n k = (\<forall>i<n. \<forall>j<n. \<forall>l<k. \<forall>m<k. M i l * M j m = M i m * M j l)"

lemma rank_one_minors_zero:
  "minors_zero (\<lambda>i l. (u i :: 'a::comm_ring) * a l) n k"
  unfolding minors_zero_def by (simp add: algebra_simps)

lemma minor_sum_rank_one:
  fixes u v :: "nat \<Rightarrow> 'a::comm_ring"
  shows "(u i * a l + v i * b l) * (u j * a m + v j * b m) - (u i * a m + v i * b m) * (u j * a l + v j * b l)
       = (u i * v j - u j * v i) * (a l * b m - a m * b l)"
  by (simp add: algebra_simps)

theorem rank_one_sum_minor:
  fixes u v :: "nat \<Rightarrow> 'a::idom" and a b :: "nat \<Rightarrow> 'a"
  assumes indu: "\<exists>i<n. \<exists>j<n. u i * v j \<noteq> u j * v i"
    and indb: "\<exists>l<k. \<exists>m<k. a l * b m \<noteq> a m * b l"
  shows "\<not> minors_zero (\<lambda>i l. u i * a l + v i * b l) n k"
proof
  assume mz: "minors_zero (\<lambda>i l. u i * a l + v i * b l) n k"
  obtain i j where ij: "i < n" "j < n" "u i * v j \<noteq> u j * v i" using indu by blast
  obtain l m where lm: "l < k" "m < k" "a l * b m \<noteq> a m * b l" using indb by blast
  have z: "(u i * a l + v i * b l) * (u j * a m + v j * b m) = (u i * a m + v i * b m) * (u j * a l + v j * b l)"
    using mz ij lm unfolding minors_zero_def by blast
  have mm: "(u i * a l + v i * b l) * (u j * a m + v j * b m) - (u i * a m + v i * b m) * (u j * a l + v j * b l)
       = (u i * v j - u j * v i) * (a l * b m - a m * b l)"
    by (rule minor_sum_rank_one)
  have "(u i * v j - u j * v i) * (a l * b m - a m * b l) = 0"
    by (rule trans[OF sym[OF mm]]) (simp add: z)
  then show False using ij(3) lm(3) by simp
qed

corollary rank_one_pair_not_in_rank_le_one_space:
  fixes u v :: "nat \<Rightarrow> 'a::idom" and a b :: "nat \<Rightarrow> 'a"
  assumes "\<exists>i<n. \<exists>j<n. u i * v j \<noteq> u j * v i" "\<exists>l<k. \<exists>m<k. a l * b m \<noteq> a m * b l"
    and add: "\<And>M N. M \<in> S \<Longrightarrow> N \<in> S \<Longrightarrow> (\<lambda>i l. M i l + N i l) \<in> S"
    and "(\<lambda>i l. u i * a l) \<in> S" "(\<lambda>i l. v i * b l) \<in> S"
    and "\<And>M. M \<in> S \<Longrightarrow> minors_zero M n k"
  shows False
proof -
  have "(\<lambda>i l. u i * a l + v i * b l) \<in> S" using add[OF assms(4,5)] by simp
  then have "minors_zero (\<lambda>i l. u i * a l + v i * b l) n k" using assms(6) by blast
  then show False using rank_one_sum_minor[OF assms(1,2)] by blast
qed

section \<open>(3) The key step of Lemma common-line\<close>

text \<open>V is an abstract vector space ('v) over a field ('k); X, Y, Z additive and homogeneous maps. K is the line
  spanned by k; the commutator condition [X,Y](S) in K is: for all w, X (Y w) - Y (X w) = sm c k for some c.\<close>

theorem common_line_step_kernel:
  fixes X Y :: "'v::ab_group_add \<Rightarrow> 'v" and sm :: "'k::field \<Rightarrow> 'v \<Rightarrow> 'v" and k :: 'v
  assumes addX: "\<And>u w. X (u + w) = X u + X w"
    and smX: "\<And>c u. X (sm c u) = sm c (X u)"
    and sm0: "\<And>u. sm 0 u = 0"
    and sm1: "\<And>u. sm 1 u = u"
    and smmul: "\<And>c d u. sm c (sm d u) = sm (c * d) u"
    and Y0: "Y 0 = 0"
    and comm: "\<And>w. \<exists>c. X (Y w) - Y (X w) = sm c k"
    and v: "X v = 0" and nz: "X (Y v) \<noteq> 0"
  shows "\<exists>m. X m = k"
proof -
  have X0: "X 0 = 0" using addX[of 0 0] by simp
  obtain c where c: "X (Y v) - Y (X v) = sm c k" using comm by blast
  have e: "X (Y v) = sm c k" using c v Y0 by simp
  have c0: "c \<noteq> 0"
  proof
    assume "c = 0"
    then show False using e nz sm0 by simp
  qed
  have "sm (inverse c) (sm c k) = k" using smmul[of "inverse c" c k] c0 sm1 by simp
  then have "k = sm (inverse c) (X (Y v))" using e by simp
  also have "\<dots> = X (sm (inverse c) (Y v))" using smX by simp
  finally show ?thesis by (intro exI[of _ "sm (inverse c) (Y v)"]) simp
qed

theorem common_line_step_image:
  fixes X Z :: "'v::ab_group_add \<Rightarrow> 'v" and sm :: "'k::field \<Rightarrow> 'v \<Rightarrow> 'v" and k :: 'v
  assumes addX: "\<And>u w. X (u + w) = X u + X w"
    and subX: "\<And>u w. X (u - w) = X u - X w"
    and smX: "\<And>c u. X (sm c u) = sm c (X u)"
    and comm: "\<And>w. \<exists>c. X (Z w) - Z (X w) = sm c k"
    and kim: "X m = k"
  shows "Z (X w) \<in> range X"
proof -
  obtain c where c: "X (Z w) - Z (X w) = sm c k" using comm by blast
  have "Z (X w) = X (Z w) - (X (Z w) - Z (X w))" by simp
  also have "\<dots> = X (Z w) - sm c k" using c by simp
  also have "\<dots> = X (Z w - sm c m)" using subX smX kim by simp
  finally show ?thesis by (rule range_eqI)
qed

section \<open>(4) The core of Lemma pencil\<close>

text \<open>The determinant of F^* G_lambda restricted to B/ker F is a binary form P(s,t) = sum_{i<=q} a_i s^i t^(q-i)
  of degree q > 0. Over the complex numbers it has a zero other than (0,0): either a_q = 0 (zero at (1,0), "at
  infinity") or p(lambda) = P(lambda,1) has degree q > 0 and a root (fundamental theorem of algebra).\<close>

definition binform :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "binform a q s t = (\<Sum>i\<le>q. a i * s ^ i * t ^ (q - i))"

lemma binform_inf: "q > 0 \<Longrightarrow> binform a q 1 0 = a q"
proof -
  assume q: "q > 0"
  have "binform a q 1 0 = (\<Sum>i\<le>q. if i = q then a i else 0)"
    unfolding binform_def
  proof (rule sum.cong[OF refl])
    fix i assume i: "i \<in> {..q}"
    show "a i * 1 ^ i * 0 ^ (q - i) = (if i = q then a i else 0)"
    proof (cases "i = q")
      case True then show ?thesis by simp
    next
      case False
      then have "q - i \<noteq> 0" using i by auto
      then show ?thesis using False by (simp add: power_0_left)
    qed
  qed
  also have "\<dots> = a q" by simp
  finally show ?thesis .
qed

lemma binform_dehomog:
  "binform a q s 1 = poly (\<Sum>i\<le>q. monom (a i) i) s"
  unfolding binform_def by (simp add: poly_sum poly_monom)

theorem pencil_core:
  assumes q: "q > 0"
  shows "\<exists>s t. (s \<noteq> 0 \<or> t \<noteq> 0) \<and> binform a q s t = 0"
proof (cases "a q = 0")
  case True
  then show ?thesis using binform_inf[OF q] by (intro exI[of _ 1] exI[of _ 0]) simp
next
  case False
  define p where "p = (\<Sum>i\<le>q. monom (a i) i)"
  have cq: "coeff p q = a q" unfolding p_def by (simp add: coeff_sum coeff_monom)
  have "q \<le> degree p" by (rule le_degree) (simp add: cq False)
  then have "degree p > 0" using q by simp
  then have "\<not> constant (poly p)" using constant_degree[of p] by simp
  then obtain z where "poly p z = 0" using fundamental_theorem_of_algebra by blast
  then show ?thesis using binform_dehomog[of a q z] unfolding p_def by (intro exI[of _ z] exI[of _ 1]) simp
qed

end
