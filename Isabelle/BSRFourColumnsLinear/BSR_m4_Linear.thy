(*  Title:      BSR_m4_Linear.thy
    Author:     Carles Marín
    Copyright:  2026
    License:    BSD

   Linear-algebra pieces of the paper "Boundary inertia and sums of squares of biquadratic forms" (C. Marín, 2026,
   in preparation).

   (1) rank5_polar_kernel: Lemma "Rank five in 4x4", eq. (9): trace(X) I + X^T = 0 forces X = 0.
   (2) singular_2x2_space: Lemma "Small tableaux": an additive set of singular 2x2 matrices has a common kernel
       vector or a common image line (over any field; only closure under addition is used).
   (3) symmetric_trilinear_polarization: a fully symmetric trilinear form with zero diagonal vanishes (Theorem
       "Full-support rank-six exclusion" and Lemma "Invariant extension of an isotropic plane").
   Not formalized: Lemma "Common-line commutators" (simultaneous triangularization). *)
theory BSR_m4_Linear
  imports Complex_Main
begin

section \<open>(1) The polar kernel of Lemma rank5\<close>

text \<open>A 4 x 4 matrix is a function X i j (indices below 4). The identity (9) is X -> (tr(X) I + X^T)/2; its kernel
  is trivial.\<close>

lemma sum4_nat: "(\<Sum>k<(4::nat). f k) = f 0 + f 1 + f 2 + f 3"
  by (simp add: eval_nat_numeral lessThan_Suc add_ac)

theorem rank5_polar_kernel:
  fixes X :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0"
  assumes zero: "\<And>i j. i < 4 \<Longrightarrow> j < 4 \<Longrightarrow> (\<Sum>k<4. X k k) * (if i = j then 1 else 0) + X j i = 0"
    and ij: "i < 4" "j < 4"
  shows "X i j = 0"
proof -
  define t where "t = (\<Sum>k<4. X k k)"
  have diag: "X k k = - t" if "k < 4" for k
  proof -
    have h: "t + X k k = 0" using zero[of k k] that unfolding t_def by simp
    from h have "- t = X k k" by (rule minus_unique)
    then show ?thesis by (rule sym)
  qed
  have "t = X 0 0 + X 1 1 + X 2 2 + X 3 3" unfolding t_def by (simp add: sum4_nat)
  also have "\<dots> = - t - t - t - t" using diag[of 0] diag[of 1] diag[of 2] diag[of 3] by simp
  finally have "5 * t = 0" by (simp add: algebra_simps)
  then have t0: "t = 0" by simp
  show ?thesis using zero[of j i] ij t0 unfolding t_def[symmetric] by simp
qed

section \<open>(2) A linear space of singular 2 x 2 matrices\<close>

text \<open>A matrix [[a,b],[c,d]] is the tuple (a,b,c,d). Common kernel: a vector (v1,v2) <> 0 killed by every member.
  Common image: a line spanned by (u1,u2) <> 0 containing both columns (a,c) and (b,d) of every member. The proof
  uses the polar form of the determinant, so only closure under addition is needed (hence any additive set, in
  particular a linear subspace, over any field).\<close>

definition common_kernel :: "('a::field \<times> 'a \<times> 'a \<times> 'a) set \<Rightarrow> bool" where
  "common_kernel S = (\<exists>v1 v2. (v1 \<noteq> 0 \<or> v2 \<noteq> 0) \<and>
     (\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0))"

definition common_image :: "('a::field \<times> 'a \<times> 'a \<times> 'a) set \<Rightarrow> bool" where
  "common_image S = (\<exists>u1 u2. (u1 \<noteq> 0 \<or> u2 \<noteq> 0) \<and>
     (\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b))"

text \<open>Normal case: the set contains a member with a <> 0 (the member is then rank one).\<close>

lemma singular_aux:
  fixes S :: "('a::field \<times> 'a \<times> 'a \<times> 'a) set"
  assumes sing: "\<And>a b c d. (a,b,c,d) \<in> S \<Longrightarrow> a * d = b * c"
    and add: "\<And>a b c d a' b' c' d'. (a,b,c,d) \<in> S \<Longrightarrow> (a',b',c',d') \<in> S \<Longrightarrow> (a+a',b+b',c+c',d+d') \<in> S"
    and M0: "(a0,b0,c0,d0) \<in> S" and a0: "a0 \<noteq> 0"
  shows "common_kernel S \<or> common_image S"
proof -
  have d0: "a0 * d0 = b0 * c0" using sing[OF M0] .
  \<comment> \<open>F1: the polar form of det against M0 vanishes.\<close>
  have F1: "a0 * (a0 * s - c0 * q) = b0 * (a0 * r - c0 * p)" if N: "(p,q,r,s) \<in> S" for p q r s
  proof -
    have h: "(a0 + p) * (d0 + s) = (b0 + q) * (c0 + r)" using sing[OF add[OF M0 N]] by simp
    have e: "a0 * s + p * d0 = b0 * r + q * c0"
      using h sing[OF N] d0 by (simp add: algebra_simps)
    have "a0 * (a0 * s + p * d0) = a0 * (b0 * r + q * c0)" using e by simp
    then show ?thesis using d0 by (simp add: algebra_simps) (metis d0 mult.assoc mult.commute)
  qed
  define k where "k p q r s = q * a0 - b0 * p" for p q r s :: 'a
  define y where "y p q r s = r * a0 - c0 * p" for p q r s :: 'a
  have F2: "k p q r s * y p q r s = 0" if N: "(p,q,r,s) \<in> S" for p q r s
  proof -
    have "k p q r s * y p q r s = a0^2 * (q * r - p * s) + p * (a0^2 * s - a0 * c0 * q - b0 * (a0 * r - c0 * p))"
      unfolding k_def y_def by (simp add: power2_eq_square algebra_simps)
    moreover have "q * r - p * s = 0" using sing[OF N] by simp
    moreover have "a0^2 * s - a0 * c0 * q - b0 * (a0 * r - c0 * p) = 0" using F1[OF N]
      by (simp add: power2_eq_square algebra_simps)
    ultimately show ?thesis by simp
  qed
  have F3: "k p q r s * y p' q' r' s' + k p' q' r' s' * y p q r s = 0"
    if N: "(p,q,r,s) \<in> S" and N': "(p',q',r',s') \<in> S" for p q r s p' q' r' s'
  proof -
    have h: "(p + p') * (s + s') = (q + q') * (r + r')" using sing[OF add[OF N N']] by simp
    have e: "p * s' + p' * s = q * r' + q' * r" using h sing[OF N] sing[OF N'] by (simp add: algebra_simps)
    have "k p q r s * y p' q' r' s' + k p' q' r' s' * y p q r s =
       a0^2 * (q * r' + q' * r - p * s' - p' * s)
       + p * (a0^2 * s' - a0 * c0 * q' - b0 * (a0 * r' - c0 * p'))
       + p' * (a0^2 * s - a0 * c0 * q - b0 * (a0 * r - c0 * p))"
      unfolding k_def y_def by (simp add: power2_eq_square algebra_simps)
    moreover have "a0^2 * s' - a0 * c0 * q' - b0 * (a0 * r' - c0 * p') = 0" using F1[OF N']
      by (simp add: power2_eq_square algebra_simps)
    moreover have "a0^2 * s - a0 * c0 * q - b0 * (a0 * r - c0 * p) = 0" using F1[OF N]
      by (simp add: power2_eq_square algebra_simps)
    moreover have "q * r' + q' * r - p * s' - p' * s = 0"
    proof -
      have "q * r' + q' * r - p * s' - p' * s = (q * r' + q' * r) - (p * s' + p' * s)" by (simp add: algebra_simps)
      then show ?thesis using e by simp
    qed
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule ccontr)
    assume neg: "\<not> (common_kernel S \<or> common_image S)"
    \<comment> \<open>not a common kernel: the vector (b0,-a0) is moved by some member\<close>
    have "\<not> common_kernel S" "\<not> common_image S" using neg by simp_all
    have hk: "\<forall>v1 v2. (v1 \<noteq> 0 \<or> v2 \<noteq> 0) \<longrightarrow>
        (\<exists>a b c d. (a,b,c,d) \<in> S \<and> \<not> (a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0))"
    proof (rule ccontr)
      assume h: "\<not> ?thesis"
      then obtain v1 v2 where "v1 \<noteq> 0 \<or> v2 \<noteq> 0"
        "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0" by blast
      then have "common_kernel S" unfolding common_kernel_def by blast
      with \<open>\<not> common_kernel S\<close> show False by blast
    qed
    have hi: "\<forall>u1 u2. (u1 \<noteq> 0 \<or> u2 \<noteq> 0) \<longrightarrow>
        (\<exists>a b c d. (a,b,c,d) \<in> S \<and> \<not> (u1 * c = u2 * a \<and> u1 * d = u2 * b))"
    proof (rule ccontr)
      assume h: "\<not> ?thesis"
      then obtain u1 u2 where "u1 \<noteq> 0 \<or> u2 \<noteq> 0"
        "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b" by blast
      then have "common_image S" unfolding common_image_def by blast
      with \<open>\<not> common_image S\<close> show False by blast
    qed
    from hk[rule_format, of b0 "- a0"] a0
    obtain p q r s where N: "(p,q,r,s) \<in> S" and Nk: "\<not> (p * b0 + q * (- a0) = 0 \<and> r * b0 + s * (- a0) = 0)"
      by auto
    from hi[rule_format, of a0 c0] a0
    obtain p' q' r' s' where N': "(p',q',r',s') \<in> S" and Ni: "\<not> (a0 * r' = c0 * p' \<and> a0 * s' = c0 * q')"
      by auto
    have kN: "k p q r s \<noteq> 0"
    proof
      assume k0: "k p q r s = 0"
      then have c1: "p * b0 + q * (- a0) = 0" unfolding k_def by (simp add: algebra_simps)
      have "a0 * (r * b0 + s * (- a0)) = - c0 * k p q r s" using F1[OF N] unfolding k_def
        by (simp add: algebra_simps)
      then have "r * b0 + s * (- a0) = 0" using k0 a0 by simp
      then show False using Nk c1 by simp
    qed
    have yN': "y p' q' r' s' \<noteq> 0"
    proof
      assume y0: "y p' q' r' s' = 0"
      then have c1: "a0 * r' = c0 * p'" unfolding y_def by (simp add: algebra_simps)
      have "a0 * (a0 * s' - c0 * q') = 0" using F1[OF N'] c1 by simp
      then have "a0 * s' = c0 * q'" using a0 by simp
      then show False using Ni c1 by simp
    qed
    have yN: "y p q r s = 0" using F2[OF N] kN by simp
    have "k p q r s * y p' q' r' s' = 0" using F3[OF N N'] yN by simp
    then show False using kN yN' by simp
  qed
qed

theorem singular_2x2_space:
  fixes S :: "('a::field \<times> 'a \<times> 'a \<times> 'a) set"
  assumes sing: "\<And>a b c d. (a,b,c,d) \<in> S \<Longrightarrow> a * d = b * c"
    and add: "\<And>a b c d a' b' c' d'. (a,b,c,d) \<in> S \<Longrightarrow> (a',b',c',d') \<in> S \<Longrightarrow> (a+a',b+b',c+c',d+d') \<in> S"
  shows "common_kernel S \<or> common_image S"
proof (cases "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0")
  case True
  then have "common_kernel S" unfolding common_kernel_def by (intro exI[of _ 1] exI[of _ 0]) auto
  then show ?thesis by simp
next
  case False
  then obtain a0 b0 c0 d0 where M0: "(a0,b0,c0,d0) \<in> S" and nz: "\<not> (a0 = 0 \<and> b0 = 0 \<and> c0 = 0 \<and> d0 = 0)"
    by blast
  show ?thesis
  proof (cases "a0 = 0")
    case False
    show ?thesis using singular_aux[OF sing add M0 False] .
  next
    case a00: True
    show ?thesis
    proof (cases "b0 = 0")
      case False
      \<comment> \<open>swap the columns\<close>
      define S1 where "S1 = {x. \<exists>a b c d. (a,b,c,d) \<in> S \<and> x = (b,a,d,c)}"
      have "common_kernel S1 \<or> common_image S1"
      proof (rule singular_aux[of S1 b0 a0 d0 c0])
        fix a b c d assume "(a,b,c,d) \<in> S1"
        then show "a * d = b * c" unfolding S1_def using sing by (auto simp: mult.commute)
      next
        fix a b c d a' b' c' d' assume "(a,b,c,d) \<in> S1" "(a',b',c',d') \<in> S1"
        then show "(a+a',b+b',c+c',d+d') \<in> S1" unfolding S1_def using add by fastforce
      next
        show "(b0,a0,d0,c0) \<in> S1" unfolding S1_def using M0 by blast
      next
        show "b0 \<noteq> 0" using False .
      qed
      then show ?thesis
      proof
        assume "common_kernel S1"
        then obtain v1 v2 where v: "v1 \<noteq> 0 \<or> v2 \<noteq> 0"
          "\<forall>a b c d. (a,b,c,d) \<in> S1 \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0"
          unfolding common_kernel_def by blast
        have "common_kernel S" unfolding common_kernel_def
        proof (rule exI[of _ v2], rule exI[of _ v1], rule conjI)
          show "v2 \<noteq> 0 \<or> v1 \<noteq> 0" using v(1) by blast
          show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a * v2 + b * v1 = 0 \<and> c * v2 + d * v1 = 0"
          proof (intro allI impI)
            fix a b c d assume "(a,b,c,d) \<in> S"
            then have "(b,a,d,c) \<in> S1" unfolding S1_def by blast
            from v(2)[rule_format, OF this] show "a * v2 + b * v1 = 0 \<and> c * v2 + d * v1 = 0"
              by (simp add: algebra_simps)
          qed
        qed
        then show ?thesis by simp
      next
        assume "common_image S1"
        then obtain u1 u2 where u: "u1 \<noteq> 0 \<or> u2 \<noteq> 0"
          "\<forall>a b c d. (a,b,c,d) \<in> S1 \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b"
          unfolding common_image_def by blast
        have "common_image S" unfolding common_image_def
        proof (rule exI[of _ u1], rule exI[of _ u2], rule conjI)
          show "u1 \<noteq> 0 \<or> u2 \<noteq> 0" using u(1) .
          show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b"
          proof (intro allI impI)
            fix a b c d assume "(a,b,c,d) \<in> S"
            then have "(b,a,d,c) \<in> S1" unfolding S1_def by blast
            from u(2)[rule_format, OF this] show "u1 * c = u2 * a \<and> u1 * d = u2 * b" by simp
          qed
        qed
        then show ?thesis by simp
      qed
    next
      case b00: True
      show ?thesis
      proof (cases "c0 = 0")
        case False
        \<comment> \<open>swap the rows\<close>
        define S2 where "S2 = {x. \<exists>a b c d. (a,b,c,d) \<in> S \<and> x = (c,d,a,b)}"
        have "common_kernel S2 \<or> common_image S2"
        proof (rule singular_aux[of S2 c0 d0 a0 b0])
          fix a b c d assume "(a,b,c,d) \<in> S2"
          then show "a * d = b * c" unfolding S2_def using sing by (auto simp: mult.commute dest: sing)
        next
          fix a b c d a' b' c' d' assume "(a,b,c,d) \<in> S2" "(a',b',c',d') \<in> S2"
          then show "(a+a',b+b',c+c',d+d') \<in> S2" unfolding S2_def using add by fastforce
        next
          show "(c0,d0,a0,b0) \<in> S2" unfolding S2_def using M0 by blast
        next
          show "c0 \<noteq> 0" using False .
        qed
        then show ?thesis
        proof
          assume "common_kernel S2"
          then obtain v1 v2 where v: "v1 \<noteq> 0 \<or> v2 \<noteq> 0"
            "\<forall>a b c d. (a,b,c,d) \<in> S2 \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0"
            unfolding common_kernel_def by blast
          have "common_kernel S" unfolding common_kernel_def
          proof (rule exI[of _ v1], rule exI[of _ v2], rule conjI)
            show "v1 \<noteq> 0 \<or> v2 \<noteq> 0" using v(1) .
            show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0"
            proof (intro allI impI)
              fix a b c d assume "(a,b,c,d) \<in> S"
              then have "(c,d,a,b) \<in> S2" unfolding S2_def by blast
              from v(2)[rule_format, OF this] show "a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0" by simp
            qed
          qed
          then show ?thesis by simp
        next
          assume "common_image S2"
          then obtain u1 u2 where u: "u1 \<noteq> 0 \<or> u2 \<noteq> 0"
            "\<forall>a b c d. (a,b,c,d) \<in> S2 \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b"
            unfolding common_image_def by blast
          have "common_image S" unfolding common_image_def
          proof (rule exI[of _ u2], rule exI[of _ u1], rule conjI)
            show "u2 \<noteq> 0 \<or> u1 \<noteq> 0" using u(1) by blast
            show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> u2 * c = u1 * a \<and> u2 * d = u1 * b"
            proof (intro allI impI)
              fix a b c d assume "(a,b,c,d) \<in> S"
              then have "(c,d,a,b) \<in> S2" unfolding S2_def by blast
              from u(2)[rule_format, OF this] show "u2 * c = u1 * a \<and> u2 * d = u1 * b" by simp
            qed
          qed
          then show ?thesis by simp
        qed
      next
        case c00: True
        then have d0nz: "d0 \<noteq> 0" using nz a00 b00 by blast
        \<comment> \<open>swap both\<close>
        define S3 where "S3 = {x. \<exists>a b c d. (a,b,c,d) \<in> S \<and> x = (d,c,b,a)}"
        have "common_kernel S3 \<or> common_image S3"
        proof (rule singular_aux[of S3 d0 c0 b0 a0])
          fix a b c d assume "(a,b,c,d) \<in> S3"
          then show "a * d = b * c" unfolding S3_def using sing by (auto simp: mult.commute dest: sing)
        next
          fix a b c d a' b' c' d' assume "(a,b,c,d) \<in> S3" "(a',b',c',d') \<in> S3"
          then show "(a+a',b+b',c+c',d+d') \<in> S3" unfolding S3_def using add by fastforce
        next
          show "(d0,c0,b0,a0) \<in> S3" unfolding S3_def using M0 by blast
        next
          show "d0 \<noteq> 0" using d0nz .
        qed
        then show ?thesis
        proof
          assume "common_kernel S3"
          then obtain v1 v2 where v: "v1 \<noteq> 0 \<or> v2 \<noteq> 0"
            "\<forall>a b c d. (a,b,c,d) \<in> S3 \<longrightarrow> a * v1 + b * v2 = 0 \<and> c * v1 + d * v2 = 0"
            unfolding common_kernel_def by blast
          have "common_kernel S" unfolding common_kernel_def
          proof (rule exI[of _ v2], rule exI[of _ v1], rule conjI)
            show "v2 \<noteq> 0 \<or> v1 \<noteq> 0" using v(1) by blast
            show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> a * v2 + b * v1 = 0 \<and> c * v2 + d * v1 = 0"
            proof (intro allI impI)
              fix a b c d assume "(a,b,c,d) \<in> S"
              then have "(d,c,b,a) \<in> S3" unfolding S3_def by blast
              from v(2)[rule_format, OF this] show "a * v2 + b * v1 = 0 \<and> c * v2 + d * v1 = 0"
                by (simp add: algebra_simps)
            qed
          qed
          then show ?thesis by simp
        next
          assume "common_image S3"
          then obtain u1 u2 where u: "u1 \<noteq> 0 \<or> u2 \<noteq> 0"
            "\<forall>a b c d. (a,b,c,d) \<in> S3 \<longrightarrow> u1 * c = u2 * a \<and> u1 * d = u2 * b"
            unfolding common_image_def by blast
          have "common_image S" unfolding common_image_def
          proof (rule exI[of _ u2], rule exI[of _ u1], rule conjI)
            show "u2 \<noteq> 0 \<or> u1 \<noteq> 0" using u(1) by blast
            show "\<forall>a b c d. (a,b,c,d) \<in> S \<longrightarrow> u2 * c = u1 * a \<and> u2 * d = u1 * b"
            proof (intro allI impI)
              fix a b c d assume "(a,b,c,d) \<in> S"
              then have "(d,c,b,a) \<in> S3" unfolding S3_def by blast
              from u(2)[rule_format, OF this] show "u2 * c = u1 * a \<and> u2 * d = u1 * b" by simp
            qed
          qed
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

text \<open>The complex case used in the paper (a linear space is in particular additive).\<close>
corollary singular_2x2_space_complex:
  fixes S :: "(complex \<times> complex \<times> complex \<times> complex) set"
  assumes "\<And>a b c d. (a,b,c,d) \<in> S \<Longrightarrow> a * d = b * c"
    and "\<And>a b c d a' b' c' d'. (a,b,c,d) \<in> S \<Longrightarrow> (a',b',c',d') \<in> S \<Longrightarrow> (a+a',b+b',c+c',d+d') \<in> S"
  shows "common_kernel S \<or> common_image S"
  using singular_2x2_space[OF assms] .

section \<open>(3) Polarization of a symmetric trilinear form\<close>

text \<open>Abstract version: B is additive in the first argument and symmetric under the transpositions of the first two
  and the last two arguments (hence fully symmetric); the target is a field of characteristic 0, e.g. the real or the
  complex numbers. The identity is 6 B(x,y,z) = D(x+y+z) - D(x+y) - D(x+z) - D(y+z) + D(x) + D(y) + D(z) with
  D(x) = B(x,x,x).\<close>

theorem symmetric_trilinear_polarization:
  fixes B :: "'v::ab_group_add \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'k::field_char_0"
  assumes add1: "\<And>x x' y z. B (x + x') y z = B x y z + B x' y z"
    and s12: "\<And>x y z. B x y z = B y x z"
    and s23: "\<And>x y z. B x y z = B x z y"
    and diag: "\<And>x. B x x x = 0"
  shows "B x y z = 0"
proof -
  have add2: "\<And>x y y' z. B x (y + y') z = B x y z + B x y' z" using add1 s12 by metis
  have add3: "\<And>x y z z'. B x y (z + z') = B x y z + B x y z'" using add2 s23 by metis
  have cube: "B (u+v) (u+v) (u+v) = B u u u + B v v v + 3 * B u u v + 3 * B u v v" for u v
  proof -
    have e1: "B u v u = B u u v" using s23 by metis
    have e2: "B v u u = B u u v" using s12 e1 by metis
    have e3: "B v u v = B u v v" using s12 by metis
    have e4: "B v v u = B u v v" using s23 e3 by metis
    show ?thesis by (simp add: add1 add2 add3 e1 e2 e3 e4 algebra_simps)
  qed
  have quad: "B (x+y) (x+y) z = B x x z + 2 * B x y z + B y y z"
    by (simp add: add1 add2 algebra_simps s12[of y x z])
  have lin: "B (x+y) z z = B x z z + B y z z" by (rule add1)
  have c1: "B (x+y+z) (x+y+z) (x+y+z) = B (x+y) (x+y) (x+y) + B z z z + 3 * B (x+y) (x+y) z + 3 * B (x+y) z z"
    by (rule cube)
  have c2: "B (x+z) (x+z) (x+z) = B x x x + B z z z + 3 * B x x z + 3 * B x z z" by (rule cube)
  have c3: "B (y+z) (y+z) (y+z) = B y y y + B z z z + 3 * B y y z + 3 * B y z z" by (rule cube)
  have c4: "B (x+y) (x+y) (x+y) = B x x x + B y y y + 3 * B x x y + 3 * B x y y" by (rule cube)
  have hz: "B x x z + B x z z = 0"
  proof -
    have "3 * (B x x z + B x z z) = 0" using c2 diag[of "x+z"] diag[of x] diag[of z] by (simp add: algebra_simps)
    then have "(3::'k) = 0 \<or> (B x x z + B x z z) = 0" by (simp only: mult_eq_0_iff)
    then show ?thesis by simp
  qed
  have hy: "B y y z + B y z z = 0"
  proof -
    have "3 * (B y y z + B y z z) = 0" using c3 diag[of "y+z"] diag[of y] diag[of z] by (simp add: algebra_simps)
    then have "(3::'k) = 0 \<or> (B y y z + B y z z) = 0" by (simp only: mult_eq_0_iff)
    then show ?thesis by simp
  qed
  have step: "B (x+y+z) (x+y+z) (x+y+z) = 0 + 0 + 3 * (B x x z + 2 * B x y z + B y y z) + 3 * (B x z z + B y z z)"
    by (simp only: c1 quad lin, simp only: diag)
  have rearr: "3 * (B x x z + 2 * B x y z + B y y z) + 3 * (B x z z + B y z z) =
      6 * B x y z + 3 * (B x x z + B x z z) + 3 * (B y y z + B y z z)" by (simp add: algebra_simps)
  have "6 * B x y z = 0"
    using step diag[of "x+y+z"] rearr hz hy by simp
  then show ?thesis by simp
qed

end
