(*  Title:      BSR_m4_Trace.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Trace lemma of the paragraph "Toward BSR(5,4)=13" of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation),
    used by Proposition "Negative-syzygy obstruction" (label prop:negsyz).
    (a) trace_pos: for real n x n matrices, Y symmetric positive definite and G symmetric positive
        semidefinite with G /= 0, tr(Y G) > 0.  The proof does not use the spectral theorem: it peels off
        one rank-one term G = (G e_k)(G e_k)^T / G_kk + G' (a Cholesky step) and inducts on the number of
        nonzero rows.
    (b) syzygy_negative: if H is a symmetric bilinear form that is negative definite on a subspace N and
        n_1,...,n_k in N are not all zero, then sum_ij Y_ij H(n_i,n_j) < 0 for every symmetric positive
        definite Y (k x k).  Here G_ij = -H(n_i,n_j) is positive semidefinite and nonzero.
    Not covered: the rest of the paragraph (dimension count, the rational multipliers, exact arithmetic),
    which are computations in the supplement and are not formalized here.
*)

theory BSR_m4_Trace
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>Definitions\<close>

definition quad :: "real^'n^'n \<Rightarrow> real^'n \<Rightarrow> real" where
  "quad A x = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * A $ i $ j * x $ j)"

definition msym :: "real^'n^'n \<Rightarrow> bool" where
  "msym A \<longleftrightarrow> (\<forall>i j. A $ i $ j = A $ j $ i)"

definition mpsd :: "real^'n^'n \<Rightarrow> bool" where
  "mpsd G \<longleftrightarrow> msym G \<and> (\<forall>x. 0 \<le> quad G x)"

definition mpd :: "real^'n^'n \<Rightarrow> bool" where
  "mpd Y \<longleftrightarrow> msym Y \<and> (\<forall>x. x \<noteq> 0 \<longrightarrow> 0 < quad Y x)"

definition mtr :: "real^'n^'n \<Rightarrow> real^'n^'n \<Rightarrow> real" where
  "mtr Y G = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Y $ i $ j * G $ j $ i)"

text \<open>mtr Y G is the trace of the matrix product Y * G.\<close>

lemma mtr_is_trace: "mtr Y G = (\<Sum>i\<in>UNIV. (Y ** G) $ i $ i)"
  by (simp add: mtr_def matrix_matrix_mult_def)

definition unitv :: "'n::finite \<Rightarrow> real^'n" where
  "unitv k = (\<chi> i. if i = k then 1 else 0)"

definition supp :: "real^'n^'n \<Rightarrow> 'n::finite set" where
  "supp G = {i. \<exists>j. G $ i $ j \<noteq> 0}"

subsection \<open>Quadratic forms\<close>

lemma sum_unit_r: "(\<Sum>j\<in>(UNIV::'n::finite set). f j * (if j = k then 1 else 0)) = (f k :: real)"
proof -
  have "\<And>j. f j * (if j = k then 1 else 0) = (if j = k then f j else 0)" by simp
  then show ?thesis by (simp add: sum.delta)
qed

lemma sum_unit_l: "(\<Sum>i\<in>(UNIV::'n::finite set). (if i = k then 1 else 0) * f i) = (f k :: real)"
proof -
  have "\<And>i. (if i = k then 1 else 0) * f i = (if i = k then f i else 0)" by simp
  then show ?thesis by (simp add: sum.delta)
qed

lemma quad_shift:
  fixes G :: "real^'n::finite^'n"
  assumes "msym G"
  shows "quad G (x + s *\<^sub>R unitv k) = quad G x + 2 * s * (\<Sum>i\<in>UNIV. x $ i * G $ i $ k) + s^2 * G $ k $ k"
proof -
  have sy: "\<And>i j. G $ i $ j = G $ j $ i" using assms by (simp add: msym_def)
  have 1: "quad G (x + s *\<^sub>R unitv k) =
    (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * G $ i $ j * x $ j)
    + s * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * G $ i $ j * (if j = k then 1 else 0))
    + s * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = k then 1 else 0) * G $ i $ j * x $ j)
    + s * s * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = k then 1 else 0) * G $ i $ j * (if j = k then 1 else 0))"
    by (simp add: quad_def unitv_def algebra_simps sum.distrib sum_distrib_left)
  have a: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * G $ i $ j * (if j = k then 1 else 0)) = (\<Sum>i\<in>UNIV. x $ i * G $ i $ k)"
    by (simp add: sum_unit_r)
  have b: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = k then 1 else 0) * G $ i $ j * x $ j) = (\<Sum>j\<in>UNIV. G $ k $ j * x $ j)"
  proof -
    have "\<And>i. (\<Sum>j\<in>UNIV. (if i = k then 1 else 0) * G $ i $ j * x $ j)
        = (if i = k then 1 else 0) * (\<Sum>j\<in>UNIV. G $ i $ j * x $ j)"
      by (simp add: sum_distrib_left mult.assoc)
    then show ?thesis by (simp add: sum_unit_l)
  qed
  have c: "(\<Sum>j\<in>UNIV. G $ k $ j * x $ j) = (\<Sum>i\<in>UNIV. x $ i * G $ i $ k)"
    by (rule sum.cong) (simp_all add: sy[of k] mult.commute)
  have d: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = k then 1 else 0) * G $ i $ j * (if j = k then 1 else 0)) = G $ k $ k"
    by (simp add: sum_unit_r sum_unit_l)
  show ?thesis unfolding 1 a b c d by (simp add: quad_def power2_eq_square algebra_simps)
qed

lemma quad_unit:
  "quad G (unitv k) = G $ k $ k"
  by (simp add: quad_def unitv_def sum_unit_r sum_unit_l)

lemma psd_diag_nonneg:
  assumes "mpsd G" shows "0 \<le> G $ k $ k"
proof -
  have "0 \<le> quad G (unitv k)" using assms by (simp add: mpsd_def)
  then show ?thesis by (simp add: quad_unit)
qed

lemma psd_diag_zero_offdiag:
  fixes G :: "real^'n::finite^'n"
  assumes "mpsd G" and "G $ i $ i = 0" and "G $ j $ j = 0"
  shows "G $ i $ j = 0"
proof -
  have sy: "msym G" using assms(1) by (simp add: mpsd_def)
  have q: "\<And>s. 0 \<le> quad G (unitv i + s *\<^sub>R unitv j)" using assms(1) by (simp add: mpsd_def)
  have e: "\<And>s. quad G (unitv i + s *\<^sub>R unitv j) = 2 * s * G $ i $ j"
  proof -
    fix s
    have "(\<Sum>l\<in>UNIV. unitv i $ l * G $ l $ j) = G $ i $ j" by (simp add: unitv_def sum_unit_l)
    then show "quad G (unitv i + s *\<^sub>R unitv j) = 2 * s * G $ i $ j"
      using quad_shift[OF sy, of "unitv i" s j] assms(2,3) by (simp add: quad_unit)
  qed
  have "0 \<le> 2 * (- G $ i $ j) * G $ i $ j" using q[of "- G $ i $ j"] e[of "- G $ i $ j"] by simp
  then have "G $ i $ j * G $ i $ j \<le> 0" by simp
  then have "G $ i $ j * G $ i $ j = 0" by (rule antisym) simp
  then show ?thesis by simp
qed

lemma psd_nonzero_diag_pos:
  fixes G :: "real^'n::finite^'n"
  assumes "mpsd G" and "G \<noteq> 0"
  shows "\<exists>k. 0 < G $ k $ k"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have dz: "\<And>k. G $ k $ k = 0" using psd_diag_nonneg[OF assms(1)] by (meson linorder_not_le order_antisym)
  have "G = 0"
  proof (rule vec_eq_iff[THEN iffD2], rule allI)
    fix i show "G $ i = 0 $ i"
    proof (rule vec_eq_iff[THEN iffD2], rule allI)
      fix j show "G $ i $ j = 0 $ i $ j" using psd_diag_zero_offdiag[OF assms(1) dz dz] by simp
    qed
  qed
  with assms(2) show False by simp
qed

subsection \<open>One Cholesky step\<close>

definition peel :: "real^'n::finite^'n \<Rightarrow> 'n \<Rightarrow> real^'n^'n" where
  "peel G k = (\<chi> i j. G $ i $ j - G $ i $ k * G $ j $ k / G $ k $ k)"

definition colv :: "real^'n::finite^'n \<Rightarrow> 'n \<Rightarrow> real^'n" where
  "colv G k = (\<chi> i. G $ i $ k)"

lemma peel_msym:
  assumes "msym G" shows "msym (peel G k)"
  using assms by (simp add: msym_def peel_def mult.commute)

lemma quad_peel:
  fixes G :: "real^'n::finite^'n"
  assumes sy: "msym G" and g: "0 < G $ k $ k"
  shows "quad (peel G k) x = quad G x - (\<Sum>i\<in>UNIV. x $ i * G $ i $ k)^2 / G $ k $ k"
proof -
  have "quad (peel G k) x = quad G x - (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * (G $ i $ k * G $ j $ k / G $ k $ k) * x $ j)"
    by (simp add: quad_def peel_def algebra_simps sum_subtractf)
  moreover have "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * (G $ i $ k * G $ j $ k / G $ k $ k) * x $ j)
      = (\<Sum>i\<in>UNIV. x $ i * G $ i $ k)^2 / G $ k $ k"
    by (simp add: power2_eq_square sum_product sum_divide_distrib algebra_simps)
  ultimately show ?thesis by simp
qed

lemma peel_psd:
  fixes G :: "real^'n::finite^'n"
  assumes "mpsd G" and g: "0 < G $ k $ k"
  shows "mpsd (peel G k)"
proof -
  have sy: "msym G" using assms(1) by (simp add: mpsd_def)
  have "\<And>x. 0 \<le> quad (peel G k) x"
  proof -
    fix x
    let ?b = "\<Sum>i\<in>UNIV. x $ i * G $ i $ k"
    let ?s = "- ?b / G $ k $ k"
    have "0 \<le> quad G (x + ?s *\<^sub>R unitv k)" using assms(1) by (simp add: mpsd_def)
    also have "quad G (x + ?s *\<^sub>R unitv k) = quad G x - ?b^2 / G $ k $ k"
      using quad_shift[OF sy, of x ?s k] g by (simp add: power2_eq_square field_simps)
    finally show "0 \<le> quad (peel G k) x" using quad_peel[OF sy g] by simp
  qed
  then show ?thesis using peel_msym[OF sy] by (simp add: mpsd_def)
qed

lemma peel_col_zero:
  fixes G :: "real^'n::finite^'n"
  assumes sy: "msym G" and g: "0 < G $ k $ k"
  shows "peel G k $ k $ j = 0"
proof -
  have "G $ k $ k * G $ j $ k / G $ k $ k = G $ j $ k" using g by simp
  then show ?thesis using sy by (simp add: peel_def msym_def)
qed

lemma peel_supp:
  fixes G :: "real^'n::finite^'n"
  assumes sy: "msym G" and g: "0 < G $ k $ k"
  shows "supp (peel G k) \<subseteq> supp G - {k}"
proof
  fix i assume i: "i \<in> supp (peel G k)"
  then obtain j where j: "peel G k $ i $ j \<noteq> 0" by (auto simp: supp_def)
  have "i \<noteq> k" using i peel_col_zero[OF sy g] by (auto simp: supp_def)
  moreover have "i \<in> supp G"
  proof (cases "G $ i $ k = 0")
    case True
    with j have "G $ i $ j \<noteq> 0" by (simp add: peel_def)
    then show ?thesis by (auto simp: supp_def)
  next
    case False
    then show ?thesis by (auto simp: supp_def)
  qed
  ultimately show "i \<in> supp G - {k}" by simp
qed

lemma mtr_peel:
  fixes G :: "real^'n::finite^'n"
  assumes g: "0 < G $ k $ k"
  shows "mtr Y G = mtr Y (peel G k) + quad Y (colv G k) / G $ k $ k"
proof -
  have "mtr Y G - mtr Y (peel G k) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Y $ i $ j * (G $ j $ k * G $ i $ k / G $ k $ k))"
    by (simp add: mtr_def peel_def algebra_simps sum_subtractf sum.distrib)
  also have "\<dots> = quad Y (colv G k) / G $ k $ k"
    by (simp add: quad_def colv_def sum_divide_distrib algebra_simps)
  finally show ?thesis by simp
qed

subsection \<open>(a) The trace lemma\<close>

theorem trace_pos:
  fixes Y G :: "real^'n::finite^'n"
  assumes Y: "mpd Y" and G: "mpsd G" and G0: "G \<noteq> 0"
  shows "0 < mtr Y G"
proof -
  have main: "\<And>n. \<forall>G::real^'n^'n. card (supp G) = n \<longrightarrow> mpsd G \<longrightarrow> G \<noteq> 0 \<longrightarrow> 0 < mtr Y G"
  proof -
    fix n
    show "\<forall>G::real^'n^'n. card (supp G) = n \<longrightarrow> mpsd G \<longrightarrow> G \<noteq> 0 \<longrightarrow> 0 < mtr Y G"
    proof (induction n rule: less_induct)
      case (less n)
      show ?case
      proof (intro allI impI)
        fix G :: "real^'n^'n"
        assume cn: "card (supp G) = n" and psd: "mpsd G" and ne: "G \<noteq> 0"
        obtain k where k: "0 < G $ k $ k" using psd_nonzero_diag_pos[OF psd ne] by blast
        let ?G' = "peel G k"
        let ?v = "colv G k"
        have vne: "?v \<noteq> 0"
        proof
          assume "?v = 0"
          then have "?v $ k = 0" by simp
          with k show False by (simp add: colv_def)
        qed
        have qpos: "0 < quad Y ?v / G $ k $ k" using Y vne k by (simp add: mpd_def)
        have tr: "mtr Y G = mtr Y ?G' + quad Y ?v / G $ k $ k" by (rule mtr_peel[OF k])
        have kin: "k \<in> supp G" using k by (auto simp: supp_def intro!: exI[of _ k])
        have lt: "card (supp ?G') < n"
        proof -
          have sy: "msym G" using psd by (simp add: mpsd_def)
          have "supp ?G' \<subseteq> supp G - {k}" by (rule peel_supp[OF sy k])
          then have "card (supp ?G') \<le> card (supp G - {k})" by (intro card_mono) simp_all
          also have "\<dots> = card (supp G) - 1" using kin by (simp add: card_Diff_singleton)
          finally have "card (supp ?G') \<le> n - 1" using cn by simp
          moreover have "0 < n" using kin cn by (metis card_gt_0_iff empty_iff finite)
          ultimately show ?thesis by simp
        qed
        show "0 < mtr Y G"
        proof (cases "?G' = 0")
          case True
          then have "mtr Y ?G' = 0" by (simp add: mtr_def)
          with tr qpos show ?thesis by simp
        next
          case False
          have "0 < mtr Y ?G'" using less.IH[OF lt] peel_psd[OF psd k] False by blast
          with tr qpos show ?thesis by simp
        qed
      qed
    qed
  qed
  show ?thesis using main[of "card (supp G)"] G G0 by blast
qed

subsection \<open>(b) The syzygy corollary\<close>

theorem syzygy_negative:
  fixes H :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> real"
    and nv :: "'k::finite \<Rightarrow> 'a"
    and Y :: "real^'k^'k"
  assumes Hb: "bilinear H" and Hs: "\<And>x y. H x y = H y x"
    and N: "subspace N" and Hneg: "\<And>x. x \<in> N \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> H x x < 0"
    and nN: "\<And>i. nv i \<in> N" and nz: "\<exists>i. nv i \<noteq> 0"
    and Y: "mpd Y"
  shows "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Y $ i $ j * H (nv i) (nv j)) < 0"
proof -
  let ?G = "(\<chi> i j. - H (nv i) (nv j)) :: real^'k^'k"
  have Gsym: "msym ?G" by (simp add: msym_def Hs)
  have Hlin1: "\<And>y. linear (\<lambda>x. H x y)" using Hb by (simp add: bilinear_def)
  have Hlin2: "\<And>x. linear (\<lambda>y. H x y)" using Hb by (simp add: bilinear_def)
  have qG: "\<And>x. quad ?G x = - H (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i) (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i)"
  proof -
    fix x :: "real^'k"
    have s1: "\<And>w. H (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i) w = (\<Sum>i\<in>UNIV. x $ i * H (nv i) w)"
      by (simp add: linear_sum[OF Hlin1] linear_cmul[OF Hlin1] o_def)
    have s2: "\<And>u. H u (\<Sum>j\<in>UNIV. x $ j *\<^sub>R nv j) = (\<Sum>j\<in>UNIV. x $ j * H u (nv j))"
      by (simp add: linear_sum[OF Hlin2] linear_cmul[OF Hlin2] o_def)
    have "H (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i) (\<Sum>j\<in>UNIV. x $ j *\<^sub>R nv j)
        = (\<Sum>i\<in>UNIV. x $ i * H (nv i) (\<Sum>j\<in>UNIV. x $ j *\<^sub>R nv j))" by (rule s1)
    also have "\<dots> = (\<Sum>i\<in>UNIV. x $ i * (\<Sum>j\<in>UNIV. x $ j * H (nv i) (nv j)))"
      by (simp only: s2)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * x $ j * H (nv i) (nv j))"
      by (simp add: sum_distrib_left mult.assoc)
    finally have "H (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i) (\<Sum>j\<in>UNIV. x $ j *\<^sub>R nv j)
        = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * x $ j * H (nv i) (nv j))" .
    then show "quad ?G x = - H (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i) (\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i)"
      by (simp add: quad_def sum_negf algebra_simps)
  qed
  have Gpsd: "mpsd ?G"
  proof -
    have "\<And>x. 0 \<le> quad ?G x"
    proof -
      fix x :: "real^'k"
      let ?w = "\<Sum>i\<in>UNIV. x $ i *\<^sub>R nv i"
      have "?w \<in> N" using N nN by (intro subspace_sum) (simp_all add: subspace_scale)
      then have "H ?w ?w \<le> 0"
        using Hneg[of ?w] by (cases "?w = 0") (auto simp: linear_0[OF Hlin1])
      then show "0 \<le> quad ?G x" by (simp add: qG)
    qed
    then show ?thesis using Gsym by (simp add: mpsd_def)
  qed
  obtain i0 where i0: "nv i0 \<noteq> 0" using nz by blast
  have Gne: "?G \<noteq> 0"
  proof
    assume "?G = 0"
    then have "?G $ i0 $ i0 = 0" by simp
    then have "H (nv i0) (nv i0) = 0" by simp
    with Hneg[OF nN i0] show False by simp
  qed
  have "0 < mtr Y ?G" by (rule trace_pos[OF Y Gpsd Gne])
  moreover have "mtr Y ?G = - (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Y $ i $ j * H (nv i) (nv j))"
    by (simp add: mtr_def Hs sum_negf)
  ultimately show ?thesis by simp
qed

end
