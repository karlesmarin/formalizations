(*  Title:      Regular_Point_Hankel.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: Lemma 2 of the note BSR(m,3) = 2m, complete linear-algebra form: a Hankel multiplier H on A^3 (blocks
   symmetric, H_jl = H_lj) that vanishes on ker[I P Q] is zero; builds on Regular_Point.regular_point_algebra *)
theory Regular_Point_Hankel
  imports Regular_Point
begin

text \<open>Vectors of $V=A^3$ are functions \<open>x j i\<close> (block $j<3$, row $i<m$); a symmetric form $H$ on $V$
  is given by its blocks \<open>h j l i i'\<close>. $H$ is a \emph{Hankel} multiplier when every block is symmetric and
  $H_{jl}=H_{lj}$ (equation (2.1) of the note). With $C=[I\;P\;Q]$, the integer point of Lemma 2 is a basis of
  $\ker C$; the lemma is equivalent to: no Hankel $H\neq0$ vanishes on $\ker C$ (\<open>regular_point_hankel\<close>).
  The vectors $(-Pe_e,e_e,0)$ and $(-Qe_e,0,e_e)$ lie in $\ker C$; $H$ vanishing on them gives
  $H_{j1}=H_{j0}P$ and $H_{j2}=H_{j0}Q$, and the Hankel symmetries turn these into the three equations of
  \<open>regular_point_algebra\<close> for $M=H_{00}$.\<close>

definition Hx :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "Hx m h x = (\<lambda>j i. \<Sum>l<3. \<Sum>i'<m. h j l i i' * x l i')"

definition Cx :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Cx m x = (\<lambda>i. x 0 i + (\<Sum>t<m. cycP m i t * x 1 t) + (\<Sum>t<m. cycQ m i t * x 2 t))"

definition hankel :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "hankel m h \<longleftrightarrow> (\<forall>j<3. \<forall>l<3. \<forall>i<m. \<forall>i'<m. h j l i' i = h j l i i' \<and> h l j i i' = h j l i i')"

text \<open>The two families of kernel vectors.\<close>
definition kP :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "kP m e = (\<lambda>j i. if j = 0 then - cycP m i e else if j = 1 then (if i = e then 1 else 0) else 0)"

definition kQ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "kQ m e = (\<lambda>j i. if j = 0 then - cycQ m i e else if j = 2 then (if i = e then 1 else 0) else 0)"

lemma sum_ind: "e < (m::nat) \<Longrightarrow> (\<Sum>t<m. f t * (if t = e then 1 else 0)) = (f e :: real)"
proof -
  assume e: "e < m"
  have "(\<Sum>t<m. f t * (if t = e then 1 else 0)) = (\<Sum>t<m. if t = e then f t else 0)"
    by (intro sum.cong) auto
  also have "\<dots> = f e" using e by (subst sum.delta) (auto simp: finite_lessThan)
  finally show ?thesis .
qed

lemma kP_ker: "e < m \<Longrightarrow> Cx m (kP m e) i = 0"
proof -
  assume e: "e < m"
  have k0: "kP m e 0 i = - cycP m i e" and k1: "kP m e (Suc 0) t = (if t = e then 1 else 0)"
    and k2: "kP m e 2 t = 0" for t
    by (simp_all add: kP_def)
  show ?thesis unfolding Cx_def using sum_ind[OF e, of "\<lambda>t. cycP m i t"] by (simp add: k0 k1 k2)
qed

lemma kQ_ker: "e < m \<Longrightarrow> Cx m (kQ m e) i = 0"
proof -
  assume e: "e < m"
  have k0: "kQ m e 0 i = - cycQ m i e" and k1: "kQ m e (Suc 0) t = 0"
    and k2: "kQ m e 2 t = (if t = e then 1 else 0)" for t
    by (simp_all add: kQ_def)
  show ?thesis unfolding Cx_def using sum_ind[OF e, of "\<lambda>t. cycQ m i t"] by (simp add: k0 k1 k2)
qed

lemma sum3: "(\<Sum>l<(3::nat). f l) = f 0 + f 1 + (f 2 :: real)"
proof -
  have "{..<(3::nat)} = {0, 1, 2}" by auto
  then show ?thesis by (simp add: add.assoc)
qed

lemma H_on_kP:
  assumes e: "e < m" and i: "i < m"
  shows "Hx m h (kP m e) j i = h j 1 i e - mmul m (h j 0) (cycP m) i e"
proof -
  have "Hx m h (kP m e) j i = (\<Sum>i'<m. h j 0 i i' * - cycP m i' e) + (\<Sum>i'<m. h j 1 i i' * (if i' = e then 1 else 0))"
    unfolding Hx_def kP_def sum3 by simp
  also have "(\<Sum>i'<m. h j 1 i i' * (if i' = e then 1 else 0)) = h j 1 i e"
    using e by (simp add: if_distrib cong: if_cong)
  also have "(\<Sum>i'<m. h j 0 i i' * - cycP m i' e) = - mmul m (h j 0) (cycP m) i e"
    unfolding mmul_def by (simp add: sum_negf)
  finally show ?thesis by simp
qed

lemma H_on_kQ:
  assumes e: "e < m" and i: "i < m"
  shows "Hx m h (kQ m e) j i = h j 2 i e - mmul m (h j 0) (cycQ m) i e"
proof -
  have "Hx m h (kQ m e) j i = (\<Sum>i'<m. h j 0 i i' * - cycQ m i' e) + (\<Sum>i'<m. h j 2 i i' * (if i' = e then 1 else 0))"
    unfolding Hx_def kQ_def sum3 by simp
  also have "(\<Sum>i'<m. h j 2 i i' * (if i' = e then 1 else 0)) = h j 2 i e"
    using e by (simp add: if_distrib cong: if_cong)
  also have "(\<Sum>i'<m. h j 0 i i' * - cycQ m i' e) = - mmul m (h j 0) (cycQ m) i e"
    unfolding mmul_def by (simp add: sum_negf)
  finally show ?thesis by simp
qed

text \<open>Transposing a product with a symmetric factor.\<close>
lemma mmul_tr_sym:
  assumes sym: "\<forall>i<m. \<forall>j<m. M j i = M i j" and i: "i < m" and j: "j < m"
  shows "mmul m M A j i = mmul m (mtr A) M i j"
  unfolding mmul_def mtr_def using sym i j by (intro sum.cong refl) (simp add: mult.commute)

theorem regular_point_hankel:
  assumes m: "2 \<le> m"
    and hk: "hankel m h"
    and ker: "\<forall>x. (\<forall>i<m. Cx m x i = 0) \<longrightarrow> (\<forall>j<3. \<forall>i<m. Hx m h x j i = 0)"
  shows "\<forall>j<3. \<forall>l<3. \<forall>i<m. \<forall>i'<m. h j l i i' = 0"
proof -
  have b1: "h j 1 i e = mmul m (h j 0) (cycP m) i e" if "j < 3" "i < m" "e < m" for j i e
    using ker[rule_format, of "kP m e" j i] kP_ker[of e m] H_on_kP[of e m i h j] that by auto
  have b2: "h j 2 i e = mmul m (h j 0) (cycQ m) i e" if "j < 3" "i < m" "e < m" for j i e
    using ker[rule_format, of "kQ m e" j i] kQ_ker[of e m] H_on_kQ[of e m i h j] that by auto
  have hsym: "h j l i' i = h j l i i'" if "j < 3" "l < 3" "i < m" "i' < m" for j l i i'
    using hk that unfolding hankel_def by blast
  have hswap: "h l j i i' = h j l i i'" if "j < 3" "l < 3" "i < m" "i' < m" for j l i i'
    using hk that unfolding hankel_def by blast
  define M where "M = h 0 0"
  have Msym: "\<forall>i<m. \<forall>j<m. M j i = M i j" unfolding M_def using hsym by auto
  \<comment> \<open>$H_{01}=MP$, symmetric: $MP=P^{\mathsf T}M$\<close>
  have h1: "\<forall>i<m. \<forall>j<m. mmul m M (cycP m) i j = mmul m (mtr (cycP m)) M i j"
  proof (intro allI impI)
    fix i j assume i: "i < m" and j: "j < m"
    have "mmul m M (cycP m) i j = h 0 1 i j" using b1[of 0 i j] i j by (simp add: M_def)
    also have "\<dots> = h 0 1 j i" using hsym[of 0 1 j i] i j by simp
    also have "\<dots> = mmul m M (cycP m) j i" using b1[of 0 j i] i j by (simp add: M_def)
    also have "\<dots> = mmul m (mtr (cycP m)) M i j" by (rule mmul_tr_sym[OF Msym i j])
    finally show "mmul m M (cycP m) i j = mmul m (mtr (cycP m)) M i j" .
  qed
  have h2: "\<forall>i<m. \<forall>j<m. mmul m M (cycQ m) i j = mmul m (mtr (cycQ m)) M i j"
  proof (intro allI impI)
    fix i j assume i: "i < m" and j: "j < m"
    have "mmul m M (cycQ m) i j = h 0 2 i j" using b2[of 0 i j] i j by (simp add: M_def)
    also have "\<dots> = h 0 2 j i" using hsym[of 0 2 j i] i j by simp
    also have "\<dots> = mmul m M (cycQ m) j i" using b2[of 0 j i] i j by (simp add: M_def)
    also have "\<dots> = mmul m (mtr (cycQ m)) M i j" by (rule mmul_tr_sym[OF Msym i j])
    finally show "mmul m M (cycQ m) i j = mmul m (mtr (cycQ m)) M i j" .
  qed
  \<comment> \<open>$H_{10}=P^{\mathsf T}M$, so $H_{12}=H_{10}Q=P^{\mathsf T}MQ$, symmetric\<close>
  have H10: "h 1 0 i t = mmul m (mtr (cycP m)) M i t" if "i < m" "t < m" for i t
  proof -
    have "h 1 0 i t = h 0 1 i t" using hswap[of 0 1 i t] that by simp
    also have "\<dots> = mmul m M (cycP m) i t" using b1[of 0 i t] that by (simp add: M_def)
    also have "\<dots> = mmul m (mtr (cycP m)) M i t" using h1 that by blast
    finally show ?thesis .
  qed
  have H12: "h 1 2 i j = mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j" if "i < m" "j < m" for i j
  proof -
    have "h 1 2 i j = mmul m (h 1 0) (cycQ m) i j" using b2[of 1 i j] that by simp
    also have "\<dots> = mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j"
      by (rule mmul_cong_left[OF _ that(1)]) (use H10 in auto)
    finally show ?thesis .
  qed
  have h3: "\<forall>i<m. \<forall>j<m. mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j
                         = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j"
  proof (intro allI impI)
    fix i j assume i: "i < m" and j: "j < m"
    have "mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j = h 1 2 i j" using H12[OF i j] by simp
    also have "\<dots> = h 1 2 j i" using hsym[of 1 2 j i] i j by simp
    also have "\<dots> = mmul m (mmul m (mtr (cycP m)) M) (cycQ m) j i" using H12[OF j i] by simp
    also have "\<dots> = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j"
    proof -
      have "mmul m (mmul m (mtr (cycP m)) M) (cycQ m) j i = (\<Sum>s<m. \<Sum>t<m. cycP m t j * M t s * cycQ m s i)"
        unfolding mmul_def mtr_def by (simp add: sum_distrib_right)
      also have "\<dots> = (\<Sum>t<m. \<Sum>s<m. cycQ m s i * M s t * cycP m t j)"
        by (subst sum.swap) (intro sum.cong refl, use Msym i j in \<open>auto simp: mult_ac\<close>)
      also have "\<dots> = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j"
        unfolding mmul_def mtr_def by (simp add: sum_distrib_right)
      finally show ?thesis .
    qed
    finally show "mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j" .
  qed
  have M0: "\<forall>i<m. \<forall>j<m. M i j = 0" by (rule regular_point_algebra[OF m Msym h1 h2 h3])
  \<comment> \<open>every block is now zero\<close>
  have c0: "h j 0 i t = 0" if "j < 3" "i < m" "t < m" for j i t
  proof -
    have "h j 0 i t = h 0 j i t" using hswap[of 0 j i t] that by simp
    moreover have "h 0 1 i t = 0" using b1[of 0 i t] that M0 unfolding mmul_def M_def by simp
    moreover have "h 0 2 i t = 0" using b2[of 0 i t] that M0 unfolding mmul_def M_def by simp
    moreover have "h 0 0 i t = 0" using M0 that by (simp add: M_def)
    moreover have "j = 0 \<or> j = 1 \<or> j = 2" using that(1) by auto
    ultimately show ?thesis by auto
  qed
  show ?thesis
  proof (intro allI impI)
    fix j l i i' :: nat assume j: "j < 3" and l: "l < 3" and i: "i < m" and i': "i' < m"
    have "l = 0 \<or> l = 1 \<or> l = 2" using l by auto
    moreover have "h j 1 i i' = 0" using b1[OF j i i'] c0[OF j i] unfolding mmul_def by simp
    moreover have "h j 2 i i' = 0" using b2[OF j i i'] c0[OF j i] unfolding mmul_def by simp
    moreover have "h j 0 i i' = 0" using c0[OF j i i'] .
    ultimately show "h j l i i' = 0" by auto
  qed
qed

end
