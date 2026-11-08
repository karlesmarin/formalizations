(* encaje: Lemma 1 of V236 (algebraic part): for the cyclic permutation P, D = diag(1..m), Q = D P^T = D P^-1,
   a matrix M with MP = P^T M, MQ = Q^T M, P^T M Q = Q^T M P is zero; matrices as functions on indices < m *)
theory Regular_Point
  imports Complex_Main
begin

text \<open>Lemma 1 of the note (an integer regular point of the sum-of-squares map in every dimension
  $m\ge2$), algebraic core. The point is $C=[I\;P\;Q]$ with $P$ the cyclic permutation matrix,
  $D=\mathrm{diag}(1,\dots,m)$ and $Q=DP^{-1}$. A Hankel form vanishing on $\ker C$ is $C^{\mathsf T}MC$
  with $M$ symmetric, and the symmetry of its blocks $(1,2)$, $(1,3)$, $(2,3)$ reads
  $MP=P^{\mathsf T}M$, $MQ=Q^{\mathsf T}M$, $P^{\mathsf T}MQ=Q^{\mathsf T}MP$. Then
  $M(PQ-QP)=0$ and $PQ-QP=PDP^{-1}-D$ is diagonal and invertible, so $M=0$
  (theorem \<open>regular_point_algebra\<close>). The translation from the Hankel form to these three matrix
  equations (choice of the kernel basis $(-Pe_i,e_i,0)$, $(-Qe_i,0,e_i)$) is the text of the note and
  is not formalized here. Symmetry of $M$ is not needed.

  Matrices are functions \<open>nat \<Rightarrow> nat \<Rightarrow> real\<close> read on indices $<m$; $P$ sends row $i$ to column
  $i+1$ modulo $m$ (\<open>sm\<close>), and $P^{-1}=P^{\mathsf T}$ (\<open>cycP_orth\<close>).\<close>

definition mmul :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "mmul m A B = (\<lambda>i j. \<Sum>l<m. A i l * B l j)"

definition mtr :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "mtr A = (\<lambda>i j. A j i)"

text \<open>Successor modulo $m$ on $\{0,\dots,m-1\}$.\<close>
definition sm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sm m i = (if Suc i = m then 0 else Suc i)"

definition cycP :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "cycP m = (\<lambda>i j. if j = sm m i then 1 else 0)"

definition diagD :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "diagD = (\<lambda>i j. if i = j then of_nat (Suc i) else 0)"

definition cycQ :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "cycQ m = mmul m diagD (mtr (cycP m))"

lemma sm_less: "i < m \<Longrightarrow> sm m i < m"
  unfolding sm_def by auto

lemma sm_inj: "i < m \<Longrightarrow> j < m \<Longrightarrow> sm m i = sm m j \<Longrightarrow> i = j"
  unfolding sm_def by (auto split: if_splits)

lemma sm_onto: "i < m \<Longrightarrow> \<exists>l<m. sm m l = i"
proof (cases i)
  case 0
  assume "i < m"
  then show ?thesis using 0 by (intro exI[of _ "m - 1"]) (auto simp: sm_def)
next
  case (Suc k)
  assume "i < m"
  then show ?thesis using Suc by (intro exI[of _ k]) (auto simp: sm_def)
qed

lemma sum_sm_eq:
  fixes c :: real
  assumes i: "i < m"
  shows "(\<Sum>l<m. if sm m l = i then c else 0) = c"
proof -
  obtain l0 where l0: "l0 < m" "sm m l0 = i" using sm_onto[OF i] by blast
  have "(\<Sum>l<m. if sm m l = i then c else 0) = (\<Sum>l<m. if l = l0 then c else 0)"
    using l0 sm_inj sm_less by (intro sum.cong refl) (metis lessThan_iff)
  also have "\<dots> = c" using l0 by simp
  finally show ?thesis .
qed

text \<open>$PP^{\mathsf T}=I$, so $Q=DP^{\mathsf T}=DP^{-1}$.\<close>
lemma cycP_orth:
  assumes "i < m" "j < m"
  shows "mmul m (cycP m) (mtr (cycP m)) i j = (if i = j then 1 else 0)"
proof -
  have "mmul m (cycP m) (mtr (cycP m)) i j = (\<Sum>l<m. if l = sm m i then (if sm m i = sm m j then 1 else 0) else 0)"
    unfolding mmul_def cycP_def mtr_def by (intro sum.cong refl) auto
  also have "\<dots> = (if sm m i = sm m j then 1 else 0)" using sm_less[OF assms(1)] by simp
  also have "\<dots> = (if i = j then 1 else 0)" using sm_inj[OF assms] by auto
  finally show ?thesis .
qed

lemma cycQ_entry: "j < m \<Longrightarrow> l < m \<Longrightarrow> cycQ m l j = (if l = sm m j then of_nat (Suc l) else 0)"
proof -
  assume "j < m" "l < m"
  have "cycQ m l j = (\<Sum>t<m. if t = l then of_nat (Suc l) * cycP m j t else 0)"
    unfolding cycQ_def mmul_def diagD_def mtr_def by (intro sum.cong refl) auto
  also have "\<dots> = of_nat (Suc l) * cycP m j l" using \<open>l < m\<close> by simp
  finally show ?thesis by (simp add: cycP_def)
qed

lemma mmul_assoc: "mmul m (mmul m A B) C = mmul m A (mmul m B C)"
proof (intro ext)
  fix i j
  have "mmul m (mmul m A B) C i j = (\<Sum>l<m. \<Sum>t<m. A i t * B t l * C l j)"
    unfolding mmul_def by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>t<m. \<Sum>l<m. A i t * B t l * C l j)" by (rule sum.swap)
  also have "\<dots> = mmul m A (mmul m B C) i j"
    unfolding mmul_def by (simp add: sum_distrib_left mult_ac)
  finally show "mmul m (mmul m A B) C i j = mmul m A (mmul m B C) i j" .
qed

lemma mmul_cong_left:
  assumes "\<forall>i<m. \<forall>j<m. A i j = A' i j" "i < m"
  shows "mmul m A B i j = mmul m A' B i j"
  unfolding mmul_def using assms by (intro sum.cong refl) auto

text \<open>$(M\,PQ)_{ij}=M_{ij}\,(\mathrm{sm}(j)+1)$ and $(M\,QP)_{ij}=M_{ij}\,(j+1)$.\<close>
lemma M_PQ:
  assumes "i < m" "j < m"
  shows "mmul m M (mmul m (cycP m) (cycQ m)) i j = M i j * of_nat (Suc (sm m j))"
proof -
  have PQ: "mmul m (cycP m) (cycQ m) l j = (if l = j then of_nat (Suc (sm m j)) else 0)" if l: "l < m" for l
  proof -
    have "mmul m (cycP m) (cycQ m) l j = (\<Sum>t<m. if t = sm m l then cycQ m (sm m l) j else 0)"
      unfolding mmul_def cycP_def by (intro sum.cong refl) auto
    also have "\<dots> = cycQ m (sm m l) j" using sm_less[OF l] by simp
    also have "\<dots> = (if sm m l = sm m j then of_nat (Suc (sm m l)) else 0)"
      using cycQ_entry[OF assms(2) sm_less[OF l]] .
    also have "\<dots> = (if l = j then of_nat (Suc (sm m j)) else 0)" using sm_inj[OF l assms(2)] by auto
    finally show ?thesis .
  qed
  have "mmul m M (mmul m (cycP m) (cycQ m)) i j = (\<Sum>l<m. if l = j then M i j * of_nat (Suc (sm m j)) else 0)"
    unfolding mmul_def[of m M] using PQ by (intro sum.cong refl) auto
  also have "\<dots> = M i j * of_nat (Suc (sm m j))" using assms(2) by simp
  finally show ?thesis .
qed

lemma M_QP:
  assumes "i < m" "j < m"
  shows "mmul m M (mmul m (cycQ m) (cycP m)) i j = M i j * of_nat (Suc j)"
proof -
  have QP: "mmul m (cycQ m) (cycP m) l j = (if l = j then of_nat (Suc j) else 0)" if l: "l < m" for l
  proof -
    have "mmul m (cycQ m) (cycP m) l j = (\<Sum>t<m. if sm m t = l then (if l = j then of_nat (Suc l) else 0) else 0)"
      unfolding mmul_def cycP_def
      by (intro sum.cong refl) (use l in \<open>auto simp: cycQ_entry sm_less sm_inj\<close>)
    also have "\<dots> = (if l = j then of_nat (Suc l) else 0)" by (rule sum_sm_eq[OF l])
    finally show ?thesis by simp
  qed
  have "mmul m M (mmul m (cycQ m) (cycP m)) i j = (\<Sum>l<m. if l = j then M i j * of_nat (Suc j) else 0)"
    unfolding mmul_def[of m M] using QP by (intro sum.cong refl) auto
  also have "\<dots> = M i j * of_nat (Suc j)" using assms(2) by simp
  finally show ?thesis .
qed

text \<open>Lemma 1, algebraic part: the three block symmetries force $M=0$ (for $m\ge2$).\<close>
theorem regular_point_algebra:
  assumes m: "2 \<le> m"
    and sym: "\<forall>i<m. \<forall>j<m. M j i = M i j"
    and h1: "\<forall>i<m. \<forall>j<m. mmul m M (cycP m) i j = mmul m (mtr (cycP m)) M i j"
    and h2: "\<forall>i<m. \<forall>j<m. mmul m M (cycQ m) i j = mmul m (mtr (cycQ m)) M i j"
    and h3: "\<forall>i<m. \<forall>j<m. mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j
                         = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j"
  shows "\<forall>i<m. \<forall>j<m. M i j = 0"
proof (intro allI impI)
  fix i j assume i: "i < m" and j: "j < m"
  have "mmul m M (mmul m (cycP m) (cycQ m)) i j = mmul m (mmul m M (cycP m)) (cycQ m) i j"
    by (simp add: mmul_assoc)
  also have "\<dots> = mmul m (mmul m (mtr (cycP m)) M) (cycQ m) i j"
    by (rule mmul_cong_left[OF h1 i])
  also have "\<dots> = mmul m (mmul m (mtr (cycQ m)) M) (cycP m) i j"
    using h3 i j by blast
  also have "\<dots> = mmul m (mmul m M (cycQ m)) (cycP m) i j"
    by (rule mmul_cong_left[OF _ i]) (use h2 in simp)
  also have "\<dots> = mmul m M (mmul m (cycQ m) (cycP m)) i j"
    by (simp add: mmul_assoc)
  finally have "M i j * of_nat (Suc (sm m j)) = M i j * of_nat (Suc j)"
    using M_PQ[OF i j] M_QP[OF i j] by simp
  moreover have "sm m j \<noteq> j" using m j unfolding sm_def by auto
  ultimately show "M i j = 0" by simp
qed

end
