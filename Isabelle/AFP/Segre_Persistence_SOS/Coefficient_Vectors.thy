(* encaje: shared base of the entry (inner product of coefficient vectors, C4-free supports) *)
section \<open>Coefficient vectors\<close>

theory Coefficient_Vectors
  imports Complex_Main
begin

text \<open>A sum of \<open>r\<close> squares of bilinear forms is described by its coefficient vectors: the
  coefficient of the monomial \<open>x\<^sub>i y\<^sub>j\<close> in the \<open>r\<close> bilinear forms. Throughout the entry these
  vectors are functions from an index set to the scalars, and there is a single inner product,
  \<open>dot_on K u w = (\<Sum>k\<in>K. u k * w k)\<close>, summed over a set \<open>K\<close> of coordinates. Two instances
  are used: \<open>K = {..<r}\<close> for vectors indexed by natural numbers (abbreviated \<open>dot_upto r\<close>),
  and \<open>K = UNIV\<close> for vectors indexed by a finite type.\<close>

definition dot_on :: "'k set \<Rightarrow> ('k \<Rightarrow> 'a::comm_semiring_0) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "dot_on K u w = (\<Sum>k\<in>K. u k * w k)"

abbreviation dot_upto :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::comm_semiring_0) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "dot_upto r \<equiv> dot_on {..<r}"

lemma dot_on_comm: "dot_on K u w = dot_on K w u"
  by (simp add: dot_on_def mult.commute)

lemma dot_on_cong_right:
  "(\<And>k. k \<in> K \<Longrightarrow> w k = w' k) \<Longrightarrow> dot_on K u w = dot_on K u w'"
  unfolding dot_on_def by (rule sum.cong) simp_all

lemma dot_on_zero_left: "(\<And>k. k \<in> K \<Longrightarrow> u k = 0) \<Longrightarrow> dot_on K u w = 0"
  by (simp add: dot_on_def)

lemma dot_on_self_nonneg: "0 \<le> dot_on K u (u :: 'k \<Rightarrow> 'a::linordered_idom)"
  unfolding dot_on_def by (rule sum_nonneg) simp

lemma dot_on_self_eq_0:
  fixes u :: "'k \<Rightarrow> 'a::linordered_idom"
  assumes "finite K"
  shows "dot_on K u u = 0 \<longleftrightarrow> (\<forall>k\<in>K. u k = 0)"
proof -
  have "(\<Sum>k\<in>K. u k * u k) = 0 \<longleftrightarrow> (\<forall>k\<in>K. u k * u k = 0)"
    using assms by (intro sum_nonneg_eq_0_iff) simp_all
  then show ?thesis unfolding dot_on_def by simp
qed

lemma dot_upto_self_zero:
  fixes u :: "nat \<Rightarrow> 'a::linordered_idom"
  assumes "dot_upto r u u = 0" "k < r"
  shows "u k = 0"
  using assms dot_on_self_eq_0[of "{..<r}" u] by simp

lemma dot_on_diff_left:
  "dot_on K (\<lambda>i. x i - c * u i) y = dot_on K x y - c * dot_on K u (y :: 'k \<Rightarrow> 'a::comm_ring)"
  by (simp add: dot_on_def algebra_simps sum_subtractf sum_distrib_left)

lemma dot_on_diff_right:
  "dot_on K y (\<lambda>i. x i - c * u i) = dot_on K y x - c * dot_on K y (u :: 'k \<Rightarrow> 'a::comm_ring)"
  using dot_on_diff_left[of K x c u y] by (simp add: dot_on_comm[of K y])

lemma dot_on_reindex:
  assumes "bij_betw h A B"
  shows "dot_on A (x \<circ> h) (y \<circ> h) = dot_on B x y"
  using sum.reindex_bij_betw[OF assms, of "\<lambda>k. x k * y k"] by (simp add: dot_on_def)

section \<open>Supports without a four-cycle\<close>

text \<open>A set \<open>E\<close> of cells \<open>(i, j)\<close> is \<open>C\<^sub>4\<close>-free if no two rows share two columns, i.e.\ the
  bipartite graph with edge set \<open>E\<close> has no cycle of length four.\<close>

definition c4_free :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "c4_free E \<longleftrightarrow> (\<forall>i i' j j'. i \<noteq> i' \<longrightarrow> j \<noteq> j' \<longrightarrow>
     \<not> ((i, j) \<in> E \<and> (i, j') \<in> E \<and> (i', j) \<in> E \<and> (i', j') \<in> E))"

end
