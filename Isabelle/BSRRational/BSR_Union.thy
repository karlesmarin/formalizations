theory BSR_Union
  imports BSR_Rational Seven_Embedding
begin

text \<open>The bound $\mathrm{BSR}_\mathbb{Q}(m,n)\ge z(m,n)+3$: the two halves joined. Let $E$ be a finite
  $C_4$-free support with one edge of weight $7$ and the others of weight $1$. A representation of
  $f=\sum_{(i,j)\in E}c_{ij}x_i^2y_j^2$ by rational squares, given through its coefficient vectors
  (the hypothesis \<open>polarized\<close> of \<open>BSR_Rational\<close>), has at least $|E|+3$ squares. The squares
  are indexed by the finite type \<open>'r\<close>.\<close>

theorem bsr_rational_lower:
  fixes v :: "'a \<Rightarrow> 'b \<Rightarrow> 'r::finite \<Rightarrow> rat" and c :: "'a \<Rightarrow> 'b \<Rightarrow> rat"
  assumes fin: "finite E" and P: "polarized E c v" and C: "c4_free E"
    and a: "a \<in> E" and c7: "c (fst a) (snd a) = 7"
    and c1: "\<And>e. e \<in> E \<Longrightarrow> e \<noteq> a \<Longrightarrow> c (fst e) (snd e) = 1"
  shows "card E + 3 \<le> card (UNIV :: 'r set)"
proof -
  obtain h where h: "bij_betw h {0..<card (UNIV :: 'r set)} (UNIV :: 'r set)"
    using ex_bij_betw_nat_finite[of "UNIV :: 'r set"] by auto
  have bridge: "Seven_Embedding.dot (card (UNIV :: 'r set)) (x \<circ> h) (y \<circ> h) = BSR_Rational.dot x y"
    for x y :: "'r \<Rightarrow> rat"
  proof -
    have "(\<Sum>i\<in>{0..<card (UNIV :: 'r set)}. x (h i) * y (h i)) = (\<Sum>k\<in>UNIV. x k * y k)"
      using sum.reindex_bij_betw[OF h, of "\<lambda>k. x k * y k"] by simp
    then show ?thesis
      by (simp add: Seven_Embedding.dot_def BSR_Rational.dot_def atLeast0LessThan)
  qed
  have fin': "finite (E - {a})" using fin by simp
  have cardE: "card (E - {a}) = card E - 1" using a fin by simp
  obtain q where q0: "bij_betw q {0..<card (E - {a})} (E - {a})"
    using ex_bij_betw_nat_finite[OF fin'] by auto
  have q: "bij_betw q {0..<card E - 1} (E - {a})" using q0 cardE by simp
  have qE: "q i \<in> E" and qa: "q i \<noteq> a" if "i < card E - 1" for i
  proof -
    have "q i \<in> E - {a}" using bij_betw_apply[OF q] that by simp
    then show "q i \<in> E" and "q i \<noteq> a" by auto
  qed
  have qinj: "q i \<noteq> q j" if "i < card E - 1" "j < card E - 1" "i \<noteq> j" for i j
    using q that unfolding bij_betw_def inj_on_def by auto
  have emb: "BSR_Rational.dot (v (fst e) (snd e)) (v (fst e') (snd e')) =
      (if e = e' then c (fst e) (snd e) else 0)" if "e \<in> E" "e' \<in> E" for e e'
    using embedding[OF P C] that by blast
  obtain V where V: "V = (\<lambda>i. v (fst (q i)) (snd (q i)) \<circ> h)" by simp
  obtain W where W: "W = v (fst a) (snd a) \<circ> h" by simp
  have one: "1 \<le> card E" using a fin by (simp add: Suc_le_eq card_gt_0_iff) blast
  have n1: "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) (V i) = 1" if "i < card E - 1" for i
  proof -
    have "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) (V i) =
        BSR_Rational.dot (v (fst (q i)) (snd (q i))) (v (fst (q i)) (snd (q i)))"
      unfolding V by (rule bridge)
    also have "\<dots> = c (fst (q i)) (snd (q i))" using emb[OF qE[OF that] qE[OF that]] by simp
    also have "\<dots> = 1" by (rule c1[OF qE[OF that] qa[OF that]])
    finally show ?thesis .
  qed
  have o1: "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) (V j) = 0"
    if "i < card E - 1" "j < card E - 1" "i \<noteq> j" for i j
  proof -
    have "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) (V j) =
        BSR_Rational.dot (v (fst (q i)) (snd (q i))) (v (fst (q j)) (snd (q j)))"
      unfolding V by (rule bridge)
    also have "\<dots> = 0" using emb[OF qE[OF that(1)] qE[OF that(2)]] qinj[OF that] by simp
    finally show ?thesis .
  qed
  have o2: "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) W = 0" if "i < card E - 1" for i
  proof -
    have "Seven_Embedding.dot (card (UNIV :: 'r set)) (V i) W =
        BSR_Rational.dot (v (fst (q i)) (snd (q i))) (v (fst a) (snd a))"
      unfolding V W by (rule bridge)
    also have "\<dots> = 0" using emb[OF qE[OF that] a] qa[OF that] by simp
    finally show ?thesis .
  qed
  have nw: "Seven_Embedding.dot (card (UNIV :: 'r set)) W W = 7"
  proof -
    have "Seven_Embedding.dot (card (UNIV :: 'r set)) W W =
        BSR_Rational.dot (v (fst a) (snd a)) (v (fst a) (snd a))"
      unfolding W by (rule bridge)
    also have "\<dots> = 7" using emb[OF a a] c7 by simp
    finally show ?thesis .
  qed
  show ?thesis by (rule seven_embedding[OF one n1 o1 o2 nw])
qed

end
