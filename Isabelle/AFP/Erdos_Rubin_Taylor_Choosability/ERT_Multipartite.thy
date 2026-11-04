theory ERT_Multipartite
  imports ERT_Choosability Marriage.Marriage
begin

section \<open>Erdos--Rubin--Taylor 1979: $K_{2,\dots,2}$ is $k$-choosable\<close>

text \<open>Definitions from theory ERT\_Choosability (faithful to formal-conjectures'
@{text Choosable}): vertices are @{term "{..<m}"}, colours are naturals.\<close>

text \<open>The complete multipartite graph with @{term k} parts of size 2: vertex @{term "2*i"} and
@{term "2*i+1"} form part @{term i}; adjacent iff in different parts.\<close>

definition mpart :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "mpart k u v \<longleftrightarrow> u \<noteq> v \<and> u div 2 \<noteq> v div 2 \<and> u < 2 * k \<and> v < 2 * k"

lemma sgraph_mpart: "sgraph (2 * k) (mpart k)"
  unfolding sgraph_def mpart_def by auto

subsection \<open>Generalised statement over a finite set of parts\<close>

lemma sibling: "u div 2 = v div 2 \<Longrightarrow> u \<noteq> v \<Longrightarrow>
    (u = 2 * (v div 2) \<and> v = 2 * (v div 2) + 1) \<or> (v = 2 * (v div 2) \<and> u = 2 * (v div 2) + 1)"
  for u v :: nat
  by arith

lemma part_cases: "v = 2 * (v div 2) \<or> v = 2 * (v div 2) + 1"
  for v :: nat
  by arith

lemma gen:
  fixes n :: nat
  shows "\<And>(P::nat set) (L::nat \<Rightarrow> nat set). finite P \<Longrightarrow> card P = n \<Longrightarrow>
    (\<forall>v. v div 2 \<in> P \<longrightarrow> finite (L v) \<and> n \<le> card (L v)) \<Longrightarrow>
    \<exists>c::nat \<Rightarrow> nat. (\<forall>v. v div 2 \<in> P \<longrightarrow> c v \<in> L v) \<and>
      (\<forall>u v. u div 2 \<in> P \<longrightarrow> v div 2 \<in> P \<longrightarrow> u div 2 \<noteq> v div 2 \<longrightarrow> c u \<noteq> c v)"
proof (induction n)
  case 0
  hence "P = {}" by simp
  thus ?case by auto
next
  case (Suc n)
  note fin = Suc.prems(1) and cardP = Suc.prems(2) and hL = Suc.prems(3)
  show ?case
  proof (cases "\<exists>i\<in>P. L (2 * i) \<inter> L (2 * i + 1) \<noteq> {}")
    case True
    then obtain i x where iP: "i \<in> P" and xa: "x \<in> L (2 * i)" and xb: "x \<in> L (2 * i + 1)"
      by blast
    define P' where "P' = P - {i}"
    define L' where "L' v = L v - {x}" for v
    have fin': "finite P'" using fin by (simp add: P'_def)
    have card': "card P' = n" using fin iP cardP by (simp add: P'_def card_Diff_singleton)
    have hL': "\<forall>v. v div 2 \<in> P' \<longrightarrow> finite (L' v) \<and> n \<le> card (L' v)"
    proof (intro allI impI)
      fix v assume "v div 2 \<in> P'"
      hence "v div 2 \<in> P" by (simp add: P'_def)
      with hL have fv: "finite (L v)" and cv: "Suc n \<le> card (L v)" by auto
      have "card (L v) - 1 \<le> card (L v - {x})" by (simp add: card_Diff_singleton_if fv)
      thus "finite (L' v) \<and> n \<le> card (L' v)" using fv cv by (auto simp add: L'_def)
    qed
    from Suc.IH[OF fin' card' hL'] obtain c' where
      c1: "\<forall>v. v div 2 \<in> P' \<longrightarrow> c' v \<in> L' v" and
      c2: "\<forall>u v. u div 2 \<in> P' \<longrightarrow> v div 2 \<in> P' \<longrightarrow> u div 2 \<noteq> v div 2 \<longrightarrow> c' u \<noteq> c' v"
      by blast
    define c where "c v = (if v div 2 = i then x else c' v)" for v
    have in1: "\<And>v. v div 2 \<in> P \<Longrightarrow> c v \<in> L v"
    proof -
      fix v assume vP: "v div 2 \<in> P"
      show "c v \<in> L v"
      proof (cases "v div 2 = i")
        case True
        from part_cases[of v] show ?thesis
        proof
          assume "v = 2 * (v div 2)" thus ?thesis using True xa by (simp add: c_def)
        next
          assume "v = 2 * (v div 2) + 1" thus ?thesis using True xb by (simp add: c_def)
        qed
      next
        case False
        hence "v div 2 \<in> P'" using vP by (simp add: P'_def)
        thus ?thesis using c1 False by (auto simp add: c_def L'_def)
      qed
    qed
    have ne: "\<And>w. w div 2 \<noteq> i \<Longrightarrow> w div 2 \<in> P \<Longrightarrow> c w \<noteq> x"
    proof -
      fix w assume "w div 2 \<noteq> i" "w div 2 \<in> P"
      hence "w div 2 \<in> P'" by (simp add: P'_def)
      with c1 have "c' w \<in> L' w" by blast
      thus "c w \<noteq> x" using \<open>w div 2 \<noteq> i\<close> by (auto simp add: c_def L'_def)
    qed
    have prp: "\<And>u v. u div 2 \<in> P \<Longrightarrow> v div 2 \<in> P \<Longrightarrow> u div 2 \<noteq> v div 2 \<Longrightarrow> c u \<noteq> c v"
    proof -
      fix u v assume uP: "u div 2 \<in> P" and vP: "v div 2 \<in> P" and uv: "u div 2 \<noteq> v div 2"
      show "c u \<noteq> c v"
      proof (cases "u div 2 = i")
        case True
        hence "v div 2 \<noteq> i" using uv by simp
        from ne[OF this vP] True show ?thesis by (simp add: c_def)
      next
        case False
        hence F1: "u div 2 \<noteq> i" .
        show ?thesis
        proof (cases "v div 2 = i")
          case True
          from ne[OF F1 uP] True show ?thesis by (simp add: c_def)
        next
          case False
          hence F2: "v div 2 \<noteq> i" .
          have "u div 2 \<in> P'" "v div 2 \<in> P'" using uP vP F1 F2 by (auto simp add: P'_def)
          from c2[rule_format, OF this uv] show ?thesis using F1 F2 by (simp add: c_def)
        qed
      qed
    qed
    show ?thesis using in1 prp by blast
  next
    case False
    hence dis: "\<And>i. i \<in> P \<Longrightarrow> L (2 * i) \<inter> L (2 * i + 1) = {}" by blast
    define I where "I = {v. v div 2 \<in> P}"
    have Isub: "I \<subseteq> (\<Union>i\<in>P. {2 * i, 2 * i + 1})"
    proof
      fix v assume "v \<in> I"
      hence "v div 2 \<in> P" by (simp add: I_def)
      thus "v \<in> (\<Union>i\<in>P. {2 * i, 2 * i + 1})" using part_cases[of v] by auto
    qed
    have cardI: "card I \<le> 2 * Suc n"
    proof -
      have "card I \<le> card (\<Union>i\<in>P. {2 * i, 2 * i + 1})"
        using Isub fin by (intro card_mono) auto
      also have "\<dots> \<le> (\<Sum>i\<in>P. card {2 * i, 2 * i + 1})" using fin by (rule card_UN_le)
      also have "\<dots> \<le> (\<Sum>i\<in>P. 2)" by (intro sum_mono) (simp add: card_insert_le)
      also have "\<dots> = 2 * Suc n" using cardP by simp
      finally show ?thesis .
    qed
    have finI: "finite I"
    proof (rule finite_subset[OF Isub])
      show "finite (\<Union>i\<in>P. {2 * i, 2 * i + 1})" using fin by simp
    qed
    have finL: "\<forall>v\<in>I. finite (L v)" using hL by (auto simp add: I_def)
    have hall: "\<forall>J\<subseteq>I. card J \<le> card (\<Union>(L ` J))"
    proof clarify
      fix J assume JI: "J \<subseteq> I"
      have finJ: "finite J" using JI finI by (rule finite_subset)
      have finU: "finite (\<Union>(L ` J))" using JI finL finJ by (auto intro: finite_UN_I)
      show "card J \<le> card (\<Union>(L ` J))"
      proof (cases "\<exists>u\<in>J. \<exists>v\<in>J. u \<noteq> v \<and> u div 2 = v div 2")
        case True
        then obtain u v where uJ: "u \<in> J" and vJ: "v \<in> J" and uv: "u \<noteq> v" and ud: "u div 2 = v div 2"
          by blast
        have vP: "v div 2 \<in> P" using vJ JI by (auto simp add: I_def)
        have uP: "u div 2 \<in> P" using uJ JI by (auto simp add: I_def)
        have dsj: "L u \<inter> L v = {}"
          using sibling[OF ud uv] dis[OF vP] by (auto simp add: Int_commute)
        have fu: "finite (L u)" and fv: "finite (L v)" "Suc n \<le> card (L v)" "Suc n \<le> card (L u)"
          using hL uP vP by auto
        have "card (L u \<union> L v) = card (L u) + card (L v)"
          using dsj fu fv by (intro card_Un_disjoint) auto
        hence "2 * Suc n \<le> card (L u \<union> L v)" using fv by simp
        also have "\<dots> \<le> card (\<Union>(L ` J))"
          using uJ vJ finU by (intro card_mono) auto
        finally have "2 * Suc n \<le> card (\<Union>(L ` J))" .
        moreover have "card J \<le> card I" using JI finI by (intro card_mono)
        ultimately show ?thesis using cardI by linarith
      next
        case False
        hence inj: "inj_on (\<lambda>v. v div 2) J" by (auto simp add: inj_on_def)
        have img: "(\<lambda>v. v div 2) ` J \<subseteq> P" using JI by (auto simp add: I_def)
        have "card J = card ((\<lambda>v. v div 2) ` J)" using inj by (simp add: card_image)
        also have "\<dots> \<le> card P" using img fin by (intro card_mono)
        finally have cJ: "card J \<le> Suc n" using cardP by simp
        show ?thesis
        proof (cases "J = {}")
          case True thus ?thesis by simp
        next
          case False
          then obtain v where vJ: "v \<in> J" by blast
          hence "v div 2 \<in> P" using JI by (auto simp add: I_def)
          with hL have "Suc n \<le> card (L v)" by blast
          moreover have "card (L v) \<le> card (\<Union>(L ` J))"
            using vJ finU by (intro card_mono) auto
          ultimately show ?thesis using cJ by linarith
        qed
      qed
    qed
    from marriage_HV[OF finI finL hall] obtain R where
      R1: "\<forall>i\<in>I. R i \<in> L i" and R2: "inj_on R I" by blast
    have "\<forall>v. v div 2 \<in> P \<longrightarrow> R v \<in> L v" using R1 by (simp add: I_def)
    moreover have "\<forall>u v. u div 2 \<in> P \<longrightarrow> v div 2 \<in> P \<longrightarrow> u div 2 \<noteq> v div 2 \<longrightarrow> R u \<noteq> R v"
    proof (intro allI impI)
      fix u v assume "u div 2 \<in> P" "v div 2 \<in> P" "u div 2 \<noteq> v div 2"
      hence "u \<in> I" "v \<in> I" "u \<noteq> v" by (auto simp add: I_def)
      with R2 show "R u \<noteq> R v" by (auto simp add: inj_on_def)
    qed
    ultimately show ?thesis by blast
  qed
qed

subsection \<open>The theorem\<close>

theorem ert_multipartite: "choosable (2 * k) (mpart k) k"
  unfolding choosable_def
proof (intro allI impI)
  fix L :: "nat \<Rightarrow> nat set"
  assume hL: "\<forall>v<2 * k. finite (L v) \<and> card (L v) = k"
  have "\<forall>v. v div 2 \<in> {..<k} \<longrightarrow> finite (L v) \<and> k \<le> card (L v)"
    using hL by auto
  from gen[OF finite_lessThan _ this] obtain c where
    c1: "\<forall>v. v div 2 \<in> {..<k} \<longrightarrow> c v \<in> L v" and
    c2: "\<forall>u v. u div 2 \<in> {..<k} \<longrightarrow> v div 2 \<in> {..<k} \<longrightarrow> u div 2 \<noteq> v div 2 \<longrightarrow> c u \<noteq> c v"
    by auto
  show "\<exists>c. (\<forall>v<2 * k. c v \<in> L v) \<and> (\<forall>u v. mpart k u v \<longrightarrow> c u \<noteq> c v)"
  proof (intro exI[of _ c] conjI allI impI)
    fix v assume "v < 2 * k"
    hence "v div 2 \<in> {..<k}" by auto
    thus "c v \<in> L v" using c1 by blast
  next
    fix u v assume "mpart k u v"
    hence "u div 2 \<noteq> v div 2" "u div 2 \<in> {..<k}" "v div 2 \<in> {..<k}"
      by (auto simp add: mpart_def)
    thus "c u \<noteq> c v" using c2 by blast
  qed
qed

end
