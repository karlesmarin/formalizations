(*  Title:      IL_Iso.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Iso
  imports IL_Count
begin

lemma iso_char:
  assumes ok: "okc cs" and a: "a \<in> Vc cs"
  shows "(\<forall>b. \<not> Ec cs a b) \<longleftrightarrow> (\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1)"
proof
  assume H: "\<forall>b. \<not> Ec cs a b"
  have lt: "fst a < length cs" and ka: "snd a < snd (cs ! fst a)" using a by (auto simp: Vc_mem)
  have pos: "1 \<le> snd (cs ! fst a)" by (rule okc_pos[OF ok lt])
  show "\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1"
  proof (rule ccontr)
    assume N: "\<not> (\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1)"
    show False
    proof (cases "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)")
      case True
      let ?b = "(fst a, nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a))"
      have "T0 cs a ?b \<noteq> 0" using True lt unfolding T0_nz by simp
      hence "Ec cs a ?b" unfolding Ec_def by blast
      thus False using H by blast
    next
      case False
      hence cyn: "\<not> fst (cs ! fst a)" and ge: "snd (cs ! fst a) \<le> snd a + 1"
        using ka unfolding hn_def by auto
      have m1: "snd (cs ! fst a) \<noteq> 1" using N cyn by simp
      have m2: "2 \<le> snd (cs ! fst a)" by (rule nat_ge2[OF pos m1])
      have k1: "1 \<le> snd a" using ge m2 by arith
      let ?b = "(fst a, snd a - 1)"
      have h: "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd ?b)" using cyn ka k1 unfolding hn_def by simp
      have "snd a = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd ?b)" using cyn k1 unfolding nxt_def by simp
      hence "T0 cs ?b a \<noteq> 0" using h lt unfolding T0_nz by simp
      hence "Ec cs a ?b" unfolding Ec_def by blast
      thus False using H by blast
    qed
  qed
next
  assume C: "\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1"
  have lt: "fst a < length cs" and ka: "snd a < snd (cs ! fst a)" using a by (auto simp: Vc_mem)
  have ka0: "snd a = 0" using C ka by simp
  show "\<forall>b. \<not> Ec cs a b"
  proof
    fix b show "\<not> Ec cs a b"
    proof
      assume "Ec cs a b"
      thus False unfolding Ec_def
      proof
        assume "T0 cs a b \<noteq> 0"
        hence "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)" unfolding T0_nz by blast
        thus False using C ka0 unfolding hn_def by simp
      next
        assume y: "T0 cs b a \<noteq> 0"
        hence y': "fst b = fst a" "snd a = nxt (fst (cs ! fst b)) (snd (cs ! fst b)) (snd b)"
          unfolding T0_nz by auto
        have e: "fst b = fst a" by (rule y'(1))
        have "snd a = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd b)" using y'(2) unfolding e .
        thus False using C ka0 unfolding nxt_def by simp
      qed
    qed
  qed
qed

lemma nz_Cz:
  assumes ok: "okc cs"
  shows "lgraph.nz (Vc cs) (Ec cs) = card (Cz cs)"
proof -
  interpret g: lgraph "Vc cs" "Ec cs" by (rule lgraph_Vc[OF ok])
  have "g.isoset = (SIGMA c:Cz cs. {..<snd (cs ! c)})"
  proof (rule set_eqI)
    fix a :: "nat \<times> nat"
    obtain c k where p: "a = (c, k)" by (cases a) auto
    show "a \<in> g.isoset \<longleftrightarrow> a \<in> (SIGMA c:Cz cs. {..<snd (cs ! c)})"
    proof
      assume h: "a \<in> g.isoset"
      hence aV: "a \<in> Vc cs" and H: "\<forall>b. \<not> Ec cs a b" unfolding g.isoset_def by auto
      from iso_char[OF ok aV] H have C: "\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1" by blast
      show "a \<in> (SIGMA c:Cz cs. {..<snd (cs ! c)})"
        using aV C p unfolding Cz_def Vc_mem by auto
    next
      assume h: "a \<in> (SIGMA c:Cz cs. {..<snd (cs ! c)})"
      hence aV: "a \<in> Vc cs" and C: "\<not> fst (cs ! fst a) \<and> snd (cs ! fst a) = 1"
        using p unfolding Cz_def Vc_mem by auto
      from iso_char[OF ok aV] C have "\<forall>b. \<not> Ec cs a b" by blast
      thus "a \<in> g.isoset" unfolding g.isoset_def using aV by simp
    qed
  qed
  hence "g.nz = card (SIGMA c:Cz cs. {..<snd (cs ! c)})" unfolding g.nz_def by simp
  also have "\<dots> = (\<Sum>c\<in>Cz cs. snd (cs ! c))"
    by (subst card_SigmaI) (simp_all add: Cz_def)
  also have "\<dots> = (\<Sum>c\<in>Cz cs. 1)" by (rule sum.cong) (auto simp: Cz_def)
  finally show ?thesis by simp
qed

end
