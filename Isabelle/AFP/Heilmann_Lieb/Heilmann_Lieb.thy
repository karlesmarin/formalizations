(*  Title:      Heilmann_Lieb.thy
    Author:     Carles Marín

The Heilmann--Lieb theorem: the matching polynomial of a finite graph has only real roots.
*)

theory Heilmann_Lieb
  imports Matching_Polynomial Cone_Step
begin

lemma del1_del1: "del1 (del1 E v) u = del2 E u v"
  unfolding del1_def del2_def by auto

lemma mu_empty: "graph {} E \<Longrightarrow> mu {} E = 1"
proof -
  assume G: "graph {} E"
  have "E = {}"
  proof (rule ccontr)
    assume "E \<noteq> {}"
    then obtain e where "e \<in> E" by blast
    then have "card e = 2" "e \<subseteq> {}" using G unfolding graph_def by blast+
    then show False by simp
  qed
  then have "matchings E = {{}}" unfolding matchings_def matching_def by (auto simp: pairwise_def)
  then show ?thesis unfolding mu_def by simp
qed

lemma hl_step:
  assumes G: "graph V E" and w: "w \<in> V"
    and IH: "\<exists>rs. mu (V - {w}) (del1 E w) = lin_prod rs \<and> length rs = card (V - {w}) \<and>
           (\<forall>u\<in>V - {w}. in_cone (mu (V - {w} - {u}) (del1 (del1 E w) u)) rs)"
  shows "\<exists>ts. mu V E = lin_prod ts \<and> length ts = card V \<and> in_cone (mu (V - {w}) (del1 E w)) ts"
proof -
  obtain rs where rs: "mu (V - {w}) (del1 E w) = lin_prod rs" "length rs = card (V - {w})"
    and cn: "\<forall>u\<in>V - {w}. in_cone (mu (V - {w} - {u}) (del1 (del1 E w) u)) rs"
    using IH by blast
  have fV: "finite V" using G by (simp add: graph_def)
  have fN: "finite (nbrs E w)" using nbrs_sub[OF G w] fV finite_subset by blast
  have S: "in_cone (\<Sum>u\<in>nbrs E w. mu (V - {u, w}) (del2 E u w)) rs"
  proof (rule in_cone_sum[OF fN])
    fix u assume u: "u \<in> nbrs E w"
    then have uV: "u \<in> V - {w}" using nbrs_sub[OF G w] by blast
    have "V - {w} - {u} = V - {u, w}" by auto
    then show "in_cone (mu (V - {u, w}) (del2 E u w)) rs"
      using cn uV del1_del1[of E w u] by metis
  qed
  obtain ts where ts: "length ts = Suc (length rs)"
    "[:0, 1:] * lin_prod rs - (\<Sum>u\<in>nbrs E w. mu (V - {u, w}) (del2 E u w)) = lin_prod ts"
    "in_cone (lin_prod rs) ts"
    using cone_step[OF S] by blast
  have pos: "0 < card V" using w fV card_gt_0_iff by blast
  have "card (V - {w}) = card V - 1" using w fV by (simp add: card_Diff_singleton)
  then have len: "length ts = card V" using ts(1) rs(2) pos by simp
  have "mu V E = [:0, 1:] * mu (V - {w}) (del1 E w) - (\<Sum>u\<in>nbrs E w. mu (V - {u, w}) (del2 E u w))"
    by (rule mu_recurrence[OF G w])
  also have "\<dots> = lin_prod ts" using rs(1) ts(2) by simp
  finally have m: "mu V E = lin_prod ts" .
  show ?thesis using m len ts(3) rs(1) by metis
qed

text \<open>The strong form, proved by induction on the number of vertices: the matching polynomial is a product of
  real linear factors, and deleting any vertex gives a polynomial in the cone of its roots.\<close>

theorem heilmann_lieb_strong:
  assumes "graph V E"
  shows "\<exists>rs. mu V E = lin_prod rs \<and> length rs = card V \<and>
           (\<forall>v\<in>V. in_cone (mu (V - {v}) (del1 E v)) rs)"
  using assms
proof (induction "card V" arbitrary: V E rule: less_induct)
  case less
  have G: "graph V E" using less.prems .
  show ?case
  proof (cases "V = {}")
    case True
    then show ?thesis using mu_empty G by (intro exI[of _ "[]"]) simp
  next
    case False
    have fV: "finite V" using G by (simp add: graph_def)
    have step: "\<And>w. w \<in> V \<Longrightarrow> \<exists>ts. mu V E = lin_prod ts \<and> length ts = card V \<and>
        in_cone (mu (V - {w}) (del1 E w)) ts"
    proof -
      fix w assume w: "w \<in> V"
      have pos: "0 < card V" using w fV card_gt_0_iff by blast
      have lt: "card (V - {w}) < card V" using w fV pos by (simp add: card_Diff_singleton)
      have "\<exists>rs. mu (V - {w}) (del1 E w) = lin_prod rs \<and> length rs = card (V - {w}) \<and>
           (\<forall>u\<in>V - {w}. in_cone (mu (V - {w} - {u}) (del1 (del1 E w) u)) rs)"
        by (rule less.hyps[OF lt graph_del1[OF G]])
      then show "\<exists>ts. mu V E = lin_prod ts \<and> length ts = card V \<and>
          in_cone (mu (V - {w}) (del1 E w)) ts"
        by (rule hl_step[OF G w])
    qed
    obtain v0 where v0: "v0 \<in> V" using False by blast
    obtain ts0 where t0: "mu V E = lin_prod ts0" "length ts0 = card V" using step[OF v0] by blast
    show ?thesis
    proof (rule exI[of _ ts0], intro conjI)
      show "mu V E = lin_prod ts0" by (rule t0(1))
      show "length ts0 = card V" by (rule t0(2))
      show "\<forall>v\<in>V. in_cone (mu (V - {v}) (del1 E v)) ts0"
      proof
        fix w assume w: "w \<in> V"
        obtain tw where tw: "mu V E = lin_prod tw" "in_cone (mu (V - {w}) (del1 E w)) tw"
          using step[OF w] by blast
        have "mset tw = mset ts0" using mset_eq_of_lin_prod_eq[of tw ts0] tw(1) t0(1) by simp
        then show "in_cone (mu (V - {w}) (del1 E w)) ts0" using in_cone_perm tw(2) by blast
      qed
    qed
  qed
qed

lemma lin_factor_times: "[:a, 1:] * (p::'a::comm_ring_1 poly) = pCons 0 p + smult a p"
  by (simp add: mult_pCons_left smult_1_left)

lemma poly_map_lin_prod:
  "poly (map_poly complex_of_real (lin_prod rs)) z = prod_list (map (\<lambda>r. z - complex_of_real r) rs)"
proof (induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  let ?p = "lin_prod rs"
  have h: "map_poly complex_of_real ([:-r, 1:] * ?p)
      = pCons 0 (map_poly complex_of_real ?p) + smult (- complex_of_real r) (map_poly complex_of_real ?p)"
    unfolding lin_factor_times
    by (rule poly_eqI) (simp add: coeff_map_poly coeff_pCons coeff_smult split: nat.splits)
  have "poly (map_poly complex_of_real (lin_prod (r # rs))) z
      = poly (pCons 0 (map_poly complex_of_real ?p) + smult (- complex_of_real r) (map_poly complex_of_real ?p)) z"
    using h by simp
  also have "\<dots> = (z - complex_of_real r) * poly (map_poly complex_of_real ?p) z"
    by (simp add: poly_pCons algebra_simps)
  finally show ?case using Cons.IH by simp
qed

theorem heilmann_lieb:
  assumes "graph V E" and "poly (map_poly complex_of_real (mu V E)) z = 0"
  shows "z \<in> \<real>"
proof -
  obtain rs where "mu V E = lin_prod rs" using heilmann_lieb_strong[OF assms(1)] by blast
  then have "prod_list (map (\<lambda>r. z - complex_of_real r) rs) = 0"
    using assms(2) poly_map_lin_prod by simp
  then obtain r where "z - complex_of_real r = 0" unfolding prod_list_zero_iff by auto
  then have "z = complex_of_real r" by simp
  then show ?thesis by simp
qed

end
