theory Cell_Normalization
imports Algebras_of_Cells Locales_For_Macintyre
begin

locale one_val_point_cell = padic_fields + 
  fixes \<C> a b c \<phi> m f
  assumes f_closed: "f \<in> carrier (UP (SA m))"
  assumes \<phi>_Unit: "\<phi> \<in> Units (SA m)"
  assumes \<C>_cell: "is_cell_condition \<C>"
  assumes \<C>_eq: "\<C> = Cond m b c \<phi> \<phi> closed_interval"
  assumes a_def: "a = taylor_expansion (SA m) c f"
  assumes b_nonempty: "b \<noteq> {}"

locale refined_one_val_point_cell = one_val_point_cell + 
  fixes inds :: "nat set"
  assumes inds_memE: "\<And> j. j \<in> inds \<Longrightarrow> a j \<in> Units (SA m)"
  assumes inds_non_memE: "\<And> j. j \<notin> inds \<Longrightarrow> a j = \<zero>\<^bsub>SA m\<^esub>"
  assumes inds_nonempty: "inds \<noteq> {}"

locale cell_normalization = refined_one_val_point_cell + 
  fixes i\<^sub>0 :: nat
  assumes i\<^sub>0_min: "\<And> j t x. t#x \<in> condition_to_set \<C> 
                            \<Longrightarrow> val ((a i\<^sub>0 x)\<otimes>(t \<ominus> c x)[^]i\<^sub>0) \<le> val ((a j x)\<otimes>(t \<ominus> c x)[^]j)"

context padic_fields
begin

definition center_term where
"center_term m c = (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). hd x) \<ominus>\<^bsub>SA (Suc m)\<^esub> (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). c (tl x))"

lemma center_term_closed:
  assumes "c \<in> carrier (SA m)"
  shows "center_term m c \<in> carrier (SA (Suc m))"
  unfolding center_term_def 
  apply(rule UPSA.R.ring_simprules) 
   apply(rule restrict_in_SA_car, rule hd_is_semialg_function, blast)
  using assms tl_comp_in_SA by blast
  
lemma center_term_eval:
  assumes "c \<in> carrier (SA m)"
  assumes "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "center_term m c xs = hd xs \<ominus> c (tl xs)"
  using SA_minus_eval[of "(\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). hd x)" "Suc m" "\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). c (tl x)" xs] 
        restrict_apply assms restrict_in_SA_car hd_is_semialg_function tl_comp_in_SA
  unfolding center_term_def 
  by (metis (mono_tags) zero_less_Suc)


text\<open>The function $a(x)(t - c(x))^i$ is semialgebraic in $m+1$ variables when
     the functions $c(x)$ and $a(x)$ are semialgebraic in $m$ variables:\<close>

definition monom_center_term where 
"monom_center_term m a c i = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). a (tl x)) \<otimes>\<^bsub>SA (Suc m)\<^esub> (center_term m c)[^]\<^bsub>SA (Suc m)\<^esub>(i::nat)"

lemma monom_center_term_closed: 
  assumes "a \<in> carrier (SA m)"
  assumes "c \<in> carrier (SA m)"
  shows "monom_center_term m a c i \<in> carrier (SA (Suc m))"
  unfolding monom_center_term_def 
  by(rule R.ring_simprules, rule tl_comp_in_SA, rule assms,
          rule R.nat_pow_closed, rule center_term_closed, rule assms) 

lemma monom_center_term_eval:
  assumes "a \<in> carrier (SA m)"
  assumes "c \<in> carrier (SA m)"
  assumes "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "monom_center_term m a c i xs = a (tl xs) \<otimes> (hd xs \<ominus> c (tl xs))[^]i"
  using tl_comp_in_SA[of a m] restrict_apply assms
        center_term_closed[of c m] center_term_eval[of c m xs ]SA_mult monom_center_term_def
  by (smt SA_nat_pow)

definition normal_cell where 
"normal_cell m b =  Cond m b (\<zero>\<^bsub>SA m\<^esub>) (\<one>\<^bsub>SA m\<^esub>) (\<one>\<^bsub>SA m\<^esub>) closed_interval"

lemma normal_cell_cell_cond: 
  assumes "is_semialgebraic m b"
  shows "is_cell_condition (normal_cell m b)"
  unfolding normal_cell_def 
  apply(rule is_cell_conditionI', rule assms, blast, blast, blast)
  unfolding is_convex_condition_def by blast 

lemma normal_cell_memI:
  assumes "is_semialgebraic m b"
  assumes "x \<in> b"
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "val t = 0"
  shows "t#x \<in> condition_to_set (normal_cell m b)"
proof- 
  have 0: "\<one>\<^bsub>SA m\<^esub> x = \<one>"
    using assms is_semialgebraic_closed SA_oneE by blast
  have 1: "\<zero>\<^bsub>SA m\<^esub> x = \<zero>"
    using assms is_semialgebraic_closed SA_zeroE by blast
  have 2: "val (t \<ominus> \<zero>) = 0"
  proof- 
    have 0: "t \<ominus> \<zero> = t"
      by(rule Qp.minus_zero, rule assms)
    show ?thesis unfolding 0 by(rule assms)
  qed
  show ?thesis 
  unfolding normal_cell_def condition_to_set.simps cell_def mem_Collect_eq 
  apply(rule conjI, rule Qp_pow_ConsI, rule assms)
  using is_semialgebraic_closed assms apply blast
  apply(rule conjI) unfolding list_tl apply(rule assms)
  apply(rule closed_interval_memI)
  unfolding  list_hd 0 1 2 val_one 
   apply blast by blast
qed

lemma normal_cell_memE:
  assumes "is_semialgebraic m b"
  assumes  "t#x \<in> condition_to_set (normal_cell m b)" 
  shows  "t \<in> carrier Q\<^sub>p"
         "val t = 0"
         "x \<in> b"
proof- 
  have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms unfolding normal_cell_def condition_to_set.simps cell_def by blast 
  show t_closed: "t \<in> carrier Q\<^sub>p"
    using tx_closed 
    by (metis Qp_pow_ConsE list_hd)
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using tx_closed Qp_pow_ConsE list_tl by metis 
  have 0: "\<one>\<^bsub>SA m\<^esub> x = \<one>"
    by(rule SA_oneE, rule x_closed)
  have 1: "\<zero>\<^bsub>SA m\<^esub> x = \<zero>"
    by(rule SA_zeroE, rule x_closed)
  have 2: "t \<ominus> \<zero> = t"
    by(rule Qp.minus_zero, rule t_closed)
  have 3: "val t \<le> 0"
    using assms unfolding normal_cell_def condition_to_set.simps
    using cell_memE(3)[of "t#x" m b "\<zero>\<^bsub>SA m\<^esub>" "\<one>\<^bsub>SA m\<^esub>" "\<one>\<^bsub>SA m\<^esub>" closed_interval] 
    unfolding list_tl list_hd 0 1 val_one 2  
    using closed_interval_memE by blast
  have 4: "val t \<ge> 0"
    using assms unfolding normal_cell_def condition_to_set.simps
    using cell_memE(3)[of "t#x" m b "\<zero>\<^bsub>SA m\<^esub>" "\<one>\<^bsub>SA m\<^esub>" "\<one>\<^bsub>SA m\<^esub>" closed_interval] 
    unfolding list_tl list_hd 0 1 val_one 2  
    using closed_interval_memE by blast
  show "val t = 0"
    using 3 4 basic_trans_rules(24) by blast
  show "x \<in> b"
    using assms unfolding normal_cell_def condition_to_set.simps cell_def list_tl list_hd mem_Collect_eq 
    by blast 
qed

end

context one_val_point_cell
begin
  
lemma b_closures: 
"b \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
"is_semialgebraic m b"
"\<And> x. x \<in> b \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  using \<C>_cell is_cell_conditionE''(1) is_semialgebraic_closed unfolding \<C>_eq 
  by auto
 
lemma c_closures: 
"c \<in> carrier (SA m)"
"\<And>x. x \<in> b \<Longrightarrow> c x \<in> carrier Q\<^sub>p"
  using \<C>_cell b_closures SA_car_closed[of c m] unfolding \<C>_eq 
  by (auto simp: is_cell_conditionE''(1) is_semialgebraic_closed)

lemma \<phi>_closures: 
"\<phi> \<in> carrier (SA m)"
"\<And>x. x \<in> b \<Longrightarrow> \<phi> x \<in> carrier Q\<^sub>p"
"\<And>x. x \<in> b \<Longrightarrow> \<phi> x \<noteq> \<zero>"
  using \<phi>_Unit b_closures 
  by (auto simp: SA_Units_memE' SA_Units_closed_fun subset_iff)

lemma c_eval: 
"x \<in> b \<Longrightarrow> c x \<in> carrier Q\<^sub>p"
  apply(intro SA_car_closed[of _ m], auto simp: c_closures)
  using  b_closures(1) by auto 

lemma \<C>_nontrivial: 
  "condition_to_set \<C> \<noteq> {}"
  "\<And> x. x \<in> b \<Longrightarrow> (\<phi> x \<oplus> c x)#x \<in> condition_to_set \<C>"
  "\<exists> t x. t#x \<in> condition_to_set \<C>"
proof- 
  show "\<And>x. x \<in> b \<Longrightarrow> (\<phi> x \<oplus> c x)#x \<in> condition_to_set \<C>"
  proof- 
    fix x assume x_def: "x \<in> b" 
    obtain t where t_def: "t = \<phi> x \<oplus> c x"
      by blast 
    have t_closed: "t \<in> carrier Q\<^sub>p"
      unfolding t_def using \<phi>_closures c_eval x_def by auto 
    have 0: "t \<ominus> c x = \<phi> x"
      unfolding t_def using x_def \<phi>_closures c_eval 
      by (simp add: Qp.add.inv_solve_right' a_minus_def)
    have "t#x \<in> condition_to_set \<C>"
      unfolding \<C>_eq condition_to_set.simps cell_def mem_Collect_eq 
                list_tl list_hd closed_interval_def 0 
      apply(intro conjI) 
      apply (meson Qp_pow_ConsI b_closures(1) subset_iff t_closed x_def)
      using x_def by auto 
    thus "(\<phi> x \<oplus> c x) # x \<in> condition_to_set \<C>"
      using t_def by auto 
  qed
  thus "\<exists> t x. t#x \<in> condition_to_set \<C>" 
    using b_nonempty by auto 
  thus "condition_to_set \<C> \<noteq> {}"
    by auto 
qed

lemma a_closed: 
"a \<in> carrier (UP (SA m))"
"a i \<in> carrier (SA m)"
  using f_closed c_closures UPSA.taylor_closed cfs_closed
  unfolding  a_def UPSA.taylor_def by auto 
 
lemma \<C>_memE:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "t \<in> carrier Q\<^sub>p"
        "x \<in> b"
        "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        "val (t \<ominus> c x) = val (\<phi> x)"
        "t \<ominus> c x \<in> carrier Q\<^sub>p"
        "t \<ominus> c x \<noteq> \<zero>"
proof- 
  show 0: "t \<in> carrier Q\<^sub>p"  "x \<in> b"   "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"  "val (t \<ominus> c x) = val (\<phi> x)"
    using assms cartesian_power_head[of "t#x" Q\<^sub>p m ] cartesian_power_tail[of "t#x" Q\<^sub>p m ]
    unfolding \<C>_eq condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd closed_interval_def
    by auto  
  show "t \<ominus> c x \<in> carrier Q\<^sub>p" "t \<ominus> c x \<noteq> \<zero>"
    using 0 \<phi>_Unit \<phi>_closures Qp.cring_simprules(4) c_eval unfolding val_def 
    by auto 
qed

lemma \<C>_memI:
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "x \<in> b"
  assumes "val (t \<ominus> c x) = val (\<phi> x)"
  shows "t#x \<in> condition_to_set \<C>"
  unfolding \<C>_eq condition_to_set.simps 
  apply(rule cell_memI, unfold list_tl list_hd closed_interval_def mem_Collect_eq assms) 
  using assms Qp_pow_ConsI assms(1) assms(2) b_closures(3) by auto 

lemma a_deg: "deg (SA m) a = deg (SA m) f"
  unfolding a_def 
  using UPSA.taylor_def UPSA.taylor_deg c_closures f_closed by presburger

end

context refined_one_val_point_cell
begin

lemma inds_closures:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "\<And> i. a i x \<in> carrier Q\<^sub>p"
        "\<And> i. i \<in> inds \<Longrightarrow> a i x \<noteq> \<zero>"
        "\<And> i. i \<in> inds \<Longrightarrow> a i x \<otimes> (t \<ominus> c x)[^]i \<noteq> \<zero>"
        "\<And> i. i \<in> inds \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = ord (a i x \<otimes> (t \<ominus> c x)[^]i)"
        "\<And> i. i \<in> inds \<Longrightarrow> ord (a i x \<otimes> (t \<ominus> c x)[^]i) = ord (a i x) + i* ord(t \<ominus> c x)"
        "\<And> i. i \<notin> inds \<Longrightarrow> a i x = \<zero>"
        "\<And> i. i \<notin> inds \<Longrightarrow> a i x \<otimes> (t \<ominus> c x)[^]i = \<zero>"
        "\<And> i. i \<notin> inds \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = \<infinity>"
proof-
  have 0: "t \<in> carrier Q\<^sub>p" "x \<in> b" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "val (t \<ominus> c x) = val (\<phi> x)"
        "t \<ominus> c x \<in> carrier Q\<^sub>p"  "t \<ominus> c x \<noteq> \<zero>"
    using assms  \<C>_memE by auto 
  show 1: "\<And> i. a i x \<in> carrier Q\<^sub>p"
    using a_closed SA_car_closed 0 by auto 
  show 2: "\<And> i. i \<in> inds \<Longrightarrow> a i x \<noteq> \<zero>"
    using inds_memE 0 SA_Units_memE' by blast
  show 3: "\<And> i. i \<in> inds \<Longrightarrow> a i x \<otimes> (t \<ominus> c x)[^]i \<noteq> \<zero>"
    using 0 1 2 by (meson Qp.integral Qp.nat_pow_closed Qp.nonzero_pow_nonzero)
  show "\<And> i. i \<in> inds \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = ord (a i x \<otimes> (t \<ominus> c x)[^]i)"
    using 3 val_def by auto 
  show "\<And> i. i \<in> inds \<Longrightarrow> ord (a i x \<otimes> (t \<ominus> c x)[^]i) = ord (a i x) + i* ord(t \<ominus> c x)"
    by (smt 0 2 3 ord_mult 1 Qp.nat_pow_nonzero Qp.not_nonzero_memE nonzero_nat_pow_ord)
  show 4: "\<And> i. i \<notin> inds \<Longrightarrow> a i x = \<zero>"
    using inds_non_memE 0 SA_zeroE by presburger
  show  "\<And> i. i \<notin> inds \<Longrightarrow> a i x \<otimes> (t \<ominus> c x)[^]i = \<zero>"
    unfolding 4 using 0 by auto 
  thus "\<And> i. i \<notin> inds \<Longrightarrow> val (a i x \<otimes> (t \<ominus> c x)[^]i) = \<infinity>"
    using val_def by auto 
qed

lemma inds_closures2:
  assumes "x \<in> b" 
  shows "\<And> i. a i x \<in> carrier Q\<^sub>p"
        "\<And> i. i \<in> inds \<Longrightarrow> a i x \<noteq> \<zero>"
        "\<And> i. i \<notin> inds \<Longrightarrow> a i x = \<zero>"
  using SA_car_closed[of _ m] inds_memE b_closures(3) SA_Units_memE'[of _ m] 
        inds_non_memE  a_closed  SA_Units_closed assms SA_zeroE by auto   

lemma f_nonzero: "f \<noteq> \<zero>\<^bsub>UP (SA m)\<^esub>"
proof(rule ccontr)
  assume A: "\<not> f \<noteq> \<zero>\<^bsub>UP (SA m)\<^esub>"
  hence 0: "a = \<zero>\<^bsub>UP (SA m)\<^esub>"
    unfolding a_def 
    by (metis UPSA.P.add.right_cancel UPSA.UP_l_zero UPSA.taylor_expansion_add a_def c_closures
        f_closed local.a_closed(1))
  hence 1: "\<And> j. a j = \<zero>\<^bsub>SA m\<^esub>" 
    by simp
  have 2: "\<zero>\<^bsub>SA m\<^esub> \<notin> Units (SA m)"
  proof- 
    obtain x where x_def: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using Qp_n_nonempty by fastforce
    have " \<zero>\<^bsub>SA m\<^esub> x = \<zero>"
      using SA_zeroE x_def by auto 
    thus ?thesis using SA_Units_memE' x_def by auto 
  qed
  show False 
    using inds_nonempty inds_memE 2 unfolding 1 by auto 
qed

lemma deg_f_inds:
"deg (SA m) f \<in> inds"
proof- 
  have "f (deg (SA m) f) \<noteq> \<zero>\<^bsub>SA m\<^esub>"
    using f_nonzero f_closed 
    by (metis UPSA.deg_ltrm UPSA.deg_zero UPSA.ltrm_deg_0 UPSA.monom_zero)
  thus ?thesis 
    using f_nonzero inds_non_memE[of "deg (SA m) f"] inds_nonempty a_def  
    by (smt (z3) Collect_empty_eq Collect_mem_eq SA_units_not_zero UPSA.cfs_zero UPSA.deg_ltrm
        UPSA.deg_zero UPSA.monom_zero UPSA.zcf_degree_zero UPSA.zcf_zero_degree_zero a_deg 
        inds_memE local.a_closed(1))
qed

lemma to_Qp_deg: 
"\<And> x. x \<in> b \<Longrightarrow> deg Q\<^sub>p (SA_poly_to_Qp_poly m x f) = deg (SA m) f"
proof- 
  fix x assume A: "x \<in> b"
  have 0: "(SA_poly_to_Qp_poly m x f) (deg (SA m) f) = f (deg (SA m) f) x"
    using A b_closures 
    by (simp add: SA_poly_to_Qp_poly_coeff f_closed)
  have 1: "(SA_poly_to_Qp_poly m x a) (deg (SA m) f) = a (deg (SA m) f) x"
    using A b_closures 
    by (simp add: SA_poly_to_Qp_poly_coeff a_closed)
  have 2: "SA_poly_to_Qp_poly m x a = taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f)"
    unfolding a_def 
    by (simp add: A SA_poly_to_Qp_poly_taylor_poly b_closures(3) c_closures f_closed)
  have 3: "(SA_poly_to_Qp_poly m x a) (deg (SA m) f) \<noteq> \<zero>"
    unfolding 1 using deg_f_inds A b_closures inds_closures2(2) by presburger
  have 4: "deg Q\<^sub>p (SA_poly_to_Qp_poly m x a) = (deg (SA m) a)"
    apply(intro UPQ.deg_eqI SA_poly_to_Qp_poly_closed b_closures A
                SA_poly_to_Qp_poly_deg_bound a_closed )
    using 3 unfolding a_deg by auto 
  have 5: "deg Q\<^sub>p (SA_poly_to_Qp_poly m x f) = deg Q\<^sub>p (SA_poly_to_Qp_poly m x a)"
    unfolding 2 
    using A SA_poly_to_Qp_poly_closed UPQ.taylor_def UPQ.taylor_deg b_closures(3) c_eval f_closed by presburger
  show "deg Q\<^sub>p (SA_poly_to_Qp_poly m x f) = deg (SA m) f"
    unfolding 5 4 a_deg by auto 
qed

end


context cell_normalization
begin

lemma i\<^sub>0_inds:
"i\<^sub>0 \<in> inds"
proof- 
  obtain j where j_def: "j \<in> inds"
    using inds_nonempty by auto 
  obtain t x where tx_def: "t#x \<in> condition_to_set \<C>"
    using \<C>_nontrivial by blast
  show ?thesis 
    using i\<^sub>0_min[of t x j] inds_closures(8)[of t x i\<^sub>0] 
          j_def inds_closures[of t x j] tx_def by auto 
qed

definition \<alpha> where \<alpha>_def:
"\<alpha> = inv\<^bsub>SA m\<^esub> a i\<^sub>0 \<otimes>\<^bsub>SA m\<^esub> \<phi> [^]\<^bsub>SA m\<^esub> - int i\<^sub>0"

lemma \<alpha>_closure: 
"\<alpha> \<in> carrier (SA m)"
"\<alpha> \<in> Units (SA m)"
  unfolding \<alpha>_def 
  using \<phi>_Unit inds_memE R.Units_inverse R.Units_m_closed R.int_pow_unit_closed 
      SA_Units_closed i\<^sub>0_inds apply presburger
  by (simp add: R.Units_int_pow_closed \<phi>_Unit i\<^sub>0_inds inds_memE)

definition g where g_def: 
"g = \<alpha> \<odot>\<^bsub>UP (SA m)\<^esub> compose (SA m) a (up_ring.monom (UP (SA m)) \<phi> 1)"

definition g' where g'_def: 
"g' = pderiv m g"

lemma \<phi>_monom_closed: 
  "compose (SA m) a (up_ring.monom (UP (SA m)) \<phi> 1) \<in> carrier (UP (SA m))"
  apply(intro sub_closed) using  \<phi>_Unit a_closed by auto 

lemma g_closed: "g \<in> carrier (UP (SA m))"
  unfolding g_def 
  by(intro UPSA.smult_closed \<alpha>_closure \<phi>_monom_closed)

definition \<beta> where \<beta>_def: 
"\<beta> j = \<phi> [^]\<^bsub>SA m\<^esub> (int j - int i\<^sub>0) \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a i\<^sub>0"

lemma \<beta>_closures: "\<beta> j \<in> carrier (SA m)" "\<beta> j \<in> Units (SA m)"
  unfolding \<beta>_def 
  by (auto simp: SA_Units_closed R.Units_int_pow_closed \<phi>_Unit i\<^sub>0_inds inds_memE)

lemma g_cfs:
"g j = \<alpha> \<otimes>\<^bsub>SA m\<^esub> \<phi> [^]\<^bsub>SA m\<^esub> j \<otimes>\<^bsub>SA m\<^esub> a j"
"g j = (\<phi>[^]\<^bsub>SA m\<^esub>(int j - int i\<^sub>0)) \<otimes>\<^bsub>SA m\<^esub>(a j \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a i\<^sub>0)"
"g j = \<beta> j \<otimes>\<^bsub>SA m\<^esub> a j"
proof- 
  have 0: "g j = \<alpha> \<otimes>\<^bsub>SA m\<^esub> (compose (SA m) a (up_ring.monom (UP (SA m)) \<phi> 1) j)"
    unfolding g_def by(intro cfs_smult \<alpha>_closure \<phi>_monom_closed)
  show 1: "g j = \<alpha> \<otimes>\<^bsub>SA m\<^esub> \<phi> [^]\<^bsub>SA m\<^esub> j \<otimes>\<^bsub>SA m\<^esub> a j"
    unfolding 0 using linear_sub_cfs[of a m \<phi> _ j] \<phi>_Unit a_closed  R.Units_closed
                R.cring_simprules(11) R.nat_pow_closed \<alpha>_closure(1) by presburger
  have R: "\<And> a b c R. \<lbrakk>cring R; a \<in> Units R; b \<in> carrier R; c \<in> Units R\<rbrakk> \<Longrightarrow> 
          inv\<^bsub>R\<^esub> a \<otimes>\<^bsub>R\<^esub> c [^]\<^bsub>R\<^esub> - int i\<^sub>0 \<otimes>\<^bsub>R\<^esub> c [^]\<^bsub>R\<^esub> j \<otimes>\<^bsub>R\<^esub> b =
                           c [^]\<^bsub>R\<^esub> (int j - int i\<^sub>0) \<otimes>\<^bsub>R\<^esub> (b \<otimes>\<^bsub>R\<^esub> inv\<^bsub>R\<^esub> a)"
  proof- 
    fix a b c R assume A: "cring R" "a \<in> Units R" "b \<in> carrier R" " c \<in> Units R"
    interpret L?: cring R  using A by  auto 
    have 0: "c [^]\<^bsub>R\<^esub> (int j - int i\<^sub>0) = c [^]\<^bsub>R\<^esub> j \<otimes>\<^bsub>R\<^esub> c [^]\<^bsub>R\<^esub> - int i\<^sub>0"
      using A  by (metis diff_conv_add_uminus int_pow_int local.int_pow_add)
    have 1: "\<And> x y z w.\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; w \<in> carrier R\<rbrakk>
                    \<Longrightarrow>  x \<otimes>\<^bsub>R\<^esub> y \<otimes>\<^bsub>R\<^esub> z \<otimes>\<^bsub>R\<^esub> w =    z \<otimes>\<^bsub>R\<^esub> y \<otimes>\<^bsub>R\<^esub> (w \<otimes>\<^bsub>R\<^esub> x)" 
      using L.m_assoc L.m_comm by auto 
    show "inv\<^bsub>R\<^esub> a \<otimes>\<^bsub>R\<^esub> c [^]\<^bsub>R\<^esub> - int i\<^sub>0 \<otimes>\<^bsub>R\<^esub> c [^]\<^bsub>R\<^esub> j \<otimes>\<^bsub>R\<^esub> b =
                           c [^]\<^bsub>R\<^esub> (int j - int i\<^sub>0) \<otimes>\<^bsub>R\<^esub> (b \<otimes>\<^bsub>R\<^esub> inv\<^bsub>R\<^esub> a)"
      unfolding 0 apply(rule 1) using A(2,3,4) Units_closed Units_int_pow_closed 
      by auto 
  qed
  show 2: "g j = (\<phi>[^]\<^bsub>SA m\<^esub>(int j - int i\<^sub>0)) \<otimes>\<^bsub>SA m\<^esub>(a j \<otimes>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> a i\<^sub>0)"
    unfolding 1 \<alpha>_def by(intro R inds_memE a_closed i\<^sub>0_inds \<phi>_Unit R.cring) 
  show "g j = \<beta> j \<otimes>\<^bsub>SA m\<^esub> a j"
    unfolding 2 \<beta>_def 
    using R.Units_closed R.Units_int_pow_closed R.m_closed R.m_comm R.m_lcomm SA_Units_inv_closed
            \<phi>_Unit i\<^sub>0_inds inds_memE local.a_closed(2) by presburger
qed

lemma g_cfs_eval: 
"x \<in> b \<Longrightarrow> g j x = (\<phi> x[^](int j - int i\<^sub>0)) \<otimes>(a j x \<otimes> inv (a i\<^sub>0 x))"
  unfolding g_cfs(3) \<beta>_def 
  using SA_mult[of x m "\<beta> j" "a j"] b_closures SA_inv_eval SA_mult SA_unit_int_pow
        \<beta>_def \<phi>_Unit g_cfs(2) g_cfs(3) i\<^sub>0_inds inds_memE 
  by auto

lemma g_deg: 
"deg (SA m) g = deg (SA m) f"
  unfolding g_def 
  using deg_smult linear_sub_deg[of a m \<phi>] a_closed(1)
  unfolding a_def 
  by (metis (no_types, opaque_lifting) R.cring UPSA.deg_smult' UP_cring.taylor_def
      UP_cring.taylor_deg UP_cring_def \<alpha>_closure(2) \<phi>_Unit \<phi>_monom_closed a_def c_closures f_closed)

lemma g_cfs_inds:
  assumes "j \<in> inds"
  shows "g j \<in> Units (SA m)"
  unfolding g_cfs(3) using \<beta>_closures inds_memE assms 
  by (meson R.Units_m_closed)

lemma g_cfs_not_inds: 
  assumes "j \<notin> inds"
  shows "g j = \<zero>\<^bsub>SA m\<^esub>"
  unfolding g_cfs(3) using \<beta>_closures inds_closures
  by (simp add: assms inds_non_memE)

lemma g'_closed:
"pderiv m g \<in> carrier (UP (SA m))"
"g' \<in> carrier (UP (SA m))"
  using g_closed g'_def 
  by (auto simp: UPSA.pderiv_closed)

lemma pderiv_ith_cfs:
"taylor_expansion (SA m) c (UPSA.pderiv m f) j = [Suc j]\<cdot>\<^bsub>SA m\<^esub>taylor_expansion (SA m) c f (Suc j)"
proof- 
  have 0: "taylor_expansion (SA m) c (UPSA.pderiv m f) = pderiv m (taylor_expansion (SA m) c f)"
    using UPSA.taylor_expansion_pderiv_comm c_closures f_closed by presburger
  show ?thesis unfolding 0 
    apply(rule pderiv_cfs)
  using a_def local.a_closed by presburger
qed

lemma to_Qp_g_cfs:
  "x \<in> b \<Longrightarrow> SA_poly_to_Qp_poly m x g j = g j x"
  by (meson  b_closures SA_poly_to_Qp_poly_coeff basic_trans_rules(31) g_closed)

lemma g_closures: 
  assumes "x \<in> b"
  shows "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
        "g j x \<in> carrier Q\<^sub>p" "g j x = (\<beta> j x) \<otimes> a j x"
    apply(intro SA_poly_to_Qp_poly_closed g_closed b_closures assms
                , intro SA_car_closed[of "g j" m] b_closures cfs_closed g_closed assms)
  unfolding g_cfs(3) 
  using SA_mult assms b_closures(3) by force

lemma g_cfs_inds_eval: 
  assumes "x \<in> b"
  assumes "j \<in> inds"
  shows "g j x \<noteq> \<zero>"
        "SA_poly_to_Qp_poly m x g j \<noteq> \<zero>"
   apply (meson SA_Units_memE' assms(1) assms(2) b_closures g_cfs_inds subsetD)
  by (metis (no_types, lifting) SA_Units_memE' assms(1) assms(2) b_closures g_cfs_inds in_mono to_Qp_g_cfs)

lemma g_cfs_not_inds_eval: 
  assumes "x \<in> b"
  assumes "j \<notin> inds"
  shows "g j x = \<zero>"
        "SA_poly_to_Qp_poly m x g j = \<zero>"
   using SA_zeroE assms(1) assms(2) b_closures g_cfs_not_inds to_Qp_g_cfs by auto

lemma g_cf_val_inds: "\<And>x j. x \<in> b \<Longrightarrow> j \<in> inds \<Longrightarrow> val (g j x) \<ge> 0"
proof- fix x j assume A: "x \<in> b" "j \<in> inds"
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A b_closures by blast 
  have 0: "g j x = (\<phi> x[^](int j - int i\<^sub>0)) \<otimes>(a j x \<otimes> inv (a i\<^sub>0 x) )"
    using g_cfs_eval A by auto 
  have 1:"\<phi> x \<in> Units Q\<^sub>p"
    using \<phi>_Unit x_closed SA_Units_nonzero Units_eq_nonzero by blast
  have 2: "(\<phi> x[^](int j - int i\<^sub>0)) = (\<phi> x[^]int j) \<otimes> inv (\<phi> x[^] int i\<^sub>0)"
    using 1 
    by (metis Qp.int_pow_add Qp.int_pow_inv' add_uminus_conv_diff)
  have 3: "a j x \<in> Units Q\<^sub>p"
    using inds_memE x_closed SA_Units_nonzero 
    unfolding Units_eq_nonzero 
    by (meson A(2))
  have 4: "a i\<^sub>0 x \<in> Units Q\<^sub>p"
    using inds_memE  x_closed SA_Units_nonzero i\<^sub>0_inds
    unfolding Units_eq_nonzero 
    by (meson A(2))
  have 5: "ord (g j x) = (int j - int i\<^sub>0)*ord(\<phi> x) + ord (a j x) - ord (a i\<^sub>0 x)"
    unfolding 0 using 1 3 4 Qp.Units_int_pow_closed Qp.Units_inv_Units Qp.Units_m_closed 
      Units_eq_nonzero int_pow_ord ord_fract ord_mult by force
  have 6: "ord (g j x) = (int j*ord(\<phi> x) + ord (a j x)) - (int i\<^sub>0*ord(\<phi> x) + ord (a i\<^sub>0 x))"
    unfolding 5 using left_diff_distrib' by auto
  obtain t where t_def: "t = \<phi> x \<oplus> c x"
    by blast 
  have tx_closed: "t#x \<in> condition_to_set \<C>"
    unfolding t_def using \<C>_nontrivial A by auto 
  have 7: "ord(\<phi> x) = ord (t \<ominus> c x)"
    using tx_closed 1 Units_eq_nonzero \<C>_memE(4) \<C>_memE(5) equal_val_imp_equal_ord(1) by force
  have 6: "ord (g j x) \<ge> 0"
    unfolding 6 7 
    using tx_closed  A(2) eint_ord_code(1) i\<^sub>0_inds i\<^sub>0_min[of t x j] 
          inds_closures(4)[of t x i\<^sub>0] inds_closures(4)[of t x j] 
          inds_closures(5)[of t x i\<^sub>0] inds_closures(5)[of t x j]
    by auto 
  thus "val (g j x) \<ge> 0"
    using g_cfs val_ord 
    by (metis A(1) A(2) eint_defs(1) eint_ord_code(1) g_cfs_inds_eval(1) val_def)
qed

lemma g_cf_val: "\<And>x j. x \<in> b \<Longrightarrow> val (g j x) \<ge> 0"
  using g_cf_val_inds g_cfs_not_inds_eval val_zero 
  by (metis eint_ord_simps(3))

lemma g_integral: "g \<in> integral_on m b"
  apply(rule integral_on_memI)
  using g_closed apply blast
  apply(rule val_ring_memI)
  apply (simp add: g_closures(2) to_Qp_g_cfs)
  using to_Qp_g_cfs g_cf_val by auto 

lemma g'_integral: "g' \<in> integral_on m b"
proof(intro integral_on_memI g'_closed)
  fix x i assume A: "x \<in> b"
  have 0: "SA_poly_to_Qp_poly m x g' i = g' i x"
    using g'_closed A b_closures SA_poly_to_Qp_poly_coeff by presburger
  have 1: "g' i x = [Suc i]\<cdot>(g (Suc i) x)"
    unfolding g'_def pderiv_def poly_shift_def n_mult_def 
    by (metis A R.zero_closed SA_Units_closed SA_add_pow_apply b_closures(3) g_cfs_inds g_cfs_not_inds)
  show "SA_poly_to_Qp_poly m x g' i \<in> \<O>\<^sub>p"
    unfolding 0 1 using g_integral integral_on_memE 
    by (metis A g_closures(2) nat_add_pow_mult_assoc to_Qp_g_cfs
        val_ring_nat_inc_closed val_ring_times_closed)
qed

lemma g_cfs_integral:
  assumes "x \<in> b"
  shows "g j x \<in> \<O>\<^sub>p"
        "SA_poly_to_Qp_poly m x g j \<in> \<O>\<^sub>p"
  apply (metis assms g_integral integral_on_memE(2) to_Qp_g_cfs)
  by (metis assms g_integral integral_on_memE(2))

lemma g'_cfs_integral:
  assumes "x \<in> b"
  shows "SA_poly_to_Qp_poly m x g' j \<in> \<O>\<^sub>p"
        "g' j x \<in> \<O>\<^sub>p"
  apply (metis assms g'_integral integral_on_memE(2))
  using  assms g'_integral integral_on_memE(2) g'_closed b_closures SA_poly_to_Qp_poly_coeff 
  by metis

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>The Change of Variables $u = \frac{t - c(x)}{\varphi(x)}$\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition u where u_def: 
"u = monom_center_term m (inv\<^bsub>SA m\<^esub> \<phi>) c 1"

lemma u_closed: "u \<in> carrier (SA (Suc m))"
  unfolding u_def by(rule monom_center_term_closed, auto simp: \<phi>_Unit c_closures)

lemma u_eval_car:
  assumes "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "u(t#x) = inv (\<phi> x) \<otimes> (t \<ominus> c x)"
proof- 
  have 0: "monom_center_term m (inv\<^bsub>SA m\<^esub> \<phi>) c 1 (t # x) = (inv\<^bsub>SA m\<^esub> \<phi>) x \<otimes> (t \<ominus> c x) [^] (1::nat)"
    using assms monom_center_term_eval[of "inv\<^bsub>SA m\<^esub> \<phi>" m c "t#x" 1 ] c_closures
    unfolding u_def  list_tl list_hd 
    using SA_Units_inv_closed \<phi>_Unit by presburger
  show ?thesis unfolding 0 u_def  
    by (metis (no_types, lifting) Qp.minus_closed Qp.nat_pow_eone SA_car_closed SA_inv_eval 
        \<phi>_Unit assms c_closures(1) cartesian_power_head cartesian_power_tail list.sel(1) list.sel(3))
qed

lemma u_eval:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "u(t#x) = inv (\<phi> x) \<otimes> (t \<ominus> c x)"
  apply(rule u_eval_car)
  using assms unfolding \<C>_eq condition_to_set.simps cell_def by auto 

definition u_inv where u_inv_def: 
"u_inv = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). \<phi> (tl x)) \<otimes>\<^bsub>SA (Suc m)\<^esub>(\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). hd x) \<oplus>\<^bsub>SA (Suc m)\<^esub> (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). c (tl x))"

lemma u_inv_closed: "u_inv \<in> carrier (SA (Suc m))"
  unfolding u_inv_def 
  apply(rule UPSA.R.ring_simprules, rule UPSA.R.ring_simprules)
    apply(intro tl_comp_in_SA \<phi>_closures)
  using  hd_is_semialg_function restrict_in_SA_car zero_less_Suc apply presburger
    by(intro tl_comp_in_SA c_closures)

lemma u_inv_eval_car: 
  assumes "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "u_inv (t#x) = \<phi> x \<otimes> t \<oplus> (c x)"
  unfolding u_inv_def using assms SA_mult SA_add by auto 

lemma u_inv_eval:
  assumes "t#x \<in> condition_to_set (normal_cell m b)"
  shows "u_inv (t#x) = \<phi> x \<otimes> t \<oplus> (c x)"
  apply(rule u_inv_eval_car)
  using assms 
  by (meson Qp_pow_ConsI b_closures(2) b_closures(3) normal_cell_memE(1) normal_cell_memE(3))

lemma u_maps_to_normal_cell: 
  assumes "t#x \<in> condition_to_set \<C>"
  shows "(u(t#x)#x) \<in> condition_to_set (normal_cell m b)"
proof(intro normal_cell_memI b_closures \<C>_memE[of t] assms SA_car_closed[of u "Suc m"] u_closed )
  show "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms 
    by (simp add: Qp_pow_ConsI \<C>_memE(1) \<C>_memE(2) b_closures(3))
  have 0: "u(t#x) = inv (\<phi> x) \<otimes> (t \<ominus> c x)"
    using assms u_eval by auto 
  have 1: "ord (u(t#x)) = ord(inv (\<phi> x)) +  ord (t \<ominus> c x)"
    unfolding 0 using assms 
    by (meson Qp_funs_Units_memE(3) SA_Units_Qp_funs_Units \<C>_memE(2) \<C>_memE(3) \<C>_memE(5) \<C>_memE(6)
        \<phi>_Unit \<phi>_closures(2) inv_in_frac(3) not_nonzero_Qp ord_mult)
  have 2:  "ord (u(t#x)) = 0"
    unfolding 1 using assms \<C>_memE(2) \<C>_memE(4) \<C>_memE(5) \<C>_memE(6) \<phi>_closures(2) \<phi>_closures(3) ord_of_inv val_ord' 
    by auto
  show "val (u (t # x)) = 0"
    unfolding val_def 2 
    by (metis "0" Qp.integral Qp.nonzero_memE(1) Qp.nonzero_memE(2) Qp_funs_Units_memE(3)
        SA_Units_Qp_funs_Units \<C>_memE(2) \<C>_memE(3) \<C>_memE(5) \<C>_memE(6) \<phi>_Unit \<phi>_closures(2) 
        assms eint_0 inv_in_frac(3))
qed

lemma u_inv_u:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "u_inv(u(t#x)#x) = t"
  using u_inv_eval[of "u(t#x)" x] u_eval[of t x] assms 
  by (metis (no_types, lifting) Qp.add.inv_solve_right Qp.m_comm \<C>_memE(1) \<C>_memE(2) \<C>_memE(5)
      \<phi>_closures(2) \<phi>_closures(3) a_minus_def c_closures(2) inv_in_frac(1) local.fract_cancel_right 
      not_nonzero_Qp u_maps_to_normal_cell)

lemma u_inv_u_car:
  assumes "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "u_inv(u(t#x)#x) = t"
  using u_inv_eval_car[of "u(t#x)" x] u_eval_car[of t x] assms 
  by (metis (no_types, lifting) Qp.add.inv_solve_right Qp.m_comm Qp.minus_closed 
      Qp.not_nonzero_memE Qp_funs_Units_memE(3) Qp_pow_ConsE(2) Qp_pow_ConsI SA_Units_Qp_funs_Units
      SA_car_closed \<phi>_Unit \<phi>_closures(1) a_minus_def c_closures(1) cartesian_power_tail 
      field_inv(3) list.sel(1) list.sel(3) local.fract_cancel_right u_closed)

lemma u_inv_maps_to_\<C>: 
  assumes "s#x \<in> condition_to_set (normal_cell m b)"
  shows "(u_inv(s#x)#x) \<in> condition_to_set \<C>"
proof(rule  \<C>_memI)
  show 0: "u_inv (s # x) \<in> carrier Q\<^sub>p" "x \<in> b"
    apply(intro SA_car_closed[of u_inv "Suc m"] u_inv_closed)
    using assms unfolding normal_cell_def condition_to_set.simps cell_def by auto 
  have 1: " u_inv (s # x) \<ominus> c x = \<phi> x \<otimes> s"
    using u_inv_eval assms 
    by (metis (no_types, lifting) "0"(1) "0"(2) Qp.add.inv_solve_right Qp.m_closed \<phi>_closures(2)
        a_minus_def b_closures(2) c_eval normal_cell_memE(1))
  show " val (u_inv (s # x) \<ominus> c x) = val (\<phi> x)"
    unfolding 1 using normal_cell_memE 0 assms \<phi>_closures(2) b_closures(2) val_mult by auto
qed

lemma u_u_inv:
  assumes "s#x \<in> condition_to_set (normal_cell m b)"
  shows "u(u_inv(s#x)#x) = s"
  using u_eval[of "u_inv(s#x)" x] u_inv_eval[of s x] assms u_inv_maps_to_\<C>
  by (metis (no_types, lifting) Qp.add.inv_solve_right Qp.inv_cancelR(1) Qp.m_closed 
      Units_eq_nonzero \<C>_memE(1) \<C>_memE(2) \<phi>_closures(2) \<phi>_closures(3) a_minus_def b_closures(2)
      c_closures(2) normal_cell_memE(1) not_nonzero_Qp)

lemma u_u_inv_car:
  assumes "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "u(u_inv(s#x)#x) = s"
proof- 
  have 0: "u (u_inv (s # x) # x) = inv \<phi> x \<otimes> ((\<phi> x \<otimes> s \<oplus> c x) \<ominus> c x)"
    using u_eval_car[of "u_inv(s#x)" x] u_inv_eval_car[of s x] assms 
    by (metis Qp.add.m_closed Qp.m_closed Qp_pow_ConsE(2) Qp_pow_ConsI SA_car_closed 
        \<phi>_closures(1) c_closures(1) cartesian_power_tail list.sel(1) list.sel(3))
  have sx_closed: "s \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms  Qp_pow_ConsE[of "s#x" ] list_hd list_tl  by auto    
  have 1: "(\<phi> x \<otimes> s \<oplus> c x) \<ominus> c x = \<phi> x \<otimes> s"
    using sx_closed SA_car_closed assms 
    using Qp.add.inv_solve_right' Qp.cring_simprules(15) \<phi>_closures(1) c_closures(1) by force
  show ?thesis
    using sx_closed SA_car_closed assms
    unfolding 0 1 
    by (metis Qp.cring_simprules(11) Qp.cring_simprules(12) SA_Units_memE' \<phi>_Unit \<phi>_closures(1)
        field_inv(1) inv_in_frac(1))
qed

lemma g_eval_u_car:
  assumes "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)) =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
        "(SA_poly_to_Qp_poly m x f \<bullet> t) = inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)))"
proof- 
  obtain s where s_def: "s = u(t#x)"
    by blast 
  have s_normal: "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding s_def assms 
    by (metis Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) assms cartesian_power_tail list.sel(3) u_closed)
  have x_closures: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using s_normal by (metis cartesian_power_tail list.sel(3))
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using SA_car_closed assms s_def u_closed by presburger
  obtain g0 where g0_def: "g0 = Cring_Poly.compose (SA m) a (up_ring.monom (UP (SA m)) \<phi> 1)"
    by blast 
  have g0_closed: "g0 \<in> carrier (UP (SA m))"
    unfolding g0_def using \<phi>_monom_closed by force
  have to_Qp_g0: "SA_poly_to_Qp_poly m x g0 = 
              Cring_Poly.compose Q\<^sub>p (taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f))
                                     (up_ring.monom (UP Q\<^sub>p) (\<phi> x) 1)"
  proof- 
    have 0: "SA_poly_to_Qp_poly m x g0 = 
          Cring_Poly.compose Q\<^sub>p (SA_poly_to_Qp_poly m x a) 
                      (SA_poly_to_Qp_poly m x (up_ring.monom (UP (SA m)) \<phi> 1))"
      apply(unfold g0_def, rule SA_poly_to_Qp_poly_sub[of a m "(up_ring.monom (UP (SA m)) \<phi> 1)" x ])
      using a_closed \<phi>_closures x_closures by auto 
    have 1: "(SA_poly_to_Qp_poly m x (up_ring.monom (UP (SA m)) \<phi> 1)) = 
                                                    up_ring.monom (UP Q\<^sub>p) (\<phi> x) 1"
      using SA_poly_to_Qp_poly_monom[of x m \<phi> 1] \<phi>_closures(1) x_closures by fastforce
    have 2: "(SA_poly_to_Qp_poly m x (taylor_expansion (SA m) c f)) =
                               taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f)"
      using f_closed c_closures x_closures SA_poly_to_Qp_poly_taylor_poly by auto 
    show ?thesis unfolding 0 1 2 a_def by blast 
  qed
  have to_Qp_g: "SA_poly_to_Qp_poly m x g = \<alpha> x \<odot>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x g0"
    unfolding g_def using  g0_def x_closures g_closures 
    by (meson SA_poly_to_Qp_poly_smult \<alpha>_closure(1) \<phi>_monom_closed)
  have g0_eval: "SA_poly_to_Qp_poly m x g0 \<bullet> s = SA_poly_to_Qp_poly m x f \<bullet> t"
  proof- 
    have 0: "SA_poly_to_Qp_poly m x g0 \<bullet> s = 
            (taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f)) \<bullet>
                     ((up_ring.monom (UP Q\<^sub>p) (\<phi> x) 1) \<bullet> s) "
      unfolding to_Qp_g0 
      using SA_car_closed SA_poly_to_Qp_poly_closed UPQ.taylor_closed UPQ.taylor_def UPQ.to_fun_sub 
        \<phi>_closures(1) c_eval f_closed s_closed x_closures(1) x_closures  c_closures(1) by auto
    have 1: "(up_ring.monom (UP Q\<^sub>p) (\<phi> x) 1) \<bullet> s = \<phi> x \<otimes> s"
      by (metis Qp.nat_pow_eone SA_car_closed UPQ.to_fun_monom \<phi>_closures(1) assms
                cartesian_power_tail list.sel(3) s_closed)
    have 2:  "\<phi> x \<otimes> s = t \<ominus> c x"
      unfolding s_def using u_eval[of t x] assms 
      by (metis Qp.add.inv_solve_right Qp.cring_simprules(1) Qp.m_closed SA_car_closed 
                \<phi>_closures(1) a_minus_def c_closures(1) s_closed s_def s_normal u_inv_eval_car 
                u_inv_u_car x_closures)
    show ?thesis 
      unfolding 0 1 2 
      by (metis SA_poly_to_Qp_poly_closed UPQ.taylor_def UPQ.taylor_eval' \<C>_cell \<C>_eq assms 
          cartesian_power_head f_closed is_cell_condition_closure'(1) list.sel(1) x_closures)
  qed
  have 0: "(\<alpha> x \<odot>\<^bsub>UP Q\<^sub>p\<^esub> SA_poly_to_Qp_poly m x g0) \<bullet> s = \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
    using g0_eval 
    using SA_car_closed SA_poly_to_Qp_poly_closed UPQ.to_fun_smult \<alpha>_closure(1) g0_closed 
      s_closed x_closures by presburger
  show a: "SA_poly_to_Qp_poly m x g \<bullet> u (t # x) = \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
    unfolding to_Qp_g using 0 s_def by auto 
  show  "(SA_poly_to_Qp_poly m x f \<bullet> t) = inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)))"
    unfolding a using assms \<alpha>_closure 
    by (metis Qp.inv_cancelR(1) SA_Units_nonzero SA_car_closed SA_poly_to_Qp_poly_closed 
        UPQ.to_fun_closed Units_eq_nonzero a cell_normalization.g_closed cell_normalization_axioms 
        g0_closed g0_eval s_closed u_closed x_closures)
qed

lemma g_eval_u:
  assumes "t#x \<in> condition_to_set \<C>"
  shows "SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)) =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
        "(SA_poly_to_Qp_poly m x f \<bullet> t) = inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)))"
proof- have 0: "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by(meson Qp_pow_ConsI \<C>_memE(1) \<C>_memE(3) assms)
  thus "SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)) =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
        "(SA_poly_to_Qp_poly m x f \<bullet> t) = inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)))"
    using g_eval_u_car by auto 
qed

lemma g_eval_s_car:
  assumes "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "SA_poly_to_Qp_poly m x g \<bullet> s =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x)))"
        "(SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x))) =  inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> s)"
proof- 
  obtain t where t_def: " t = u_inv(s#x)"
    by blast 
  have 0: "SA_poly_to_Qp_poly m x g \<bullet> (u(t#x)) =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> t)"
    apply(intro g_eval_u_car, unfold t_def) 
    by (metis Qp_pow_ConsI SA_car_closed assms cartesian_power_tail list.sel(3) u_inv_closed)
  thus 1: "SA_poly_to_Qp_poly m x g \<bullet> s =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x)))" 
    unfolding t_def using assms u_u_inv_car by force
  show "(SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x))) =  inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> s)"
    unfolding 1 using assms 0 g_eval_u_car(2) t_def 
    by (metis Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) cartesian_power_tail 
        list.sel(3) u_inv_closed)
qed

lemma g_eval_s:
  assumes "s#x \<in> condition_to_set (normal_cell m b)"
  shows "SA_poly_to_Qp_poly m x g \<bullet> s =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x)))"
        "(SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x))) =  inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> s)"
proof- 
  have 0: "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by (meson assms Qp_pow_ConsI b_closures(2) b_closures(3) normal_cell_memE(1) normal_cell_memE(3))
  show "SA_poly_to_Qp_poly m x g \<bullet> s =
                   (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x)))"
        "(SA_poly_to_Qp_poly m x f \<bullet> (u_inv(s#x))) =  inv (\<alpha> x) \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> s)"
    using 0 g_eval_s_car by auto 
qed


lemma (in UP_cring) taylor_smult:
  assumes "f \<in> carrier P"
  assumes "c \<in> carrier R"
  assumes "a \<in> carrier R"
  shows "taylor c (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub> taylor c f"
  unfolding taylor_def taylor_expansion_def 
  by(intro sub_smult[of ] X_plus_closed assms)

abbreviation(input) mon where
"mon \<equiv> up_ring.monom (UP (SA m))"

abbreviation(input) cmp where
"cmp \<equiv> compose (SA m)"

abbreviation(input) ev_poly where
"ev_poly \<equiv> SA_poly_to_Qp_poly m"

lemma g_taylor_term:
  assumes "s \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "d \<in> carrier (SA m)"
  assumes "t = u_inv(s#x)"
  assumes "e = \<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c"
  shows "UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s =
            \<alpha> x \<otimes> (UPQ.taylor_term (e x) (SA_poly_to_Qp_poly m x f) i \<bullet> t)"
        "UPQ.taylor_term (e x) (SA_poly_to_Qp_poly m x f) i \<bullet> t  = 
               inv \<alpha> x \<otimes> (UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s)"
proof- 
  have Qp_closures: "e \<in> carrier (SA m)" "t \<in> carrier Q\<^sub>p" "\<phi> x \<in> Units Q\<^sub>p" "\<phi> x \<in> carrier Q\<^sub>p" "s \<in> carrier Q\<^sub>p"
                 "inv \<phi> x \<in> Units Q\<^sub>p" "inv \<phi> x \<in> carrier Q\<^sub>p" "\<alpha> x \<in> Units Q\<^sub>p" "\<alpha> x \<in> carrier Q\<^sub>p" "c x \<in> carrier Q\<^sub>p" "d \<in> carrier (SA m)"
                 "d x \<in> carrier Q\<^sub>p" "UPSA.taylor m e f i x \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  proof- 
    show 0: "e \<in> carrier (SA m)" 
      unfolding assms(5)  using \<phi>_closures(1) assms(3) c_closures(1) by blast
    show 1: "t \<in> carrier Q\<^sub>p" "\<phi> x \<in> Units Q\<^sub>p" "inv \<phi> x \<in> Units Q\<^sub>p" 
         "\<alpha> x \<in> Units Q\<^sub>p" "c x \<in> carrier Q\<^sub>p" "d x \<in> carrier Q\<^sub>p" 
         "UPSA.taylor m e f i x \<in> carrier Q\<^sub>p" 
      using assms Qp_pow_ConsI SA_car_closed u_inv_closed apply presburger
      using Qp.UnitsI(2) SA_Units_closed_fun SA_Units_memE' \<phi>_Unit assms(2) field_inv(1) field_inv(3) 
        apply meson
      using SA_Units_memE' SA_car_closed Units_eq_nonzero \<phi>_Unit \<phi>_closures(1) assms(2)
          inv_in_frac(3) apply presburger   
      using SA_Units_nonzero Units_eq_nonzero \<alpha>_closure(2) assms(2) apply presburger
      using SA_car_closed assms(2) c_closures(1)  SA_car_closed assms(2) assms(3) apply auto 
      by(intro SA_car_closed[of _ m] cfs_closed, intro  taylor_closed f_closed assms 0, auto) 
    show "s \<in> carrier Q\<^sub>p"  "d \<in> carrier (SA m)" " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using assms by auto 
    show "\<phi> x \<in> carrier Q\<^sub>p" "inv \<phi> x \<in> carrier Q\<^sub>p" "\<alpha> x \<in> carrier Q\<^sub>p"
      using 1 by auto 
  qed
  have poly_closures: "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
                      "SA_poly_to_Qp_poly m x f \<in> carrier (UP Q\<^sub>p)"
                      "\<And>j. mon \<phi> j \<in> carrier (UP (SA m))"
                      "\<And>j. mon e j \<in> carrier (UP (SA m))"
                      "\<And>j. mon \<one>\<^bsub>SA m\<^esub> j \<in> carrier (UP (SA m))"
                      "taylor m d g \<in> carrier (UP (SA m))"
                      "taylor m e f \<in> carrier (UP (SA m))"
    using  SA_poly_to_Qp_poly_closed g_closed f_closed Qp_closures taylor_closed \<phi>_closures
    by auto 
  have monom_simps: "\<And> f. X_poly_plus (SA m) f = mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon f 0"
                    "\<And> f. to_polynomial (SA m) f = mon f 0"
                    "\<And> a f . taylor m a f = cmp f (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon a 0)"
    unfolding taylor_def taylor_expansion_def X_poly_plus_def X_poly_def to_polynomial_def by auto 
  have 0: "UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s =
            UPQ.taylor (d x) (SA_poly_to_Qp_poly m x g) i \<otimes> (s \<ominus> d x) [^] i"
    by(intro UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x g" s "d x" i ]
             Qp_closures poly_closures ) 
  have 1: "UPQ.taylor (d x) (SA_poly_to_Qp_poly m x g) i =
           SA_poly_to_Qp_poly m x (taylor m d g) i"
    using SA_poly_to_Qp_poly_taylor_poly 
    by (simp add: Qp_closures UPQ.taylor_def UPSA.taylor_def g_closed)
  have 2: "SA_poly_to_Qp_poly m x (taylor m d g) i = taylor m d g i x"
    by (simp add: SA_poly_to_Qp_poly_coeff UPSA.taylor_closed assms(2) assms(3) g_closed)
  have 3: " taylor m d g = \<alpha> \<odot>\<^bsub>UP (SA m)\<^esub> 
              taylor m d (cmp a (mon \<phi> 1))"
    unfolding g_def apply(intro taylor_smult sub_closed)
    by (auto simp add: a_closed \<alpha>_closure assms \<phi>_closures(1)) 
  have 4: "taylor m d (cmp a (mon \<phi> 1)) = 
          cmp a (cmp (mon \<phi> 1) (X_poly_plus (SA m) d))"
    using sub_assoc unfolding monom_simps 
    by (simp add: Qp_closures local.a_closed(1) poly_closures(3))
  have 5: "cmp a (cmp (mon \<phi> 1) (X_poly_plus (SA m) d)) 
            =  cmp f 
                              (cmp (X_poly_plus (SA m) c) 
                                              (cmp (mon \<phi> 1) 
                                                              (X_poly_plus (SA m) d)))"
    unfolding a_def monom_simps using sub_assoc 
    using Qp_closures UPSA.sub_closed UPSA.taylor_def c_closures(1) f_closed 
          monom_simps(3) poly_closures(3) by force
  obtain h where h_def: "h = (cmp (X_poly_plus (SA m) c) 
                                  (cmp (mon \<phi> 1) 
                                       (X_poly_plus (SA m) d)))"
    by blast 
  obtain h0 where h0_def: "h0 =(cmp (mon \<phi> 1) (X_poly_plus (SA m) d))"
    by blast 
  have h_eq: "h = h0 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0"
    unfolding h_def h0_def monom_simps  
    by (smt (z3) R.one_closed P.m_lcomm P.nat_pow_eone X_plus_closed deg_const is_UP_monomE(1) 
                monom_as_mult monom_is_UP_monom(1) sub_add sub_assoc sub_const sub_monom(1) 
                to_poly_closed \<phi>_closures(1) assms(3) c_closures(1) monom_simps(1))    
  have h0_eq1: "h0 = \<phi> \<odot>\<^bsub>UP (SA m)\<^esub> (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon d 0)"
    unfolding h0_def monom_simps 
    using Qp_closures sub_monom_deg_one \<phi>_closures(1) by force
  have h0_eq2: "h0 = mon \<phi> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon (\<phi> \<otimes>\<^bsub>SA m\<^esub> d) 0"
    unfolding h0_eq1 
    by (simp add: monic_monom_smult monom_mult_smult smult_r_distr \<phi>_closures(1) assms(3))
  have h_eq2: "h = mon \<phi> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon (\<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c) 0"
    unfolding h_eq h0_eq2 
    by (simp add: P.a_ac(1) \<phi>_closures(1) assms(3) c_closures(1))
  have 6: "taylor m d g = \<alpha> \<odot>\<^bsub>UP (SA m)\<^esub> cmp f h"
    unfolding 3 4 5 h_def by auto 
  have 7: "cmp f h = cmp (taylor m e f) (mon \<phi> 1)"    
  proof- 
    have a: "cmp (taylor m e f) (mon \<phi> 1) = cmp f (cmp (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon e 0) (mon \<phi> 1))"
      unfolding  h_eq2 monom_simps 
      by (simp add: Qp_closures(1) UPSA.sub_assoc f_closed poly_closures(3))
    have b: "cmp (mon \<one>\<^bsub>SA m\<^esub> 1) (mon \<phi> 1) = mon \<phi> 1"
      using UPSA.sub_monom_deg_one \<phi>_closures(1) by auto
    have c: " cmp (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon e 0) (mon \<phi> 1)   = 
              cmp (mon \<one>\<^bsub>SA m\<^esub> 1) (mon \<phi> 1) \<oplus>\<^bsub>UP (SA m)\<^esub> cmp (mon e 0) (mon \<phi> 1)"
      by (simp add: sub_add  \<phi>_closures(1) Qp_closures)
    have d: " cmp (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon e 0)   
                  (mon \<phi> 1) = mon \<phi> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon e 0"
      unfolding c b  by (simp add: Qp_closures(1) UPSA.sub_const poly_closures(3))
    show ?thesis unfolding a d unfolding h_eq2 assms(5) by auto 
  qed
  have 8: "SA_poly_to_Qp_poly m x (taylor m d g) i = \<alpha> x \<otimes> (cmp (taylor m e f) (mon \<phi> 1)) i x"
    using 2 6 7 SA_mult UPSA.sub_closed \<alpha>_closure(1) assms(2) poly_closures by force
  have 9: "(cmp (taylor m e f) (mon \<phi> 1)) i = (\<phi>[^]\<^bsub>SA m\<^esub> i) \<otimes>\<^bsub>SA m\<^esub> (taylor m e f) i"
    using UPSA.linear_sub_cfs \<phi>_closures(1) poly_closures(7) by blast
  have 10: "SA_poly_to_Qp_poly m x (taylor m d g) i = (\<alpha> x \<otimes> \<phi> x [^]i) \<otimes> (taylor m e f) i x"
  proof- 
    have a: "(\<phi> [^]\<^bsub>SA m\<^esub> i \<otimes>\<^bsub>SA m\<^esub> UPSA.taylor m e f i) x = (\<phi> [^]\<^bsub>SA m\<^esub> i) x \<otimes> (taylor m e f) i x"
      apply(rule SA_mult) by (simp add: assms(2))
    have b: "(\<phi> [^]\<^bsub>SA m\<^esub> i) x  = \<phi> x [^]i"
      by (simp add: SA_nat_pow assms(2))
    have c: "\<alpha> x \<otimes> \<phi> x [^] i \<otimes> UPSA.taylor m e f i x = \<alpha> x \<otimes> (\<phi> x [^] i \<otimes> UPSA.taylor m e f i x)"
      by(intro Qp.m_assoc[of "\<alpha> x" "\<phi> x [^] i" "UPSA.taylor m e f i x"], auto simp: Qp_closures)
    show ?thesis  unfolding 8 9 a b c by auto 
  qed
  have 11: "UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s =
            \<alpha> x \<otimes> \<phi> x [^] i \<otimes> UPSA.taylor m e f i x \<otimes> (s \<ominus> d x) [^] i"
    unfolding 0 1 10 by auto 
  have 13: "s = u (t#x)"
   using u_u_inv_car[of s x] assms Qp_pow_ConsI by blast
  have 14 :"u (t#x) = inv \<phi> x \<otimes> (t \<ominus> c x)"
    apply(rule u_eval_car)
    using assms Qp_pow_ConsI SA_car_closed u_inv_closed by presburger
  have 15: "inv \<phi> x \<otimes> (t \<ominus> c x) \<ominus> d x = inv \<phi> x \<otimes> (t \<ominus> (c x \<oplus> \<phi> x \<otimes> d x))"
  proof -
    have "u_inv (s # x) \<in> carrier Q\<^sub>p"
      by (meson Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) assms u_inv_closed)
    then show ?thesis
      by (smt (z3) Qp.cring_simprules(4) Qp.function_ring_car_memE Qp.inv_cancelR(1) Qp.m_closed 
          Qp.r_minus_distr Qp.right_inv_add Qp_funs_Units_memE(3) SA_Units_Qp_funs_Units 
          SA_car_memE(2) Units_eq_nonzero \<phi>_Unit \<phi>_closures(1) assms c_closures(1) inv_in_frac(1) 
          not_nonzero_Qp)
  qed
  have 16: "c x \<oplus> \<phi> x \<otimes> d x = e x"
    by (simp add: Qp.add.m_comm Qp_closures SA_add SA_mult assms)
  have 17: "(s \<ominus> d x) [^] i = (inv \<phi> x [^] i) \<otimes> (t \<ominus> e x) [^] i"
    using 14 15 16 Qp.nat_pow_distrib Qp_closures Qp_pow_ConsI SA_car_closed assms u_u_inv_car 
    by force
  have 18: "UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s =
           (\<alpha> x \<otimes> \<phi> x [^] i \<otimes> inv \<phi> x [^] i) \<otimes> UPSA.taylor m e f i x \<otimes>  (t \<ominus> e x) [^] i"
    using 11 17  Qp.m_assoc Qp.m_comm Qp_closures SA_car_closed  by auto
  have 19: "(\<alpha> x \<otimes> \<phi> x [^] i \<otimes> inv \<phi> x [^] i) = \<alpha> x"
    by (simp add: Qp.Units_pow_closed Qp.inv_cancelR(1) Qp.m_comm Qp.nat_pow_of_inv Qp_closures)
  have 20: "UPQ.taylor_term (e x) (SA_poly_to_Qp_poly m x f) i \<bullet> t 
            = UPSA.taylor m e f i x \<otimes> (t \<ominus> e x) [^] i"
    using  UPQ.to_fun_taylor_term Qp_closures(1) Qp_closures(2) SA_car_closed 
            SA_poly_to_Qp_poly_taylor_cfs UPQ.taylor_def UPSA.taylor_def assms(2) 
            f_closed poly_closures(2) by presburger
  show "UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s =
    \<alpha> x \<otimes> (UPQ.taylor_term (e x) (SA_poly_to_Qp_poly m x f) i \<bullet> t)"
     unfolding 18 20 19 
     using Qp.m_assoc Qp.minus_closed Qp.nat_pow_closed Qp_closures(1) Qp_closures(13) 
       Qp_closures(14) Qp_closures(2) Qp_closures(9) SA_car_closed by presburger
   thus "UPQ.taylor_term (e x) (SA_poly_to_Qp_poly m x f) i \<bullet> t =
    inv \<alpha> x \<otimes> (UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s)"
     by (metis "20" Qp.cring_simprules(4) Qp.function_ring_car_memE Qp.inv_cancelR(1) Qp.m_closed 
                Qp.nat_pow_closed Qp_closures SA_car_memE(2))
qed

lemma g'_taylor_term:
  assumes "s \<in> carrier Q\<^sub>p"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "t = u_inv(s#x)"
  shows "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i \<bullet> s =
            (\<alpha> x \<otimes> \<phi> x) \<otimes> (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i \<bullet> t)"
proof- 
  have zero: "\<zero>\<^bsub>SA m\<^esub> x = \<zero>"
    using assms SA_zeroE by force
  have Qp_closures: "t \<in> carrier Q\<^sub>p" "\<phi> x \<in> Units Q\<^sub>p" "\<phi> x \<in> carrier Q\<^sub>p" "s \<in> carrier Q\<^sub>p"
                 "inv \<phi> x \<in> Units Q\<^sub>p" "inv \<phi> x \<in> carrier Q\<^sub>p" "\<alpha> x \<in> Units Q\<^sub>p" "\<alpha> x \<in> carrier Q\<^sub>p"
                 "c x \<in> carrier Q\<^sub>p" "c \<in> carrier (SA m)" "c x \<in> carrier Q\<^sub>p" 
                 "UPSA.taylor m c f i x \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  proof- 
    show 1: "t \<in> carrier Q\<^sub>p" "\<phi> x \<in> Units Q\<^sub>p" "inv \<phi> x \<in> Units Q\<^sub>p" 
         "\<alpha> x \<in> Units Q\<^sub>p" "c x \<in> carrier Q\<^sub>p" 
         "UPSA.taylor m c f i x \<in> carrier Q\<^sub>p" 
      using assms Qp_pow_ConsI SA_car_closed u_inv_closed apply presburger
      using Qp.UnitsI(2) SA_Units_closed_fun SA_Units_memE' \<phi>_Unit assms(2) field_inv(1) field_inv(3) 
        apply meson
      using SA_Units_memE' SA_car_closed Units_eq_nonzero \<phi>_Unit \<phi>_closures(1) assms(2)
          inv_in_frac(3) apply presburger   
      using SA_Units_nonzero Units_eq_nonzero \<alpha>_closure(2) assms(2) apply presburger
      using SA_car_closed assms(2) c_closures(1)  SA_car_closed assms(2) assms(3) apply auto 
      by(intro SA_car_closed[of _ m] cfs_closed, intro  taylor_closed f_closed assms zero, auto) 
    show "s \<in> carrier Q\<^sub>p"  " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" " c \<in> carrier (SA m)" " c x \<in> carrier Q\<^sub>p"
         "\<phi> x \<in> carrier Q\<^sub>p" "inv \<phi> x \<in> carrier Q\<^sub>p" "\<alpha> x \<in> carrier Q\<^sub>p"
      using assms c_closures SA_car_closed 1 by auto 
  qed
  have poly_closures: "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
                      "SA_poly_to_Qp_poly m x f \<in> carrier (UP Q\<^sub>p)"
                      "SA_poly_to_Qp_poly m x g' \<in> carrier (UP Q\<^sub>p)"
                      "SA_poly_to_Qp_poly m x (pderiv m f) \<in> carrier (UP Q\<^sub>p)"
                      "\<And>j. mon \<phi> j \<in> carrier (UP (SA m))"
                      "\<And>j. mon c j \<in> carrier (UP (SA m))"
                      "\<And>j. mon \<one>\<^bsub>SA m\<^esub> j \<in> carrier (UP (SA m))"
                      "taylor m \<zero>\<^bsub>SA m\<^esub> g \<in> carrier (UP (SA m))"
                      "taylor m c f \<in> carrier (UP (SA m))"
    using  SA_poly_to_Qp_poly_closed g_closed f_closed Qp_closures taylor_closed \<phi>_closures
            g'_closed pderiv_closed
    by auto
  have c_eq: "c = \<phi> \<otimes>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> \<oplus>\<^bsub>SA m\<^esub> c"
    by (simp add: assms Qp_closures(10) \<phi>_closures(1))
  have 0: "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g) (Suc i) \<bullet> s =
            \<alpha> x \<otimes> (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) (Suc i) \<bullet> t)"
          "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) (Suc i) \<bullet> t  = 
            inv \<alpha> x \<otimes> (UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g) (Suc i) \<bullet> s)"
    using g_taylor_term[of s x "\<zero>\<^bsub>SA m\<^esub>" t c] assms \<phi>_closures c_eq  
    by auto  
  have 1: "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i \<bullet> s =
            UPQ.taylor (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i \<otimes> (s \<ominus> (\<zero>\<^bsub>SA m\<^esub> x)) [^] i"
   by(intro UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x g'" s "\<zero>\<^bsub>SA m\<^esub> x" i ]
                poly_closures Qp_closures, auto simp: zero)
  have 2: "UPQ.taylor (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i = 
            g' i x"
    unfolding zero 
    by (simp add: Qp_closures(13) SA_poly_to_Qp_poly_coeff UPQ.taylor_def 
        UPQ.taylor_expansion_at_zero g'_closed(2) poly_closures(3))
  have 3: "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i \<bullet> s = 
                                    g' i x \<otimes> s [^] i"
    unfolding 1 2 
    using Qp.minus_zero Qp_closures(4) zero by presburger
  have 4: "g' i x = [Suc i] \<cdot> g (Suc i) x"
    using g'_def 
    by (smt (verit, best) Qp_closures(13) R.Units_int_pow_closed R.cring R.m_closed 
        SA_Units_closed SA_Units_inv_closed SA_add_pow_apply UP_cring.n_mult_def 
        UP_cring.pderiv_def UP_cring.poly_shift_def UP_cring_def \<phi>_Unit g_cfs(2) i\<^sub>0_inds
        inds_memE local.a_closed(2))    
  have 5: "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t =
            UPQ.taylor (c x) (SA_poly_to_Qp_poly m x f) i \<otimes> (t \<ominus> c x) [^] i"
    by(intro UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x f" t "c x" i ]
             Qp_closures poly_closures) 
  have 6: "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i \<bullet> t =
            UPQ.taylor (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i \<otimes> (t \<ominus> c x) [^] i"
    by(intro UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x (pderiv m f)" t "c x" i ]
             Qp_closures poly_closures) 
  have 7: "UPQ.taylor (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i = 
             taylor m c (pderiv m f) i x"
    using SA_poly_to_Qp_poly_taylor_poly taylor_def UPQ.taylor_def 
    by (simp add: Qp_closures(10) Qp_closures(13) SA_poly_to_Qp_poly_taylor_cfs UPSA.pderiv_closed f_closed)
  have 8: "UPQ.taylor (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i = 
             pderiv m (taylor m c f) i x"
     unfolding 7 
     using UPSA.pderiv_cfs UPSA.taylor_def pderiv_ith_cfs poly_closures(9) by presburger
   have 9: "UPSA.pderiv m (UPSA.taylor m c f) i x = [Suc i] \<cdot> a (Suc i) x"
     using taylor_def unfolding a_def 
     using Qp_closures(10) SA_add_pow_apply UPSA.taylor_expansion_pderiv_comm a_def assms(2)
            f_closed local.a_closed(2) pderiv_ith_cfs by presburger
   have 10: "g (Suc i) x \<otimes> s [^] i = \<alpha> x \<otimes> \<phi> x \<otimes> a (Suc i) x \<otimes> (t \<ominus> c x) [^] i"
   proof- 
     have a: "(t \<ominus> c x) [^] i = \<phi> x [^] i \<otimes> s [^] i"
       using u_inv_eval_car[of s x] unfolding assms 
       by (metis Qp.add.inv_solve_right Qp.m_closed Qp.nat_pow_distrib Qp_closures
            Qp_pow_ConsI a_minus_def assms(3))
     have b: "g (Suc i) x = \<alpha> x \<otimes> \<phi> x [^] Suc i \<otimes> a (Suc i) x"
       unfolding g_cfs(1)[of "Suc i"] 
       using Qp_closures(13) SA_mult SA_nat_pow by force
     show ?thesis unfolding a b 
       by (smt (z3) Qp.m_closed Qp.m_comm Qp.m_lcomm Qp.nat_pow_Suc2 Qp.nat_pow_closed
           Qp_closures(3) Qp_closures(4) Qp_closures(8) SA_car_closed assms(2) local.a_closed(2))
   qed
   have 11: "[Suc i] \<cdot> g (Suc i) x \<otimes> s [^] i  = [Suc i] \<cdot> (g (Suc i) x \<otimes> s [^] i)"
     by (metis Qp.add_pow_ldistr Qp.nat_pow_closed Qp_closures(13) Qp_closures(4) g_cfs_inds
         SA_Units_closed_fun SA_car_closed g_cfs_not_inds inds_non_memE local.a_closed(2))
  have 12: "(\<alpha> x \<otimes> \<phi> x) \<otimes> ([Suc i] \<cdot> a (Suc i) x \<otimes> (t \<ominus> c x) [^] i) = 
              [Suc i] \<cdot> ((\<alpha> x \<otimes> \<phi> x) \<otimes> ( a (Suc i) x \<otimes> (t \<ominus> c x) [^] i))"
    by (smt Qp.add_pow_ldistr Qp.add_pow_rdistr Qp.m_closed Qp.minus_closed Qp.nat_pow_closed
              Qp_closures SA_car_closed assms(2) local.a_closed(2))
  show "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') i \<bullet> s =
    (\<alpha> x \<otimes> \<phi> x) \<otimes> (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (pderiv m f)) i \<bullet> t)"
    unfolding 6 3 8 4 9 10 11 12 
    by (smt Qp.m_assoc Qp.m_closed Qp.minus_closed Qp.nat_pow_closed Qp_closures
              SA_car_closed assms(2) local.a_closed(2))
qed

lemma g'_eval_u_car:
  assumes "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  shows "SA_poly_to_Qp_poly m x g' \<bullet> (u(t#x)) =
                   (\<alpha> x \<otimes> \<phi> x) \<otimes> (SA_poly_to_Qp_poly m x (pderiv m f) \<bullet> t)"
proof- 
  obtain s where s_def: "s = u(t#x)"
    by blast 
  have s_normal: "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding s_def assms 
    by (metis Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) assms cartesian_power_tail list.sel(3) u_closed)
  have x_closures: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using s_normal by (metis cartesian_power_tail list.sel(3))
  have s_closed: "s \<in> carrier Q\<^sub>p"
    using SA_car_closed assms s_def u_closed by presburger
  obtain g0 where g0_def: "g0 = Cring_Poly.compose (SA m) a (up_ring.monom (UP (SA m)) \<phi> 1)"
    by blast 
  have g0_closed: "g0 \<in> carrier (UP (SA m))"
    unfolding g0_def using \<phi>_monom_closed by force
  have g'_eq: "g' = \<alpha> \<odot>\<^bsub>UP (SA m)\<^esub> (pderiv m g0)"
    unfolding g'_def g_def g0_def 
    using UPSA.pderiv_smult \<alpha>_closure(1) \<phi>_monom_closed by blast
  have g0'_eq: "pderiv m g0 = \<phi> \<odot>\<^bsub>UP (SA m)\<^esub> cmp (pderiv m a) (mon \<phi> 1)"
    unfolding g0_def  
    by (meson UPSA.linear_sub_deriv \<phi>_closures(1) local.a_closed(1))
  have 0: "g' = (\<alpha> \<otimes>\<^bsub>SA m\<^esub>\<phi>) \<odot>\<^bsub>UP (SA m)\<^esub> cmp (pderiv m a) (mon \<phi> 1)"
    unfolding g'_eq g0'_eq 
    using UPSA.is_UP_monomE(1) UPSA.monom_is_UP_monom(1) UPSA.pderiv_closed UPSA.smult_assoc1 
          UPSA.sub_closed \<alpha>_closure(1) \<phi>_closures(1) local.a_closed(1) by presburger
  have 1: "SA_poly_to_Qp_poly m x (cmp (pderiv m a) (mon \<phi> 1)) \<bullet> (u(t#x)) = 
            ev_poly x (pderiv m a) \<bullet> (ev_poly x (mon \<phi> 1)  \<bullet> (u(t#x))) "
    using UPQ.to_fun_sub unfolding 0 
    using SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_sub UPSA.pderiv_closed \<phi>_closures(1)
          local.a_closed(1) s_closed s_def x_closures by force
  have 2: "ev_poly x (mon \<phi> 1) = up_ring.monom (UP Q\<^sub>p) (\<phi> x) 1"
    using SA_poly_to_Qp_poly_monom \<phi>_closures(1) x_closures by blast
  have 3: "ev_poly x (mon \<phi> 1)  \<bullet> (u(t#x)) = \<phi> x \<otimes> s"
    unfolding 2 s_def 
    using SA_Units_closed_fun UPQ.to_fun_monom \<phi>_Unit s_closed s_def x_closures by force
  have 4: "\<phi> x \<otimes> s = t \<ominus> c x"
    unfolding s_def using u_eval_car 
    by (metis Qp.add.inv_solve_right Qp.function_ring_car_memE Qp.m_closed Qp_pow_ConsE(2)
              SA_car_memE(2) \<phi>_closures(1) a_minus_def assms c_closures(1) list.sel(1) s_def 
              s_normal u_inv_eval_car u_inv_u_car x_closures)
  have to_Qp_g0: "SA_poly_to_Qp_poly m x (cmp (pderiv m a) (mon \<phi> 1)) \<bullet> (u(t#x)) = 
          SA_poly_to_Qp_poly m x (UPSA.pderiv m a) \<bullet> (t \<ominus> c x)"
    unfolding 1 3 4 by auto 
  have 5: "ev_poly x g'  \<bullet> s = (\<alpha> x \<otimes> \<phi> x)\<otimes>(SA_poly_to_Qp_poly m x (cmp (pderiv m a) (mon \<phi> 1)) \<bullet> s)"
    unfolding 0 
    using SA_car_closed SA_mult SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_smult 
          UPQ.to_fun_smult UPSA.pderiv_closed UPSA.sub_closed \<alpha>_closure(1) \<phi>_closures(1) 
          local.a_closed(1) s_closed x_closures by auto
  have tminus: "t \<ominus> c x \<in> carrier Q\<^sub>p"
    by (metis 4 Qp.function_ring_car_memE Qp.m_closed SA_car_memE(2) \<phi>_closures(1) s_closed 
              x_closures)
  have a: "ev_poly x (UPSA.pderiv m a) = UPQ.pderiv (ev_poly x a)"
      using SA_poly_to_Qp_poly_comm_pderiv local.a_closed(1) x_closures by blast
    have b: "pderiv m a = taylor m c (pderiv m f)"
      unfolding a_def taylor_def 
      using UPSA.taylor_expansion_pderiv_comm c_closures(1) f_closed by blast
    have c: "ev_poly x (UPSA.pderiv m a) = 
             compose Q\<^sub>p (ev_poly x (pderiv m f)) (ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0))"
      unfolding b taylor_def taylor_expansion_def X_poly_plus_def X_poly_def to_polynomial_def 
      using SA_poly_to_Qp_poly_sub[of "UPSA.pderiv m a" m "mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0" x ]
            R.one_closed SA_poly_to_Qp_poly_sub UPSA.UP_a_closed UPSA.is_UP_monomE(1) 
            UPSA.monom_is_UP_monom(2) UPSA.pderiv_closed c_closures(1) f_closed x_closures
      by presburger
    have d: "ev_poly x (UPSA.pderiv m a) \<bullet> (t \<ominus> c x) 
              = ev_poly x (pderiv m f) \<bullet> ((ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0))\<bullet>(t \<ominus> c x))"
      unfolding c apply(intro UPQ.to_fun_sub[of "ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0)"
                            "ev_poly x (pderiv m f)" "t \<ominus> c x"] 
                            SA_poly_to_Qp_poly_closed )
      by(auto simp add:  c_closures(1) x_closures  tminus UPSA.pderiv_closed f_closed)
    have e: "(ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0))\<bullet>(t \<ominus> c x) = t"
    proof- 
      have 0: "(ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0)) = 
                  ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1) \<oplus>\<^bsub>UP Q\<^sub>p\<^esub> ev_poly x (mon c 0)"
        by (meson R.cring R.cring_simprules(6) SA_poly_to_Qp_poly_add UP_ring.intro 
                  UP_ring.monom_closed c_closures(1) cring_def x_closures)
      have 1: "ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1)\<bullet>(t \<ominus> c x) = t \<ominus> c x"
        by (metis "4" Qp.nat_pow_eone Qp.semiring_axioms R.semiring_axioms SA_Units_closed_fun SA_oneE SA_poly_to_Qp_poly_monom UPQ.to_fun_monom \<phi>_Unit s_closed semiring.semiring_simprules(3) semiring.semiring_simprules(4) semiring.semiring_simprules(9) x_closures)
      have 2: "ev_poly x (mon c 0)\<bullet>(t \<ominus> c x) = c x"
      proof-
        have 0: "ev_poly x (mon c 0) = to_polynomial Q\<^sub>p (c x)"
          by (simp add: SA_poly_to_Qp_poly_monom c_closures(1) to_polynomial_def x_closures)
        show ?thesis using tminus unfolding 0 
          by (metis UPQ.to_fun_to_poly \<C>_cell \<C>_eq is_cell_condition_closure'(1) x_closures)
      qed
      have 3: "(ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1 \<oplus>\<^bsub>UP (SA m)\<^esub> mon c 0))\<bullet>(t \<ominus> c x) = 
                  ev_poly x (mon \<one>\<^bsub>SA m\<^esub> 1)\<bullet>(t \<ominus> c x) \<oplus> ev_poly x (mon c 0)\<bullet>(t \<ominus> c x)"
        unfolding 0 
        by (metis Qp.minus_closed R.cring_simprules(6) SA_poly_to_Qp_poly_closed UPQ.to_fun_plus 
                UPSA.is_UP_monomE(1) UPSA.monom_is_UP_monom(1) \<C>_cell \<C>_eq assms c_closures(1) 
                cartesian_power_head is_cell_condition_closure'(1) list.sel(1) x_closures)
      show ?thesis unfolding 1 2 3 
      by (metis "4" assms s_def s_normal u_inv_eval_car u_inv_u_car)
    qed
    have 7: "ev_poly x g'  \<bullet> s = \<alpha> x \<otimes> \<phi> x \<otimes> (ev_poly x (UPSA.pderiv m f) \<bullet> t)"
      unfolding 5 unfolding s_def unfolding  to_Qp_g0 d e by auto 
  show ?thesis using 7 unfolding s_def by auto 
qed

fun normalize_cell_inv where 
"normalize_cell_inv (Cond n C d a1 a2 I) = 
      Cond n C ((\<phi> \<otimes>\<^bsub>SA m\<^esub> d) \<oplus>\<^bsub>SA m\<^esub> c) (\<phi> \<otimes>\<^bsub>SA m\<^esub> a1) (\<phi> \<otimes>\<^bsub>SA m\<^esub> a2) I"

lemma normalize_cell_inv_closed:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "is_cell_condition (normalize_cell_inv \<B>)"
proof- 
  obtain C d a1 a2 I where params: "\<B> = Cond m C d a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  show ?thesis 
    unfolding normalize_cell_inv.simps params 
    apply(intro is_cell_conditionI' R.m_closed R.a_closed)
    using assms(1) c_closures(1) \<phi>_closures(1)
    unfolding params by auto 
qed

lemma normalize_cell_inv_arity:
  assumes "arity \<B> = m"
  shows "arity (normalize_cell_inv \<B>) = m"
  using normalize_cell_inv.simps assms arity.simps 
  by (metis condition_decomp')

lemma normalize_inv_normal_cell:
"normalize_cell_inv (normal_cell m b) = \<C>"
  unfolding \<C>_eq normalize_cell_inv.simps normal_cell_def 
  by (simp add: \<phi>_closures(1) c_closures(1))

fun normalize_cell where 
"normalize_cell (Cond n C d a1 a2 I) = 
    Cond n C ((inv\<^bsub>SA m\<^esub> \<phi>)\<otimes>\<^bsub>SA m\<^esub>(d \<ominus>\<^bsub>SA m\<^esub> c)) 
                      ((inv\<^bsub>SA m\<^esub> \<phi>) \<otimes>\<^bsub>SA m\<^esub> a1) ((inv\<^bsub>SA m\<^esub> \<phi>) \<otimes>\<^bsub>SA m\<^esub> a2) I"

lemma normalize_cell_arity:
  assumes "arity \<B> = m"
  shows "arity (normalize_cell \<B>) = m"
  using normalize_cell.simps assms arity.simps  
  by (metis condition_decomp')

lemma normalize_cell_closed:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "is_cell_condition (normalize_cell \<B>)"
proof- 
  obtain C d a1 a2 I where params: "\<B> = Cond m C d a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  show ?thesis 
    unfolding normalize_cell.simps params 
    apply(intro is_cell_conditionI' R.m_closed R.a_closed R.minus_closed)
    using assms(1) c_closures(1) \<phi>_closures(1) \<phi>_Unit
    unfolding params by auto 
qed

lemma normalize_\<C>:
"normalize_cell \<C> = normal_cell m b"
  unfolding \<C>_eq normal_cell_def normalize_cell.simps 
  by (metis R.Units_l_inv R.r_null R.r_right_minus_eq SA_Units_inv_closed \<phi>_Unit c_closures(1))

lemma normalize_cell_inverse_formula:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "normalize_cell (normalize_cell_inv \<B>) = \<B>"
        "normalize_cell_inv (normalize_cell \<B>) = \<B>"
proof- 
  obtain C d a1 a2 I where params: "\<B> = Cond m C d a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  have R: "\<And> f. f \<in> carrier (SA m) \<Longrightarrow> inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (\<phi> \<otimes>\<^bsub>SA m\<^esub> f) = f"
          "\<And> f. f \<in> carrier (SA m) \<Longrightarrow>  \<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> f) = f"
    using R.inv_cancelR[of \<phi> m] \<phi>_Unit   \<phi>_closures(1) apply auto[1]
    by (metis R.cring_simprules(11) R.l_one SA_Units_inv_closed SA_Units_memE(1)
              \<phi>_Unit \<phi>_closures(1))
  have 0: "(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (\<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c \<ominus>\<^bsub>SA m\<^esub> c)) = d"
  proof- 
    have 0: "\<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c \<ominus>\<^bsub>SA m\<^esub> c = \<phi> \<otimes>\<^bsub>SA m\<^esub> d"
      using c_closures \<phi>_closures \<phi>_Unit assms unfolding params a_minus_def 
      by (meson R.add.inv_solve_right' R.add.m_closed R.m_closed is_cell_conditionE(2))
    show ?thesis unfolding 0 apply(rule R)
      using assms unfolding params  by auto 
  qed
  have 1: "(\<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c)) \<oplus>\<^bsub>SA m\<^esub> c) = d"
  proof- 
    have 1: "inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c) = inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> d \<ominus>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> c"
      using R.r_minus_distr \<phi>_Unit assms(1) c_closures(1) params by force
    have 2: "\<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> d \<ominus>\<^bsub>SA m\<^esub> inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> c) = 
            \<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> d) \<ominus>\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> c)"
      by (metis (no_types, lifting) R.m_closed R.r_minus_distr SA_Units_inv_closed \<phi>_Unit \<phi>_closures(1) assms(1) c_closures(1) is_cell_conditionE''(5) params)
    have 3: " \<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> d) = d"
      apply(rule R) using assms unfolding params by auto 
    have 4: " \<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> c) = c"
      by(intro R c_closures)  
    show ?thesis using assms c_closures 
      unfolding params 0 1 2 3 4 unfolding a_minus_def 
      by (simp add: R.a_ac(2) R.cring R.ring_simprules(16) cring.cring_simprules(7))
  qed
  have 2: "( \<phi> \<otimes>\<^bsub>SA m\<^esub>(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> a1)) = a1"
          "(\<phi> \<otimes>\<^bsub>SA m\<^esub> (inv\<^bsub>SA m\<^esub>\<phi> \<otimes>\<^bsub>SA m\<^esub> a2)) = a2"
    apply(intro R(2)[of a1]) using params assms apply auto[1]
    apply(intro R(2)[of a2]) using params assms by auto[1]
  have 3: "(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (\<phi> \<otimes>\<^bsub>SA m\<^esub> a1)) = a1" 
          "(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (\<phi> \<otimes>\<^bsub>SA m\<^esub> a2)) = a2"
    apply(intro R(1)[of a1]) using params assms apply auto[1]
    apply(intro R(1)[of a2]) using params assms by auto[1]
  show "normalize_cell (normalize_cell_inv \<B>) = \<B>"
        "normalize_cell_inv (normalize_cell \<B>) = \<B>"
    unfolding params normalize_cell.simps normalize_cell_inv.simps 0 1 2 3
    using \<phi>_Unit params assms by auto 
qed

lemma(in padic_fields) convex_member_mult:
  assumes "a \<in> Units Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p" 
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  assumes "is_convex_condition I"
  assumes "val b \<in> I (val c) (val d)"
  shows "val(a \<otimes> b) \<in> I (val (a \<otimes> c)) (val (a \<otimes> d))"
proof- 
  have 0: "val (a \<otimes> b) = val a + val b" "val (a \<otimes> c) = val a + val c" 
            "val (a \<otimes> d) = val a + val d" 
    using val_mult assms by auto 
  have 1: "\<exists>i. val a = eint i"
    using assms Units_eq_nonzero val_ord by blast
  have "val b \<in> I (val c) (val d) \<longrightarrow> val(a \<otimes> b) \<in> I (val (a \<otimes> c)) (val (a \<otimes> d))"
    by(rule convex_condition_induct, rule assms(5), 
          unfold 0 closed_interval_def left_closed_interval_def  
                  closed_ray_def open_ray_def mem_Collect_eq, auto simp: 1)
  thus ?thesis using assms by auto 
qed

lemma(in padic_fields) mult_ineq:
  assumes "a \<in> Units Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p" 
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val b \<le> val c + eint N"
  shows "val(a \<otimes> b) \<le> val (a \<otimes> c) + eint N"
proof-
  have 0: "val (a \<otimes> b) = val a + val b" "val (a \<otimes> c) = val a + val c"           
    using val_mult assms by auto 
  have 1: "\<exists>i. val a = eint i"
    using assms Units_eq_nonzero val_ord by blast
  show ?thesis unfolding 0 
    by (simp add: assms(4))
qed

lemma u_maps_to_normalized_cell:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "t#x \<in> condition_to_set \<B>"
  shows "u(t#x)#x \<in> condition_to_set (normalize_cell \<B>)"
proof- 
  obtain C d a1 a2 I where params: "\<B> = Cond m C d a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms 
    unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd apply auto[1] 
    using assms 
    unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    apply (metis cartesian_power_head list.sel(1))
    using assms unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    by(metis cartesian_power_tail list_tl)
  have d_closed: "d \<in> carrier (SA m)"
    using assms params by auto 
  have 0: "u (t # x) \<ominus> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c)) x = 
           inv \<phi> x \<otimes> (t \<ominus> c x) \<ominus> (inv \<phi> x) \<otimes> (d x \<ominus> c x)"
    using u_eval_car[of t x] tx_closed d_closed 
    by (simp add: SA_inv_eval SA_minus_eval SA_mult \<phi>_Unit c_closures(1))
  have 1: "u (t # x) \<ominus> (inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c)) x = 
           inv \<phi> x \<otimes> (t \<ominus> d x)"
    unfolding 0 using tx_closed d_closed c_closures 
    by (metis Qp.cring_simprules(4) Qp.r_minus_distr Qp_diff_diff Qp_funs_Units_memE(3)
        SA_Units_Qp_funs_Units SA_car_closed \<phi>_Unit \<phi>_closures(1) inv_in_frac(1))
  have 2: "(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> a1) x =  inv \<phi> x \<otimes> a1 x"
    by (simp add: SA_inv_eval SA_mult \<phi>_Unit tx_closed(3))
  have 3: "(inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> a2) x =  inv \<phi> x \<otimes> a2 x"
    by (simp add: SA_inv_eval SA_mult \<phi>_Unit tx_closed(3))
  have 4: "u (t # x) \<in> carrier Q\<^sub>p"
    using tx_closed u_closed SA_car_closed by presburger
  show "u(t#x)#x \<in> condition_to_set (normalize_cell \<B>)"
    unfolding params normalize_cell.simps condition_to_set.simps
    apply(rule cell_memI, unfold list_tl list_hd 1 2 3)
    using tx_closed(2) 4 Qp_pow_ConsI tx_closed(3) apply presburger
    using assms unfolding params condition_to_set.simps cell_def list_tl mem_Collect_eq apply simp
    using convex_member_mult[of "inv \<phi> x" "t \<ominus> d x" "a1 x" "a2 x" I]
          assms unfolding params 
    by (metis Qp.cring_simprules(4) Qp_funs_Units_memE(3) SA_Units_Qp_funs_Units SA_car_closed 
        Units_eq_nonzero \<phi>_Unit \<phi>_closures(1) condition_to_set_memE'(2) d_closed inv_in_frac(3) 
        is_cell_conditionE''(8) is_cell_conditionE(3) is_cell_conditionE(4) tx_closed(2) 
        tx_closed(3))
qed

lemma u_inv_maps_from_normalized_cell:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "s#x \<in> condition_to_set \<B>"
  shows "u_inv(s#x)#x \<in> condition_to_set (normalize_cell_inv \<B>)"
proof- 
  obtain C d a1 a2 I where params: "\<B> = Cond m C d a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  have sx_closed: "s#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "s \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms 
    unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd apply auto[1] 
    using assms 
    unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    apply (metis cartesian_power_head list.sel(1))
    using assms unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
    by(metis cartesian_power_tail list_tl)
  have d_closed: "d \<in> carrier (SA m)"
    using assms params by auto 
  have 1: "u_inv (s # x) \<ominus> (\<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c) x = \<phi> x \<otimes> (s \<ominus> d x) "
  proof- 
    have 0: "u_inv (s # x) \<ominus> (\<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c) x  = 
              (\<phi> x \<otimes> s \<oplus> c x) \<ominus> (\<phi> x \<otimes> d x \<oplus> c x)"
      using u_inv_eval_car[of s x] sx_closed c_closures d_closed SA_add SA_mult by presburger
    show ?thesis unfolding 0 
      by (smt (z3) Qp.add.inv_solve_right Qp.add.m_closed Qp.add.m_comm Qp.m_closed 
          Qp.r_minus_distr Qp.right_inv_add SA_car_closed \<phi>_closures(1) a_minus_def 
          c_closures(1) d_closed sx_closed(2) sx_closed(3))
  qed
  have 2: "( \<phi> \<otimes>\<^bsub>SA m\<^esub> a1) x =  \<phi> x \<otimes> a1 x"
    by (simp add: SA_inv_eval SA_mult \<phi>_Unit sx_closed(3))
  have 3: "(\<phi> \<otimes>\<^bsub>SA m\<^esub> a2) x =  \<phi> x \<otimes> a2 x"
    by (simp add: SA_inv_eval SA_mult \<phi>_Unit sx_closed(3))
  have 4: "u_inv (s # x) \<in> carrier Q\<^sub>p"
    using sx_closed u_inv_closed SA_car_closed by presburger
  show "u_inv (s#x)#x \<in> condition_to_set (normalize_cell_inv \<B>)"
    unfolding params normalize_cell_inv.simps condition_to_set.simps
    apply(rule cell_memI, unfold list_hd list_tl 1)
    using sx_closed(2) 4 Qp_pow_ConsI sx_closed(3) apply presburger
    using assms unfolding params condition_to_set.simps cell_def list_tl mem_Collect_eq apply simp
    using convex_member_mult[of "\<phi> x" "s \<ominus> d x" "a1 x" "a2 x" I]
          assms unfolding params 
    by (metis (no_types, lifting) "2" "3" Qp.cring_simprules(4) Qp.not_nonzero_memE
        Qp_funs_Units_memE(3) SA_Units_Qp_funs_Units SA_car_closed Units_eq_nonzero 
        \<phi>_Unit \<phi>_closures(1) condition_to_set_memE'(2) is_cell_conditionE''(8)
        is_cell_condition_closure'(1) is_cell_condition_closure'(2) is_cell_condition_closure'(3)
        sx_closed(2) sx_closed(3))
qed

definition var_change where 
"var_change F xs = (F xs)#(tl xs)"

lemma obtain_cell_mem_coords:
  assumes "arity \<B> = m"
  assumes "xs \<in> condition_to_set \<B>"
  shows "\<exists> t x. xs = t#x"
proof- 
  have "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms condition_to_set.simps arity.simps 
    by (meson basic_trans_rules(31) cell_condition_to_set_subset)
  thus ?thesis 
    by (metis Suc_length_conv cartesian_power_car_memE)
qed

lemma u_var_change_cell:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "var_change u ` (condition_to_set \<B>) = condition_to_set (normalize_cell \<B>)"
proof(rule equalityI')
  fix xs assume A: "xs \<in> var_change u ` condition_to_set \<B>"
  obtain t x where tx_def: "t#x \<in> condition_to_set \<B> \<and> xs = var_change u (t#x)"
    using A assms obtain_cell_mem_coords unfolding image_iff by blast
  have xs_eq: "xs = var_change u (t#x)"
    using tx_def by auto 
  show "xs \<in> condition_to_set (normalize_cell \<B>)"
    unfolding xs_eq var_change_def list_tl 
    apply(intro u_maps_to_normalized_cell assms)
    using tx_def by auto 
next
  fix xs assume A: "xs \<in> condition_to_set (normalize_cell \<B>)"
  obtain t x where tx_def: "xs = t#x"
    using A obtain_cell_mem_coords normalize_cell.simps assms arity.simps 
    by (metis condition_decomp')
  have 0: "arity (normalize_cell \<B>) = m"
    using assms normalize_cell.simps arity.simps 
    by (metis condition_decomp')
  have 1: "u (u_inv (t # x) # x) = t"
    apply(rule  u_u_inv_car[of t x] )
    using A cell_condition_to_set_subset[of "normalize_cell \<B>"]
    unfolding tx_def condition_decomp 0 by auto
  have xs_formula: "xs = var_change u (var_change u_inv xs)"
    unfolding tx_def var_change_def  list_tl list_hd 1 by auto 
  have 2: "var_change u_inv xs \<in> condition_to_set \<B>"
    using A unfolding var_change_def list_tl list_hd tx_def 
    by (metis "0" assms(1) assms(2) normalize_cell_closed normalize_cell_inverse_formula(2)
        u_inv_maps_from_normalized_cell)
  show "xs \<in> var_change u ` (condition_to_set \<B>)"
    using xs_formula 2 by auto 
qed

lemma u_inv_var_change_cell:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "var_change u_inv ` (condition_to_set (normalize_cell \<B>)) = condition_to_set \<B>"
proof(rule equalityI')
  fix xs assume A: "xs \<in> var_change u_inv ` condition_to_set (normalize_cell \<B>)"
  obtain t x where tx_def: "t#x \<in> condition_to_set (normalize_cell \<B>) \<and> xs = var_change u_inv (t#x)"
    using A assms obtain_cell_mem_coords unfolding image_iff 
    by (metis arity.simps condition_decomp' normalize_cell.simps)
  have xs_eq: "xs = var_change u_inv (t#x)"
    using tx_def by auto 
  have "xs \<in> condition_to_set (normalize_cell_inv (normalize_cell \<B>))"
    unfolding xs_eq var_change_def list_tl 
    apply(intro u_inv_maps_from_normalized_cell
                normalize_cell_closed assms normalize_cell_arity)
    using tx_def by auto 
  thus "xs \<in> condition_to_set \<B>"
    using assms normalize_cell_inverse_formula(2) by auto
next
  fix xs assume A: "xs \<in> condition_to_set \<B>"
  obtain t x where tx_def: "xs = t#x"
    using A obtain_cell_mem_coords normalize_cell.simps assms arity.simps 
    by (metis condition_decomp')
  have 0: "arity (normalize_cell \<B>) = m"
    using assms normalize_cell.simps arity.simps 
    by (metis condition_decomp')
  have 1: "u_inv (u (t # x) # x) = t"
    apply(rule  u_inv_u_car[of t x] )
    using assms A cell_condition_to_set_subset[of "\<B>"]
    unfolding tx_def condition_decomp 0 by auto
  have xs_formula: "xs = var_change u_inv (var_change u xs)"
    unfolding tx_def var_change_def  list_tl list_hd 1 by auto 
  have 2: "var_change u xs \<in> condition_to_set (normalize_cell \<B>)"
    using A unfolding var_change_def list_tl list_hd tx_def 
    by (metis assms(1) assms(2) u_maps_to_normalized_cell)
  show "xs \<in> var_change u_inv ` condition_to_set (normalize_cell \<B>)"
    using xs_formula 2 by auto 
qed

lemma u_inv_var_change_cell':
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  shows "var_change u_inv `(condition_to_set \<B>) = condition_to_set (normalize_cell_inv \<B>)"
proof- 
  have 0: "\<B> = normalize_cell (normalize_cell_inv \<B>)"
    using assms normalize_cell_inverse_formula(1) by presburger
  have 1: "var_change u_inv ` (condition_to_set (normalize_cell (normalize_cell_inv \<B>)))
             = condition_to_set (normalize_cell_inv \<B>)"
    by(intro u_inv_var_change_cell normalize_cell_inv_closed assms normalize_cell_inv_arity)
  thus ?thesis using 0 by auto 
qed

lemma transfer_cell_decomp: 
  assumes "is_cell_decomp m S (condition_to_set (normal_cell m b))"
  shows "is_cell_decomp m (normalize_cell_inv ` S) (condition_to_set \<C>)"
proof(rule is_cell_decompI)
  show "finite (normalize_cell_inv ` S)"
    using assms is_cell_decompE by auto 
  have 0: "\<Union> (condition_to_set ` S) = condition_to_set (normal_cell m b)"
    using assms is_cell_decompE(2)[of m S "condition_to_set (normal_cell m b)"] 
          is_partitionE[of "condition_to_set ` S" "condition_to_set (normal_cell m b)"]
    by blast 
  have 1: "var_change u_inv ` (\<Union> (condition_to_set ` S)) = 
             (\<Union> (condition_to_set ` normalize_cell_inv `  S))"
    apply(intro equalityI' ) 
    using u_inv_var_change_cell' is_cell_decompE(3,4)[of m S "condition_to_set (normal_cell m b)"]
          assms  apply fastforce
    using u_inv_var_change_cell' is_cell_decompE(3,4)[of m S "condition_to_set (normal_cell m b)"]
          assms  by fastforce
  have 2: "disjoint (condition_to_set ` normalize_cell_inv ` S)"
  proof(rule disjointI)
    fix A B assume A: "A \<in> condition_to_set ` normalize_cell_inv ` S" "A \<noteq> B"
                      "B \<in> condition_to_set ` normalize_cell_inv ` S"
    then obtain C D where defs: "C \<in> S \<and> A = condition_to_set (normalize_cell_inv C)"
                                "D \<in> S \<and> B = condition_to_set (normalize_cell_inv D)"
      by blast 
    have neq: "C \<noteq> D"
      using defs A by auto 
    have a: "condition_to_set C \<inter> condition_to_set D = {}"
      using defs is_cell_decompE is_partitionE assms A neq by auto 
    have b: "normalize_cell (normalize_cell_inv C) = C"
      apply(intro normalize_cell_inverse_formula 
              is_cell_decompE[of m S "condition_to_set (normal_cell m b)"])
      using defs assms is_cell_decompE by auto 
    have c: "var_change u ` (condition_to_set (normalize_cell_inv C)) = condition_to_set C"
    proof- 
      have 0: "is_cell_condition (normalize_cell_inv C)"
        apply(intro normalize_cell_inv_closed)
        using assms is_cell_decompE defs A by auto 
      have 1: "arity (normalize_cell_inv C) = m"
        apply(intro normalize_cell_inv_arity)
        using assms is_cell_decompE defs A by auto 
      show ?thesis 
        using 1 0 normalize_cell_inv_closed
            u_var_change_cell[of "normalize_cell_inv C"] unfolding b by auto 
    qed
    have d: "normalize_cell (normalize_cell_inv D) = D"
       apply(intro normalize_cell_inverse_formula 
              is_cell_decompE[of m S "condition_to_set (normal_cell m b)"])
      using defs assms is_cell_decompE by auto 
    have e: "var_change u ` (condition_to_set (normalize_cell_inv D)) = condition_to_set D"
        proof- 
      have 0: "is_cell_condition (normalize_cell_inv D)"
        apply(intro normalize_cell_inv_closed)
        using assms is_cell_decompE defs A by auto 
      have 1: "arity (normalize_cell_inv D) = m"
        apply(intro normalize_cell_inv_arity)
        using assms is_cell_decompE defs A by auto 
      show ?thesis 
        using 1 0 normalize_cell_inv_closed
            u_var_change_cell[of "normalize_cell_inv D"] unfolding d by auto 
    qed
    show "A \<inter> B = {}"
      using defs d e a c by auto 
  qed
  show a: "condition_to_set ` normalize_cell_inv ` S partitions condition_to_set \<C>"
    apply(rule is_partitionI disjointI)
    using 2 apply blast
    using assms 1 
    by (metis "0" \<C>_cell \<C>_eq arity.simps normalize_\<C> u_inv_var_change_cell)
  show b: "\<And>s. s \<in> normalize_cell_inv ` S \<Longrightarrow> is_cell_condition s \<and> arity s = m"
    using assms is_cell_decompE(3) is_cell_decompE(4) normalize_cell_inv_arity 
      normalize_cell_inv_closed by force
  show c: " condition_to_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by (metis \<C>_eq arity.simps cell_condition_to_set_subset)
  show "\<And>s s'.
       s \<in> normalize_cell_inv ` S \<Longrightarrow>
       s' \<in> normalize_cell_inv ` S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  proof- 
    fix s s' assume A: "s \<in> normalize_cell_inv ` S" " s' \<in> normalize_cell_inv ` S" "s \<noteq> s'"
    obtain A B where AB_def: 
       "A \<in> S" "s = normalize_cell_inv A"
       "B \<in> S" "s' = normalize_cell_inv B"
      using A by blast 
    show "condition_to_set s \<inter> condition_to_set s' = {}"
    proof(rule ccontr)
      assume false: "condition_to_set s \<inter> condition_to_set s' \<noteq> {}"
      then obtain x where x_def: "x \<in> condition_to_set s \<inter> condition_to_set s'"
        by auto 
      have 0: "A = normalize_cell s"
        using AB_def is_cell_decompE assms unfolding AB_def 
        by (metis normalize_cell_inverse_formula(1))
      have 1: "B = normalize_cell s'"
        using AB_def is_cell_decompE assms unfolding AB_def 
        by (metis normalize_cell_inverse_formula(1))
      have 2: "condition_to_set A = var_change u ` condition_to_set s"
        unfolding 0 
        using A(1) b u_var_change_cell by presburger
      have 3: "condition_to_set B = var_change u ` condition_to_set s'"
        unfolding 1 using A b u_var_change_cell by presburger
      have 4: "condition_to_set A \<inter> condition_to_set B \<noteq> {}"
        unfolding 2 3 using false by auto 
      thus False 
        using A is_cell_decompE unfolding AB_def 
        by (metis AB_def(1) AB_def(3) assms)
    qed
  qed
qed

lemma transfer_subset1:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "condition_to_set \<B> \<subseteq> condition_to_set (normal_cell m b)"
  shows "condition_to_set (normalize_cell_inv \<B>) \<subseteq> condition_to_set \<C>"
proof- 
  have 0: "condition_to_set (normalize_cell_inv \<B>) = var_change u_inv ` (condition_to_set \<B>)"
    using assms by (simp add: u_inv_var_change_cell')
  have 1: "condition_to_set \<C> = var_change u_inv ` condition_to_set (normal_cell m b)"
    by (metis \<C>_cell \<C>_eq arity.simps normalize_\<C> u_inv_var_change_cell)
  show ?thesis using assms 0 1 by auto 
qed

lemma transfer_subset2:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "condition_to_set \<B> \<subseteq> condition_to_set \<C>"
  shows "condition_to_set (normalize_cell \<B>) \<subseteq> condition_to_set (normal_cell m b)"
proof- 
  have 0: "condition_to_set (normalize_cell \<B>) = var_change u ` (condition_to_set \<B>)"
    using assms by (simp add: u_var_change_cell)
  have 1: "condition_to_set (normal_cell m b) = var_change u ` condition_to_set \<C>"
    by (metis \<C>_cell \<C>_eq arity.simps normalize_\<C> u_var_change_cell)
  show ?thesis using assms 0 1 by auto 
qed

lemma transfer_SA_poly_ubounded1:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "SA_poly_ubounded p m g (center \<B>) (condition_to_set \<B>) N"
  shows "SA_poly_ubounded p m f (center (normalize_cell_inv \<B>)) 
                                (condition_to_set (normalize_cell_inv \<B>)) N"
proof(intro SA_poly_uboundedI f_closed)
  have 0: "is_cell_condition (normalize_cell_inv \<B>)"
    by(intro normalize_cell_inv_closed assms)
  show 1: "center (normalize_cell_inv \<B>) \<in> carrier (SA m)"
    by (metis 0 assms(2) condition_decomp' is_cell_conditionE(2) normalize_cell_inv_arity)
  show 2: "condition_to_set (normalize_cell_inv \<B>) \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by (metis 0 assms(2) cell_condition_to_set_subset normalize_cell_inv_arity)
  show "\<And>x t i.
       t # x \<in> condition_to_set (normalize_cell_inv \<B>) \<Longrightarrow>
       val (SA_poly_to_Qp_poly m x f \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normalize_cell_inv \<B>) x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) +
          eint N"
  proof- 
    fix x t i assume A: "t # x \<in> condition_to_set (normalize_cell_inv \<B>)"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using "2" A Set.basic_monos(7) cartesian_power_head[of "t#x" Q\<^sub>p m] cartesian_power_tail[of "t#x" Q\<^sub>p m]
      by auto 
    obtain s where s_def: "s = u (t#x)"
      by blast 
    have s_closed: "s \<in> carrier Q\<^sub>p"
      using tx_closed SA_car_closed s_def u_closed by presburger
    obtain D d a1 a2 I 
      where params: "\<B> = Cond m D d a1 a2 I"
      using assms arity.simps by (meson equal_CondI)
    obtain e where e_def: "e = \<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c"
      by blast 
    have e_center: "e = center (normalize_cell_inv \<B>)"
      unfolding params normalize_cell_inv.simps params center.simps e_def by auto 
    have 0: "SA_poly_to_Qp_poly m x f \<bullet> t = inv \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> u (t # x))"
      using g_eval_u_car[of t x] tx_closed by auto 
    have 1: "UPQ.taylor_term (center (normalize_cell_inv \<B>) x) (SA_poly_to_Qp_poly m x f) i \<bullet> t 
              = inv \<alpha> x \<otimes> (UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s)"
      using e_def g_taylor_term[of s x d t e i] 
      by (metis assms(1) e_center is_cell_conditionE(2) params s_closed s_def tx_closed u_inv_u_car)
    have 2: "val ((SA_poly_to_Qp_poly m x g \<bullet> s))
    \<le> val ((UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x g) i \<bullet> s)) + eint N"
      using SA_poly_uboundedE' assms params 
      by (metis A condition_decomp(3) normalize_cell_inv_arity normalize_cell_inv_closed normalize_cell_inverse_formula(1) s_def u_maps_to_normalized_cell)
    show "val (SA_poly_to_Qp_poly m x f \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normalize_cell_inv \<B>) x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) +
          eint N"
      apply(unfold 0 1, intro mult_ineq) 
      using SA_Units_closed_fun SA_Units_memE' Units_eq_nonzero \<alpha>_closure(2) inv_in_frac(3) tx_closed(3) apply presburger
      using SA_poly_to_Qp_poly_closed UPQ.to_fun_closed g_closed s_closed s_def tx_closed(3) apply force
      apply (metis SA_poly_to_Qp_poly_closed UPQ.taylor_term_closed UPQ.to_fun_closed assms(1) g_closed is_cell_condition_closure'(1) params s_closed tx_closed(3))
      using "2" s_def by force
  qed
qed

lemma transfer_SA_poly_ubounded2:
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "SA_poly_ubounded p m f (center \<B>) (condition_to_set \<B>) N"
  shows "SA_poly_ubounded p m g (center (normalize_cell \<B>)) 
                                (condition_to_set (normalize_cell \<B>)) N"
proof(intro SA_poly_uboundedI g_closed)
  have 0: "is_cell_condition (normalize_cell \<B>)"
    by(intro normalize_cell_closed assms)
  show 1: "center (normalize_cell \<B>) \<in> carrier (SA m)"
    by (metis 0 assms(2) condition_decomp' is_cell_conditionE(2) normalize_cell_arity)
  show 2: "condition_to_set (normalize_cell \<B>) \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    by (metis 0 assms(2) cell_condition_to_set_subset normalize_cell_arity)
  show "\<And>x t i.
       t # x \<in> condition_to_set (normalize_cell \<B>) \<Longrightarrow>
       val (SA_poly_to_Qp_poly m x g \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normalize_cell \<B>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t) +
          eint N"
  proof- 
    fix x t i assume A: "t # x \<in> condition_to_set (normalize_cell \<B>)"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using "2" A Set.basic_monos(7) cartesian_power_head[of "t#x" Q\<^sub>p m] cartesian_power_tail[of "t#x" Q\<^sub>p m]
      by auto 
    obtain s where s_def: "s = u_inv (t#x)"
      by blast 
    have s_closed: "s \<in> carrier Q\<^sub>p"
      using tx_closed SA_car_closed s_def u_inv_closed by presburger
    obtain D d a1 a2 I 
      where params: "\<B> = Cond m D d a1 a2 I"
      using assms arity.simps by (meson equal_CondI)
    obtain e where e_def: "e = inv\<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c)"
      by blast 
    have e_center: "e = center (normalize_cell \<B>)"
      unfolding params normalize_cell.simps params center.simps e_def by auto 
    have d_eq: "d = \<phi> \<otimes>\<^bsub>SA m\<^esub> e \<oplus>\<^bsub>SA m\<^esub> c"
      unfolding e_def 
      by (metis (no_types, lifting) R.Units_inv_inv R.Units_inverse R.add.inv_solve_right'
          R.inv_cancelR(1) R.m_closed SA_Units_inv_closed SA_minus_closed \<phi>_Unit a_minus_def 
          assms(1) c_closures(1) is_cell_conditionE(2) params)
    have 0: "SA_poly_to_Qp_poly m x g \<bullet> t = \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> u_inv (t # x))"
      using g_eval_s_car[of t x] tx_closed by auto 
    have 1: "UPQ.taylor_term (center (normalize_cell \<B>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t =
                      \<alpha> x \<otimes> (UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x f) i \<bullet> s)"
      using e_center g_taylor_term(1)[of t x e s d i] e_def
      by (metis R.cring_simprules(5) SA_Units_inv_closed SA_minus_closed \<phi>_Unit assms(1) 
          c_closures(1) d_eq is_cell_conditionE(2) params s_def tx_closed(2) tx_closed(3))
    have 2: "s#x \<in> condition_to_set \<B>"
      by (metis s_def A assms(1) assms(2) normalize_cell_arity normalize_cell_closed
          normalize_cell_inverse_formula(2) u_inv_maps_from_normalized_cell)
    have 3: "val ((SA_poly_to_Qp_poly m x f \<bullet> s))
    \<le> val ((UPQ.taylor_term (d x) (SA_poly_to_Qp_poly m x f) i \<bullet> s)) + eint N"
      using SA_poly_uboundedE'[of m f "center \<B>" "condition_to_set \<B>" N] assms 2
      unfolding params center.simps by auto 
    show "val (SA_poly_to_Qp_poly m x g \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normalize_cell \<B>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t)
                               + eint N"
      apply(unfold 0 1, intro mult_ineq) 
      using SA_Units_nonzero Units_eq_nonzero \<alpha>_closure(2) tx_closed(3) apply presburger
      using SA_poly_to_Qp_poly_closed UPQ.to_fun_closed f_closed s_closed s_def tx_closed(3) apply force
       apply (metis SA_poly_to_Qp_poly_closed UPQ.taylor_term_closed UPQ.to_fun_closed assms(1)
                    f_closed is_cell_condition_closure'(1) params s_closed tx_closed(3))
      using "3" s_def by blast      
  qed
qed

lemma transfer_SA_poly_ubounded3:
  assumes "SA_poly_ubounded p m (UPSA.pderiv m f) (center \<C>) (condition_to_set \<C>) N"
  shows "SA_poly_ubounded p m g' (center (normal_cell m b)) 
                                (condition_to_set (normal_cell m b)) N"
proof(intro SA_poly_uboundedI g_closed)
  show "\<And>x t i.
       t # x \<in> condition_to_set (normal_cell m b) \<Longrightarrow>
       val (SA_poly_to_Qp_poly m x g' \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normal_cell m b) x) (SA_poly_to_Qp_poly m x g') i \<bullet> t) + eint N"
  proof-
   fix x t i assume A: "t # x \<in> condition_to_set (normal_cell m b)"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using  A Set.basic_monos(7) cartesian_power_head[of "t#x" Q\<^sub>p m]
            cartesian_power_tail[of "t#x" Q\<^sub>p m]
        apply (metis (no_types, lifting) Qp_pow_ConsI \<C>_memE(2) b_closures normal_cell_memE(1)
                                    u_inv_maps_to_\<C>)
      using A b_closures(2) normal_cell_memE(1) apply auto[1]
      using A \<C>_memE(3) u_inv_maps_to_\<C> by blast
    obtain s where s_def: "s = u_inv (t#x)"
      by blast 
    have s_closed: "s \<in> carrier Q\<^sub>p"
      using tx_closed SA_car_closed s_def u_inv_closed by presburger
    have t_eq: "t = u(s#x)"
      unfolding s_def 
      by (simp add: tx_closed(1) u_u_inv_car)
    have 0: "SA_poly_to_Qp_poly m x g' \<bullet> u (s # x) =
                 (\<alpha> x \<otimes> \<phi> x) \<otimes> (SA_poly_to_Qp_poly m x (UPSA.pderiv m f) \<bullet> s)"
      apply(rule g'_eval_u_car[of s x])
      by (simp add: Qp_pow_ConsI s_closed tx_closed(3))
    have 1: "UPQ.taylor_term (center (normal_cell m b) x) (SA_poly_to_Qp_poly m x g') i \<bullet> t = 
          \<alpha> x \<otimes> \<phi> x \<otimes> (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) i \<bullet> s)"
      unfolding normal_cell_def center.simps
      by(intro g'_taylor_term[of t x s i] s_def tx_closed)
    have sx_in: "s#x \<in> condition_to_set \<C>"
      by (simp add: A s_def u_inv_maps_to_\<C>)
    have 2: "val (SA_poly_to_Qp_poly m x (UPSA.pderiv m f) \<bullet> s)
    \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) i \<bullet> s) + eint N"
      using assms sx_in SA_poly_uboundedE'[of m "UPSA.pderiv m f" c "condition_to_set \<C>" N] 
            unfolding \<C>_eq center.simps by auto 
    show "val (SA_poly_to_Qp_poly m x g' \<bullet> t)
       \<le> val (UPQ.taylor_term (center (normal_cell m b) x) (SA_poly_to_Qp_poly m x g') i \<bullet> t) + eint N"
      unfolding 1 unfolding 0 t_eq 
      apply(intro mult_ineq Qp.Units_m_closed SA_poly_to_Qp_poly_closed UPQ.to_fun_closed
                  UPQ.taylor_term_closed pderiv_closed  f_closed SA_car_closed[of c m]
                  c_closures tx_closed s_closed )
      using SA_Units_nonzero Units_eq_nonzero \<alpha>_closure(2) tx_closed(3) apply presburger
      using SA_Units_nonzero Units_eq_nonzero \<phi>_Unit tx_closed(3) apply presburger
      using 2 by auto 
  qed
  show "g' \<in> carrier (UP (SA m))"
       "center (normal_cell m b) \<in> carrier (SA m)"
       "condition_to_set (normal_cell m b) \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding normal_cell_def condition_to_set.simps center.simps cell_def 
    using g'_closed by auto 
qed

lemma transfer_SA_poly_factors1: 
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "\<exists>u h k. SA_poly_factors p m n g (center \<B>) (condition_to_set \<B>) u h k"
  shows "\<exists>u h k. SA_poly_factors p m n f (center (normalize_cell_inv \<B>))
                                 (condition_to_set (normalize_cell_inv \<B>)) u h k"
proof-
  obtain d where d_def: "d = center \<B>"
    by blast 
  obtain e where e_def: "e = \<phi> \<otimes>\<^bsub>SA m\<^esub> d \<oplus>\<^bsub>SA m\<^esub> c"
    by blast 
  obtain y h k where uhk_def: "SA_poly_factors p m n g d (condition_to_set \<B>) y h k"
    using assms d_def by blast 
  obtain B a1 a2 I where params: "\<B> = Cond m B d a1 a2 I"
    using assms d_def condition_decomp' by blast
  have d_closed: "d \<in> carrier (SA m)"
    unfolding assms 
    using SA_poly_factors_closure(3) assms d_def by force
  have e_center: "e = center (normalize_cell_inv \<B>)"
    unfolding params normalize_cell_inv.simps center.simps e_def  by auto 
  obtain h0 where h0_def: "h0 = inv\<^bsub>SA m\<^esub>\<alpha> \<otimes>\<^bsub>SA m\<^esub> h \<otimes>\<^bsub>SA m\<^esub>inv\<^bsub>SA m\<^esub> \<phi>[^]\<^bsub>SA m\<^esub> k"
    by blast 
  have cl2: "inv\<^bsub>SA m\<^esub> \<alpha> \<in> carrier (SA m)" "h \<in> carrier (SA m)" "inv\<^bsub>SA m\<^esub> \<phi> \<in> carrier (SA m)"
      apply (simp add: \<alpha>_closure(2))
     apply (meson SA_poly_factors_closure(4) uhk_def)
    using SA_Units_inv_closed \<phi>_Unit by presburger
  have h0_closed: "h0 \<in> carrier (SA m)"
    using cl2 unfolding h0_def by blast
  obtain y0 where y0_def: "y0 = (\<lambda> xs.  y (u ((hd xs) # (tl xs)) # (tl xs)))"
    by blast 
  have y0_closed: "y0 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  proof
    fix xs assume a: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    obtain t x where tx_def: "xs = t#x"
      using a by (metis Suc_length_conv cartesian_power_car_memE)
    show "y0 xs \<in> carrier Q\<^sub>p"
      using a u_closed SA_poly_factorsE 
      unfolding y0_def tx_def list_tl list_hd  
      by (metis Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) SA_poly_factors_closure(5) 
          cartesian_power_tail list.sel(3) uhk_def)
  qed
  have 0: "\<And> t x. t # x \<in> condition_to_set \<B> \<Longrightarrow>
    SA_poly_to_Qp_poly m x g \<bullet> t = y (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> d x) [^] k"
    using SA_poly_factorsE[of m n g d "condition_to_set \<B>" y h k] assms uhk_def by presburger
  have 1: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow>
           t # x \<in> condition_to_set (normalize_cell_inv \<B>) \<Longrightarrow>
           val (y0 (t # x)) = 0 \<and>
           SA_poly_to_Qp_poly m x f \<bullet> t = y0 (t # x) [^] n \<otimes> h0 x \<otimes> (t \<ominus> e x) [^] k"
  proof(rule conjI)
    fix t x assume A: "t # x \<in> condition_to_set (normalize_cell_inv \<B>)" " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                      "t \<in> carrier Q\<^sub>p"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A Set.basic_monos(7) cartesian_power_head[of "t#x" Q\<^sub>p m] cartesian_power_tail[of "t#x" Q\<^sub>p m]
      apply (metis (no_types, lifting) assms(2) cell_condition_to_set_subset normalize_cell_inv_arity)
      using A Set.basic_monos(7) \<open>t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> lead_coeff (t # x) \<in> carrier Q\<^sub>p\<close> 
        assms(2) cell_condition_to_set_subset normalize_cell_inv_arity apply fastforce
      using A \<open>t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> tl (t # x) \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)\<close> assms(2) 
        cell_condition_to_set_subset normalize_cell_inv_arity by fastforce
    obtain s where s_def: "s = u (t#x)"
      by blast 
    have s_closed: "s \<in> carrier Q\<^sub>p"
      using tx_closed SA_car_closed s_def u_closed by presburger
    obtain D a1 a2 I 
      where params: "\<B> = Cond m D d a1 a2 I"
      using assms d_def arity.simps by (meson equal_CondI)
    have sx_closed: "s#x \<in> condition_to_set \<B>"
      by (metis s_def A  assms(1) assms(2) normalize_cell_inv_arity normalize_cell_inv_closed 
                normalize_cell_inverse_formula(1) u_maps_to_normalized_cell)
    have 1: "SA_poly_to_Qp_poly m x g \<bullet> s = y (s # x) [^] n \<otimes> h x \<otimes> (s \<ominus> d x) [^] k"
      using 0 [of s x] sx_closed  by auto 
    have 2: "SA_poly_to_Qp_poly m x f \<bullet> t = inv \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x g \<bullet> s)" 
      using g_eval_u_car(2)[of t x] s_def tx_closed(1) by presburger
    have 3: "SA_poly_to_Qp_poly m x f \<bullet> t = inv \<alpha> x \<otimes> (y (s # x) [^] n \<otimes> h x \<otimes> (s \<ominus> d x) [^] k)" 
      unfolding 1 2 by auto 
    have cl: "inv \<alpha> x \<in> carrier Q\<^sub>p"  "y (s # x) [^] n \<in> carrier Q\<^sub>p" "h x \<in> carrier Q\<^sub>p" 
              "(s \<ominus> d x) [^] k \<in> carrier Q\<^sub>p" "inv \<phi> x \<in> carrier Q\<^sub>p" "(t \<ominus> c x) \<in> carrier Q\<^sub>p" 
              "d x \<in> carrier Q\<^sub>p"
         apply (meson SA_Units_memE' SA_car_closed \<alpha>_closure(1) cell_normalization.\<alpha>_closure(2) cell_normalization_axioms field_inv(3) tx_closed(3))
      using A SA_poly_factorsE  apply (meson Qp.nat_pow_closed sx_closed uhk_def)
      using A SA_poly_factorsE  apply (meson SA_car_closed SA_poly_factors_closure(4) tx_closed(3) uhk_def)
      apply (metis Qp.cring_simprules(4) Qp.nat_pow_closed assms(1) assms(2) assms(3) d_def condition_decomp' is_cell_condition_closure'(1) s_closed tx_closed(3))
    using Qp.nonzero_memE(1) SA_Units_nonzero \<phi>_Unit nonzero_inverse_Qp tx_closed(3) apply presburger
    using Qp.cring_simprules(4) SA_car_closed c_closures(1) tx_closed(2) tx_closed(3) apply presburger
    using SA_car_closed d_closed tx_closed(3) by presburger
    have 4: "SA_poly_to_Qp_poly m x f \<bullet> t = (y (s # x) [^] n \<otimes> inv \<alpha> x \<otimes>  h x \<otimes> (s \<ominus> d x) [^] k)"
      unfolding 3 using cl Qp.cring_simprules(11) Qp.cring_simprules(14) by force
    have 5: "s \<ominus> d x = inv \<phi> x \<otimes> (t \<ominus> c x) \<ominus> d x"
      unfolding s_def using u_eval_car[of t x] tx_closed(1) by presburger
    have R: "\<And>  a b c d. \<lbrakk>a \<in> Units Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p; d \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
             inv a \<otimes> (b \<ominus> c) \<ominus> d = inv a \<otimes> (b \<ominus> (c \<oplus> a \<otimes> d))"
      by (smt (verit) Qp.Units_closed Qp.Units_inv_closed Qp.cring_simprules(4) 
                      Qp.cring_simprules(5) Qp.inv_cancelR(1) Qp.r_minus_distr Qp.right_inv_add)
    have 6: "s \<ominus> d x = inv \<phi> x \<otimes> (t \<ominus> (c x \<oplus> \<phi> x \<otimes> d x))"
      unfolding 5 apply(rule R)
      using SA_Units_nonzero Units_eq_nonzero \<phi>_Unit tx_closed(3) apply presburger
      using tx_closed(2) apply blast     
      using SA_car_closed c_closures(1) tx_closed(3) apply presburger
      by (simp add: cl(7))
    have 7: "s \<ominus> d x = inv \<phi> x \<otimes> (t \<ominus> e x)"
      unfolding 6 e_def 
      by (simp add: R.add.m_comm SA_add SA_mult \<phi>_closures(1) c_closures(1) d_closed tx_closed(3))
    have 8: "SA_poly_to_Qp_poly m x f \<bullet> t =
                     (y (s # x) [^] n \<div> \<alpha> x) \<otimes> h x \<otimes> inv \<phi> x  [^] k \<otimes> (t \<ominus> e x) [^] k"
      unfolding 4 7 using cl 
      by (metis (no_types, lifting) Qp.cring_simprules(11) Qp.cring_simprules(4) Qp.nat_pow_closed
                Qp.nat_pow_distrib Qp.nat_pow_eone R.cring_simprules(1) R.cring_simprules(5)
                SA_car_closed UPQ.monom_term_car \<phi>_closures(1) e_def c_closures(1) d_closed 
                tx_closed(2) tx_closed(3))     
    have 9: "SA_poly_to_Qp_poly m x f \<bullet> t =
                     y (s # x) [^] n \<otimes> (inv  \<alpha> x \<otimes> h x \<otimes> (inv (\<phi> x))  [^] k) \<otimes> (t \<ominus> e x) [^] k"
      unfolding 8 
      using cl Qp.cring_simprules(11) Qp.cring_simprules(5) Qp.nat_pow_closed by presburger
    have h0_eval: "h0 x = inv  \<alpha> x \<otimes> h x \<otimes> (inv (\<phi> x)) [^] k"
      using cl2 unfolding h0_def 
      using Qp.m_comm R.Units_pow_closed R.cring_simprules(14) R.cring_simprules(5) R.nat_pow_of_inv SA_Units_closed_fun SA_Units_memE' SA_div_eval SA_nat_pow \<alpha>_closure(2) \<phi>_Unit cl(1) cl(3) field_nat_pow_inv tx_closed(3) by presburger
    have 10: "y (s # x) [^] n = y0 (t # x) [^] n"
      unfolding s_def y0_def list_tl list_hd by auto 
    show 11: "SA_poly_to_Qp_poly m x f \<bullet> t =
                     y0 (t # x) [^] n \<otimes> (h0 x) \<otimes> (t \<ominus> e x) [^] k"
      unfolding 9 10 h0_eval by auto 
    have 12: "val( y(s#x)) = 0"
      using SA_poly_factorsE(1) sx_closed uhk_def by blast
    thus "val (y0 (t # x)) = 0"
      unfolding y0_def list_tl list_hd s_def by auto 
  qed
  have "SA_poly_factors p m n f e (condition_to_set (normalize_cell_inv \<B>)) y0 h0 k"
    apply(rule SA_poly_factorsI)
         apply (metis assms(2) cell_condition_to_set_subset normalize_cell_inv_arity)
    using y0_closed  apply blast
      apply (simp add: \<phi>_closures(1) e_def assms c_closures(1) d_closed)
     apply (simp add: h0_closed)
    using 1 by presburger
  thus ?thesis 
    unfolding e_center by auto 
qed

lemma transfer_SA_poly_factors2: 
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "\<exists>u h k. SA_poly_factors p m n f (center \<B>) (condition_to_set \<B>) u h k"
  shows "\<exists>u h k. SA_poly_factors p m n g (center (normalize_cell \<B>))
                                 (condition_to_set (normalize_cell \<B>)) u h k"
proof-
  obtain d where d_def: "d = center \<B>"
    by blast 
  obtain e where e_def: "e = inv \<^bsub>SA m\<^esub> \<phi> \<otimes>\<^bsub>SA m\<^esub> (d \<ominus>\<^bsub>SA m\<^esub> c)"
    by blast 
  obtain y h k where uhk_def: "SA_poly_factors p m n f d (condition_to_set \<B>) y h k"
    using assms d_def by blast 
  obtain B a1 a2 I where params: "\<B> = Cond m B d a1 a2 I"
    using assms condition_decomp' d_def by blast
  have d_closed: "d \<in> carrier (SA m)"
    unfolding assms 
    using SA_poly_factors_closure(3) assms d_def by force
  have e_center: "e = center (normalize_cell \<B>)"
    unfolding params normalize_cell.simps center.simps e_def by auto 
  obtain h0 where h0_def: "h0 = \<alpha> \<otimes>\<^bsub>SA m\<^esub> h \<otimes>\<^bsub>SA m\<^esub> \<phi>[^]\<^bsub>SA m\<^esub> k"
    by blast 
  have cl2: "\<alpha> \<in> carrier (SA m)" "h \<in> carrier (SA m)" " \<phi> \<in> carrier (SA m)"
      apply (simp add: \<alpha>_closure)
     apply (meson SA_poly_factors_closure(4) uhk_def)
    using SA_Units_closed \<phi>_Unit by presburger
  have h0_closed: "h0 \<in> carrier (SA m)"
    using cl2 unfolding h0_def by blast
  have y_closed: "\<And> x t. t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> y(t#x) \<in> carrier Q\<^sub>p"
    using SA_poly_factorsE uhk_def  SA_poly_factors_closure(5) by force
  have h_closed: "h \<in> carrier (SA m)"
    using SA_poly_factors_closure  uhk_def   by auto 
  obtain y0 where y0_def: "y0 = (\<lambda> xs.  y (u_inv ((hd xs) # (tl xs)) # (tl xs)))"
    by blast 
  have y0_closed: "y0 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
  proof
    fix xs assume a: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    obtain t x where tx_def: "xs = t#x"
      using a by (metis Suc_length_conv cartesian_power_car_memE)
    show "y0 xs \<in> carrier Q\<^sub>p"
      using a u_inv_closed SA_poly_factorsE 
      unfolding y0_def tx_def list_tl list_hd  
      by (metis Qp.function_ring_car_memE Qp_pow_ConsI SA_car_memE(2) SA_poly_factors_closure(5) 
          cartesian_power_tail list.sel(3) uhk_def)
  qed
  have 0: "\<And> t x. t # x \<in> condition_to_set \<B> \<Longrightarrow>
    SA_poly_to_Qp_poly m x f \<bullet> t = y (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> d x) [^] k"
    using SA_poly_factorsE[of m n f d "condition_to_set \<B>" y h k] assms d_def uhk_def by presburger
  have 1: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow>
           t # x \<in> condition_to_set (normalize_cell \<B>) \<Longrightarrow>
           val (y0 (t # x)) = 0 \<and>
           SA_poly_to_Qp_poly m x g \<bullet> t = y0 (t # x) [^] n \<otimes> h0 x \<otimes> (t \<ominus> e x) [^] k"
  proof(rule conjI)
    fix t x assume A: "t # x \<in> condition_to_set (normalize_cell \<B>)" " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                      "t \<in> carrier Q\<^sub>p"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A Set.basic_monos(7) cartesian_power_head[of "t#x" Q\<^sub>p m] cartesian_power_tail[of "t#x" Q\<^sub>p m]
      apply (metis (no_types, lifting) assms(2) cell_condition_to_set_subset normalize_cell_arity)
      using A Set.basic_monos(7) \<open>t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> lead_coeff (t # x) \<in> carrier Q\<^sub>p\<close> 
        assms(2) cell_condition_to_set_subset normalize_cell_inv_arity apply fastforce
      using A \<open>t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> tl (t # x) \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)\<close> assms(2) 
        cell_condition_to_set_subset normalize_cell_inv_arity by fastforce
    obtain s where s_def: "s = u_inv (t#x)"
      by blast 
    have s_closed: "s \<in> carrier Q\<^sub>p"
      using tx_closed SA_car_closed s_def u_inv_closed by presburger
    obtain D a1 a2 I 
      where params: "\<B> = Cond m D d a1 a2 I"
      using assms d_def arity.simps by (meson equal_CondI)
    have sx_closed: "s#x \<in> condition_to_set \<B>"
      by (metis A(1) assms(1) assms(2) normalize_cell_arity normalize_cell_closed normalize_cell_inverse_formula(2) s_def u_inv_maps_from_normalized_cell)
    have 1: "SA_poly_to_Qp_poly m x f \<bullet> s = y (s # x) [^] n \<otimes> h x \<otimes> (s \<ominus> d x) [^] k"
      using 0 [of s x] sx_closed  by auto 
    have 2: "SA_poly_to_Qp_poly m x g \<bullet> t = \<alpha> x \<otimes> (SA_poly_to_Qp_poly m x f \<bullet> s)" 
      using  s_def sx_closed(1) s_def g_eval_s_car(1) tx_closed(1) 
      by presburger
    have 3: "SA_poly_to_Qp_poly m x g \<bullet> t = \<alpha> x \<otimes> (y (s # x) [^] n \<otimes> h x \<otimes> (s \<ominus> d x) [^] k)" 
      unfolding 1 2 by auto 
    have cl: "\<alpha> x \<in> carrier Q\<^sub>p"  "y (s # x) [^] n \<in> carrier Q\<^sub>p" "h x \<in> carrier Q\<^sub>p"
             "(s \<ominus> d x) \<in> carrier Q\<^sub>p" "(s \<ominus> d x) [^] k \<in> carrier Q\<^sub>p" "\<phi> x \<in> carrier Q\<^sub>p"
             "(t \<ominus> c x) \<in> carrier Q\<^sub>p" "d x \<in> carrier Q\<^sub>p"
      using SA_car_closed[of \<alpha> m] SA_car_closed[of h m] SA_car_closed[of d m] SA_car_closed[of c m]
            SA_car_closed[of \<phi> m]  \<alpha>_closure \<phi>_closures(1) c_closures A 
            Qp.nat_pow_closed[of "y (s # x)" n]  Qp.nat_pow_closed[of "s \<ominus> d x" k] y_closed[of t x]
            tx_closed d_closed SA_poly_factorsE[of m n f d "condition_to_set \<B>" y h k ] 
            uhk_def Qp.ring_simprules(4)[of s "d x"] SA_poly_factors_closure sx_closed s_closed
      by auto  
    have 4: "SA_poly_to_Qp_poly m x g \<bullet> t = (y (s # x) [^] n \<otimes> \<alpha> x \<otimes>  h x \<otimes> (s \<ominus> d x) [^] k)"
      unfolding 3 using cl Qp.cring_simprules(11) Qp.cring_simprules(14) by force
    have 5: "s \<ominus> d x = \<phi> x \<otimes> t \<oplus> c x \<ominus> d x"
      unfolding s_def using u_inv_eval_car[of t x] tx_closed(1) by presburger
    have R: "\<And>  a b c d. \<lbrakk>a \<in> Units Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p; d \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
             a \<otimes> b \<oplus> c \<ominus> d = a \<otimes> (b \<ominus> inv a \<otimes> (d \<ominus> c))"
    proof- 
      fix a b c d assume A: "a \<in> Units Q\<^sub>p""b \<in> carrier Q\<^sub>p""c \<in> carrier Q\<^sub>p""d \<in> carrier Q\<^sub>p"
      have 0: "a \<otimes> (b \<ominus> inv a \<otimes> (d \<ominus> c)) = a \<otimes> b \<ominus> a \<otimes> inv a \<otimes> (d \<ominus> c)"
        using A(1) A(2) A(3) A(4) Qp.Units_closed Qp.Units_inv_closed Qp.cring_simprules(11) 
              Qp.m_closed Qp.minus_closed Qp.r_minus_distr by presburger
      show "a \<otimes> b \<oplus> c \<ominus> d = a \<otimes> (b \<ominus> inv a \<otimes> (d \<ominus> c))"
        using A Qp.Units_closed[of a] Qp.Units_inv_closed[of a] unfolding 0 
        by (simp add: Qp.add.inv_mult_group Qp.add.m_assoc a_minus_def)
    qed
    have 6: "s \<ominus> d x = \<phi> x \<otimes> (t \<ominus> (inv \<phi> x \<otimes> (d x \<ominus> c x)))"
      unfolding 5 apply(rule R)
      using SA_Units_nonzero Units_eq_nonzero \<phi>_Unit tx_closed(3) apply presburger
      using tx_closed(2) apply blast     
      using SA_car_closed c_closures(1) tx_closed(3) apply presburger
      by (simp add: cl)
    have 7: "s \<ominus> d x = \<phi> x \<otimes> (t \<ominus> e x)"
      unfolding 6 e_def 
      by (simp add: SA_inv_eval SA_minus_eval SA_mult \<phi>_Unit c_closures(1) d_closed tx_closed(3))
    have 8: "SA_poly_to_Qp_poly m x g \<bullet> t =
                     y (s # x) [^] n \<otimes> (\<alpha> x \<otimes> h x \<otimes>  \<phi> x  [^] k) \<otimes> (t \<ominus> e x) [^] k"
      unfolding 4 7 using cl 
      by (smt (z3) A(3) Qp.cring_simprules(11) Qp.cring_simprules(4) Qp.cring_simprules(5)
          Qp.nat_pow_closed Qp.nat_pow_distrib R.cring_simprules(5) SA_Units_inv_closed 
          SA_car_closed SA_minus_closed \<phi>_Unit c_closures(1) d_closed e_def tx_closed(3))         
    have h0_eval: "h0 x = \<alpha> x \<otimes> h x \<otimes> (\<phi> x) [^] k"
      using cl2 unfolding h0_def  by (simp add: A(2) SA_mult SA_nat_pow)
    have 10: "y (s # x) [^] n = y0 (t # x) [^] n"
      unfolding s_def y0_def list_tl list_hd by auto 
    show 11: "SA_poly_to_Qp_poly m x g \<bullet> t =
                     y0 (t # x) [^] n \<otimes> (h0 x) \<otimes> (t \<ominus> e x) [^] k"
      unfolding 8 10 h0_eval by auto 
    have 12: "val( y(s#x)) = 0"
      using SA_poly_factorsE(1) sx_closed uhk_def by blast
    thus "val (y0 (t # x)) = 0"
      unfolding y0_def list_tl list_hd s_def by auto 
  qed
  have "SA_poly_factors p m n g e (condition_to_set (normalize_cell \<B>)) y0 h0 k"
    apply(rule SA_poly_factorsI)
         apply (metis assms(2) cell_condition_to_set_subset normalize_cell_arity)
        using y0_closed apply blast
        using R.Units_inv_closed R.m_closed SA_minus_closed \<phi>_Unit c_closures(1) d_closed e_def
           apply presburger
     apply (simp add: h0_closed)
    using 1 by presburger
  thus ?thesis 
    unfolding e_center by auto 
qed

lemma transfer_decomp_ubounded: 
  assumes "\<exists>S. is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and> 
                (\<forall> C \<in> S. \<exists>N. SA_poly_ubounded p m g (center C) 
                                (condition_to_set C) N)"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and> 
                (\<forall> C \<in> S. \<exists>N. SA_poly_ubounded p m f (center C) 
                                (condition_to_set C) N)"
proof- 
  obtain S where S_def: "is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and> 
                (\<forall> C \<in> S. \<exists>N. SA_poly_ubounded p m g (center C) 
                                (condition_to_set C) N)"
    using assms by auto 
  obtain S' where S'_def: "S' = normalize_cell_inv ` S"
    by auto 
  have decomp: "is_cell_decomp m S' (condition_to_set \<C>)"
    unfolding S'_def apply(rule transfer_cell_decomp)
    using S_def by auto 
  have bounded: "(\<forall>C\<in>S'. \<exists>N. SA_poly_ubounded p m f (center C) (condition_to_set C) N)"
  proof fix C assume a: "C \<in> S'"
    obtain C0 where C0_def: "C0 \<in> S" " C = normalize_cell_inv C0"
      using S'_def a by blast 
    obtain N where N_def:  "SA_poly_ubounded p m g (center C0) (condition_to_set C0) N"
      using C0_def S_def by auto 
    have " SA_poly_ubounded p m f (center C) (condition_to_set C) N"
      unfolding C0_def 
      apply(intro transfer_SA_poly_ubounded1)
      using C0_def S_def is_cell_decompE N_def by auto 
    thus "\<exists>N. SA_poly_ubounded p m f (center C) (condition_to_set C) N"
      by auto 
  qed
  thus ?thesis using decomp by auto 
qed

lemma transfer_decomp_poly_factors: 
  assumes "is_cell_condition \<B>"
  assumes "arity \<B> = m"
  assumes "\<exists>S. is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and> 
                (\<forall> C \<in> S. \<exists>u h k. SA_poly_factors p m n g (center C) (condition_to_set C) u h k)"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and> 
                (\<forall> C \<in> S. \<exists>u h k. SA_poly_factors p m n f (center C) (condition_to_set C) u h k)"
proof- 
  obtain S where S_def: "is_cell_decomp m S (condition_to_set (normal_cell m b)) \<and> 
                (\<forall> C \<in> S. \<exists>u h k. SA_poly_factors p m n g (center C) (condition_to_set C) u h k)"
    using assms by auto 
  obtain S' where S'_def: "S' = normalize_cell_inv ` S"
    by auto 
  have decomp: "is_cell_decomp m S' (condition_to_set \<C>)"
    unfolding S'_def apply(rule transfer_cell_decomp)
    using S_def by auto 
  have bounded: "(\<forall> C \<in> S'. \<exists>u h k. SA_poly_factors p m n f (center C) (condition_to_set C) u h k)"
  proof fix C assume a: "C \<in> S'"
    obtain C0 where C0_def: "C0 \<in> S" " C = normalize_cell_inv C0"
      using S'_def a by blast 
    show "\<exists>u h k. SA_poly_factors p m n f (center C) (condition_to_set C) u h k"
      unfolding C0_def 
      apply(intro transfer_SA_poly_factors1)
      using C0_def S_def is_cell_decompE  by auto 
  qed
  thus ?thesis using decomp by auto 
qed

end
end


