theory Denef_Lemma_2_4
imports Constructing_Semialgebraic_Functions
begin

section\<open>Denef's Lemma 2.4\<close>

text\<open>Denef's Lemma 2.4 is the second lemma on semialgebraic function construction. The precise 
statement is given below, with minor notational and conventional modificiations:

Assume cell decomposition $II_d$. Let $\xi(x)$ be a semialgebraic function from 
$\mathbb{Q}_p^m \to \mathbb{Q}_p$, $x = (x_1, \dots, x_m)$. Let 
$k \in \mathbb{N}$, $k \geq 2$, $k \leq d+1$. Suppose for every 
$x \in \mathbb{Q}_p^m$ that $\xi(x) \neq 0$, and that $\text{ ord }(\xi(x))$ is a multiple of $k$. 
Then there exists a semialgebraic function $\eta(x)$ from $\mathbb{Q}_p^m \to \mathbb{Q}_p$ such 
that 
\[
\text{ord}(\eta(x)) = \frac{1}{k}\text{ord}(\theta(x)), \text{  for all }x \in \mathbb{Q}_p^m
\]
\<close>
locale denef_lemma_2_4 = denef_II + 
  fixes \<xi> k m
  assumes DL_2_4_0: "k \<ge> 2" 
  assumes DL_2_4_1: "k \<le> Suc d"
  assumes DL_2_4_2: "m > 0"
  assumes DL_2_4_3: "\<xi> \<in> carrier (SA m)"
  assumes DL_2_4_4: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<xi> x \<noteq> \<zero>"
  assumes DL_2_4_5: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<xi> x) mod k = 0"

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Henselian Root Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context denef_lemma_2_4
begin 

lemma unique_kth_root:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "val (a \<ominus> \<one>) > 2*(val ([k]\<cdot>\<one>))"
  shows "\<exists>! b \<in> \<O>\<^sub>p. b[^]k = a \<and> val (b \<ominus> \<one>) > (val ([k]\<cdot>\<one>))"
  using nth_root_poly_root_fixed[of k a] assms DL_2_4_0 
  by (smt Qp.one_closed less_le_trans one_less_numeral_iff semiring_norm(76) val_dist_sym val_ring_memE(2))

lemma unique_kth_root':
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a = eint l * eint k"
  assumes "int e = ord([k]\<cdot>\<one>)"
  assumes "ac (2*e + 1) a = 1"
  shows "\<exists>! b \<in> carrier Q\<^sub>p. b[^]k = a \<and> ac (e+1) b = 1"
proof-
  have k_nonzero: "[k]\<cdot>\<one> \<in> nonzero Q\<^sub>p"
    using DL_2_4_0 by (metis Qp.nat_inc_closed Qp.nonzero_memI Qp_char_0 not_numeral_le_zero)
  obtain c where c_def: "c = \<pp>[^](-ord a)\<otimes>a"
    by blast 
  have A0: "val a = eint (l*k)"
    using assms times_eint_simps(1) by presburger
  have 0: "a \<in> nonzero Q\<^sub>p"
    using A0 assms val_nonzero' val_ring_memE(2) by blast
  have c_nonzero: "c \<in> nonzero Q\<^sub>p"
    by (metis "0" Qp.integral_iff Qp.m_closed Qp.nonzero_closed Qp.not_nonzero_memE Qp_int_pow_nonzero c_def p_nonzero)
  have 1: "ord c = 0"
    unfolding c_def using 0 assms Qp_int_pow_nonzero ord_mult ord_p_pow_int p_nonzero by presburger
  have 2: "val c = 0"
    using 0 val_ord[of c] c_nonzero unfolding 1  by (metis eint_0_iff(2))
  have 3: "ac (2*e+1) c = 1"
    using c_def assms Qp.m_comm ac_p_int_pow_factor_right p_intpow_closed(1) val_ring_memE(2) by presburger
  have 4: "val (c \<ominus> \<one>) \<ge> 2*e+1"
    using 3 c_nonzero ac_ord_prop[of c \<one> 0 "2*e+1"] 
    by (metis "1" Qp.one_nonzero ac_one add.right_neutral add_gr_0 le_add2 ord_one zero_eint_def zero_less_one)
  hence 5: "val (c \<ominus> \<one>) > 2*e"
    by (metis eSuc_eint eSuc_mono iless_Suc_eq of_nat_1 of_nat_add)
  have 6: "c \<in> \<O>\<^sub>p" using c_def 2 val_ring_memI 
    by (metis (mono_tags, opaque_lifting) Qp.add.nat_pow_eone Qp.nonzero_closed Qp.one_closed c_nonzero val_of_nat_inc val_one)
  have 7: "eint (int (2 * e)) = eint 2 * val ([k] \<cdot> \<one>)"
  proof-
    have "eint (int (2 * e)) = 2*eint e"
      using eint_nat_times_2 by blast
    thus ?thesis using val_ord[of "[k]\<cdot>\<one>"] k_nonzero unfolding assms(3) 
      by presburger 
  qed    
  hence 8: "\<exists>! b \<in> \<O>\<^sub>p. b[^]k = c \<and> val (b \<ominus> \<one>) > (val ([k]\<cdot>\<one>))"
    using 6 5 unique_kth_root[of c] by presburger
  then obtain b where b_def: "b \<in> \<O>\<^sub>p \<and> b[^]k = c \<and> val (b \<ominus> \<one>) > (val ([k]\<cdot>\<one>))
                \<and> (\<forall> x \<in> \<O>\<^sub>p. x[^]k = c \<and> val (x \<ominus> \<one>) > (val ([k]\<cdot>\<one>)) \<longrightarrow> x = b)"
    by meson
  obtain d where d_def: "d= \<pp>[^]l \<otimes> b"
    by blast 
  have b_closed: "b \<in> carrier Q\<^sub>p"
    using b_def val_ring_memE(2) by blast
  have "d[^]k = \<pp>[^](k*l) \<otimes> b[^]k"
  proof-
    have "d[^]k = (\<pp>[^]l)[^]k \<otimes> b[^]k"
      unfolding d_def using Qp.nat_pow_distrib b_closed p_natpow_closed(1) p_intpow_closed(1) by presburger
    thus ?thesis using b_closed 
      by (smt Qp_int_pow_pow int_pow_int mult_of_nat_commute of_nat_mult p_nonzero)
  qed
  hence 9: "d[^]k =  \<pp>[^](k*l) \<otimes> c" using b_def by blast 
  have 10: "k*l = ord a" using A0 "0" assms(2) eint.inject val_ord 
    by (metis mult_of_nat_commute)
  have 12: "d[^]k =  a"  unfolding 10 9 c_def 
    by (metis Qp.l_one Qp.m_comm Qp.m_lcomm Qp.nonzero_closed Qp.one_nonzero assms(1) p_intpow_closed(2) p_intpow_inv)
  have 13: "d \<in> carrier Q\<^sub>p"
    unfolding d_def using b_closed p_intpow_closed(1) by blast
  have val_b: "val b = 0"
    using b_def 2 
    by (smt Q\<^sub>p_def Qp.one_closed Zp_def eint_ord_simps(2) not_less padic_fields.val_ineq padic_fields.val_ord' padic_fields_axioms val_of_nat_inc val_one val_ring_memE(1) val_ring_memE(2) val_ultrametric_noteq')
  hence b_nonzero: "b \<in> nonzero Q\<^sub>p"
    using b_def by (metis b_closed val_nonzero' zero_eint_def)
  have 14: "ac (e + 1) b = 1"
  proof-
    have "eint (int (e + 1)) = val([k]\<cdot>\<one>) + 1"
      using assms by (metis enat_eSuc_iff k_nonzero of_nat_1 of_nat_add val_ord)
    hence "eint (int (e + 1)) \<le> val (b \<ominus> \<one>)"
      using b_def ileI1 by presburger
    thus ?thesis 
      using val_b b_def ac_val[of b \<one> "e+1"] b_nonzero one_nonzero val_one assms 
      by (smt Qp.nat_pow_0 ac_p_nat_pow add_gr_0 less_numeral_extra(1) plus_eint_simps(1) zero_eint_def)
  qed
  hence 15: "ac (e+1) d = 1"
    unfolding d_def  using ac_p_int_pow_factor add_gr_0 b_nonzero less_one by presburger
  have 16: "\<And>x. x \<in> carrier Q\<^sub>p \<and> x[^]k = a \<and> ac (e+1) x = 1 \<Longrightarrow> x = d"
  proof- fix x assume A: "x \<in> carrier Q\<^sub>p \<and> x[^]k = a \<and> ac (e+1) x = 1"
    obtain y where y_def: "y = \<pp>[^](-l) \<otimes> x"
      by blast 
    have x_nonzero: "x \<in> nonzero Q\<^sub>p"
      using A by (metis ac_def not_nonzero_Qp  zero_neq_one)
    have "\<pp>[^]-l \<in> nonzero Q\<^sub>p"
      using p_intpow_closed(2) by blast
    hence y_nonzero: "y \<in> nonzero Q\<^sub>p"
      unfolding y_def using x_nonzero Qp.domain_axioms unfolding domain_def domain_axioms_def
      by (metis Qp.nonzero_closed Qp.nonzero_mult_closed not_nonzero_Qp)
    have a_nonzero: "a \<in> nonzero Q\<^sub>p"
      by (simp add: "0")
    have ord_a: "ord a = k*l"
      using assms val_ord  by (metis "10")
    have ord_x: "k*ord x = ord a"
      using A a_nonzero by (metis nonzero_nat_pow_ord x_nonzero)
    hence "ord x = l"
    proof- have "int k \<noteq> 0" using DL_2_4_0  by presburger 
      thus ?thesis unfolding ord_a 
        by (metis mult_cancel_left ord_a ord_x)
    qed
    have 160: "ac (e+1) y = 1"
      unfolding y_def using x_nonzero A ac_p_int_pow_factor by presburger
    have 161: "val y = 0"
      unfolding y_def using ord_x x_nonzero val_ord 
      by (metis  \<open>ord x = l\<close> p_intpow_closed(2) p_intpow_inv' val_mult0 val_one val_p_int_pow y_def)
    have 162: "val (y \<ominus> \<one>) \<ge> e+1"
      using 160 161 y_nonzero ac_ord_prop[of y \<one>] 
      by (metis Qp.one_nonzero ac_one add.right_neutral add_gr_0 eint.inject le_add2 ord_one val_ord zero_eint_def zero_less_one)
    have 163: "a = x[^]k"
      using A by blast 
    have 164: "y[^]k =c"
    proof-
      have 0: "y[^]k = (\<pp>[^](-l) \<otimes> x)[^]k"
        unfolding y_def by blast 
      have "- (- int k) = int k"
        by presburger 
      hence  "y[^]k = \<pp>[^](-k*l) \<otimes> a"
        using A p_int_pow_factor_nat_pow[of x "-l" k] x_nonzero nonzero_closed[of x]
              minus_mult_minus[of l "- int k"] by (metis "0" mult.commute)
      thus "y[^]k =c"
        unfolding 0 c_def ord_a by (metis mult_minus_left)
    qed
    have 165: "val (y \<ominus> \<one>) > val ([k]\<cdot>\<one>)"
    proof-
      have "e + 1 = val([k]\<cdot>\<one>) + 1"
        by (metis assms(3) enat_eSuc_iff k_nonzero of_nat_1 of_nat_add val_ord)
      thus ?thesis using assms 162 
        by (metis eSuc_mono iless_Suc_eq)
    qed
    have 166: "y = b"
      using b_def 162 165 assms 
      by (metis "161" "164" Qp.nonzero_closed order_le_less val_ring_memI y_nonzero)
    hence 167: "\<pp>[^]l \<otimes> y = \<pp>[^]l \<otimes>b"
      by blast
    have "\<pp>[^]l \<otimes> y = x"
      unfolding y_def 
      using Qp.m_comm Qp.m_lcomm Qp.nonzero_closed Qp.r_one p_intpow_closed(1) p_intpow_inv x_nonzero by presburger
    thus "x = d" using 167
      unfolding y_def d_def by blast 
  qed
  then show ?thesis 
    using "12" "13" "15" by metis 
qed

lemma henselian_root_function_closed: 
  assumes "m > 0"
  assumes "f \<in> carrier (SA m)"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "val (f x) = eint l * eint k"
  assumes "e = nat (ord([k]\<cdot>\<one>))"
  assumes "ac (2*e + 1) (f x) = 1"
  shows "kth_rt m k f x \<in> carrier Q\<^sub>p \<and> (kth_rt m k f x)[^]k = f x \<and> ac (e + 1) (kth_rt m k f x) = 1"
proof-
  have 0: "int e = ord ([k] \<cdot> \<one>)"
    using assms(6) DL_2_4_0 
    by (metis Q\<^sub>p_def Qp.nat_inc_closed Zp_def assms(5) int_nat_eq not_numeral_le_zero ord_nonneg padic_fields.Qp_char_0 padic_fields.val_of_nat_inc padic_fields_axioms val_ring_memI)
  have 1: "\<exists>! b \<in> carrier Q\<^sub>p. b[^]k = (f x) \<and> ac (e+1) b = 1"
    apply(rule unique_kth_root'[of _ l]) 
    using function_ring_car_closed SA_car_memE(2) assms(2) assms(3) apply blast
      using assms(4) apply blast
        using 0 apply blast 
          using assms(6) by blast
  have 2: "f x \<in> carrier Q\<^sub>p"
    using assms Qp.function_ring_car_memE SA_car_memE(2) by blast
  have 3: "kth_rt m k f x =  (THE b. b \<in> carrier Q\<^sub>p \<and> b[^]k = (f x) \<and> ac (nat (ord ([k]\<cdot>\<one>)) + 1) b = 1)"
    using assms unfolding kth_rt_def restrict_def by presburger
  have 4: "(nat (ord ([k]\<cdot>\<one>)) + 1) = e + 1"
    using 0 assms by blast
  have 5: "kth_rt m k f x =  (THE b. b \<in> carrier Q\<^sub>p \<and> b[^]k = (f x) \<and> ac (e + 1) b = 1)"
    using 3 unfolding 4 by blast 
  show ?thesis using 1 2 3 the_equality[of "\<lambda>b. b \<in> carrier Q\<^sub>p \<and> b[^]k = (f x) \<and> ac (e+1) b = 1"]
    by (metis (no_types, lifting) "5")    
qed

text\<open>Following Denef's proof of Lemma 2.4, we need to replace the function $\xi$ with a new function
     which has the same valuation as $\xi$ at all points, and a constant angular component. We can 
     then apply hensel's lemma to this function to produce the root function $\eta$ promised in the 
     theorem. \<close>
lemma normalize_ac:
  assumes "e = 2*ord([k]\<cdot>\<one>) + 1"
  shows "\<exists> \<xi>_1 \<in> carrier (SA m). (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<xi>_1 x) = val (\<xi> x) \<and> ac e (\<xi>_1 x) = 1)"
proof-
  obtain G where G_def: "G = (\<lambda>t. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac e (\<xi> x) = t})"
    by blast 
  have 0: "\<And>t. t \<in> Units (Zp_res_ring e) \<Longrightarrow> is_semialgebraic m (G t)"
  proof- fix t assume A: "t \<in> Units (Zp_res_ring e)"
    have "G t = \<xi>  \<inverse>\<^bsub>m\<^esub> (ac_cong_set e t)"
    proof
      show "G t \<subseteq> \<xi> \<inverse>\<^bsub>m\<^esub> ac_cong_set e t" 
      proof(rule subsetI) fix x assume A: "x \<in> G t"
        then have 0: "\<xi> x \<noteq> \<zero>"
          using assms DL_2_4_4 G_def by blast
        have 1: "\<xi> x \<in> carrier Q\<^sub>p"
          using A assms DL_2_4_3 G_def function_ring_car_closed SA_car_memE(2) by blast
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using A unfolding G_def by blast 
        then show "x \<in> \<xi> \<inverse>\<^bsub>m\<^esub> ac_cong_set e t"
          using A DL_2_4_3 0 1
          unfolding mem_Collect_eq evimage_def G_def ac_cong_set_def by blast
      qed
      show " \<xi> \<inverse>\<^bsub>m\<^esub> ac_cong_set e t \<subseteq> G t"
        using A DL_2_4_4 DL_2_4_3 
        unfolding mem_Collect_eq evimage_def G_def ac_cong_set_def  by blast
    qed
    thus "is_semialgebraic m (G t)"
      using assms DL_2_4_3  ac_cong_set_is_univ_semialg[of e t]
      by (smt A evimage_is_semialg neq0_conv of_nat_0)
  qed 
  obtain f where f_def: "f = (\<lambda>S. (SOME t. t \<in> Units (Zp_res_ring e) \<and>  S = G t))"
    by blast
  have 1: "\<And>t. t \<in> Units (Zp_res_ring e) \<Longrightarrow> G t \<noteq> {} \<Longrightarrow> f (G t) = t"
  proof- fix t assume A: "t \<in> Units (Zp_res_ring e)" "G t \<noteq> {}"
    then obtain x where x_def: "x \<in> G t"
      by blast 
    then have 0: "ac e (\<xi> x) = t"
      unfolding G_def by blast 
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using x_def unfolding G_def  by blast
    have "\<And>s. s \<in> Units (Zp_res_ring e) \<Longrightarrow>  G t = G s \<Longrightarrow> s = t"
      using 0 x_def unfolding G_def  
      by (metis (mono_tags, lifting) mem_Collect_eq)
    then show "f (G t) = t"
      using A 0 unfolding f_def  by (metis (mono_tags, lifting) someI_ex)
  qed
  obtain Xs where Xs_def: "Xs = G ` {t \<in> Units (Zp_res_ring e). G t \<noteq> {}}"
    by blast 
  have Xs_finite: "finite Xs"
  proof-
    have "finite (Units (residue_ring (p ^ e)))"
      using assms residues.finite_Units[of "p^e"]  p_residues[of e]  by (smt gr0I of_nat_0)
    thus ?thesis unfolding Xs_def 
    proof -
      have "\<exists>f. G ` {i \<in> Units (residue_ring (p ^ e)). G i \<noteq> {}} \<subseteq> f ` Units (residue_ring (p ^ e))"
        by blast
      then show "finite (G ` {i \<in> Units (residue_ring (p ^ e)). G i \<noteq> {}})"
        by (meson \<open>finite (Units (residue_ring (p ^ e)))\<close> finite_imageI finite_subset)
    qed
  qed
  have 2:  "\<forall> S \<in> Xs. is_semialgebraic m S"
    unfolding Xs_def using 0 by blast 
  have Xs_partitions: "Xs partitions (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
  proof(rule is_partitionI)
    show "disjoint Xs"
    proof(rule disjointI)
      fix A B assume A: "A \<in> Xs" "B \<in> Xs" "A \<noteq> B"
      then obtain s where s_def: "A = G s \<and>  s \<in> Units (Zp_res_ring e)"
        unfolding Xs_def  by blast
      obtain t where t_def: "B = G t \<and> t \<in> Units (Zp_res_ring e)"
        using A unfolding Xs_def by blast 
      have tneqs: "t \<noteq> s"
        using s_def t_def A by blast
      show "A \<inter> B = {}"
      proof
        show "A \<inter> B \<subseteq> {}"
        proof fix x assume A: "x \<in> A \<inter> B"
          then have 0: "ac e (\<xi> x) = s"
            using s_def unfolding G_def by blast 
          have 1: "ac e (\<xi> x) = t"
            using A t_def unfolding G_def by blast 
          show "x \<in> {}"
            using 0 1 tneqs by blast 
        qed
        show "{} \<subseteq> A \<inter> B" 
          by blast 
      qed
    qed
    show "\<Union> Xs = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    proof
      show "\<Union> Xs \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        unfolding Xs_def G_def by blast 
      show "carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<subseteq> \<Union> Xs"
      proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        then have 0: "\<xi> x \<noteq> \<zero>"
          using DL_2_4_4 by blast
        have 1: "\<xi> x \<in> carrier Q\<^sub>p"
          using A DL_2_4_3 function_ring_car_closed SA_car_memE(2) by blast
        have 2: "ac e (\<xi> x) \<in> Units (Zp_res_ring e)"
          using 0 1 ac_units 
          by (smt assms neq0_conv not_nonzero_Qp of_nat_0)
        then have 3: "x \<in> G (ac e (\<xi> x))"
          using A 2 unfolding G_def by blast 
        then have 4: "G (ac e (\<xi> x)) \<in> Xs"
          unfolding Xs_def using 3 2 by blast
        thus "x \<in> \<Union> Xs" using  3 by blast 
      qed
    qed
  qed
  obtain g where g_def: "g = (\<lambda>S. [(inv\<^bsub>Zp_res_ring e\<^esub> (f S))]\<cdot>\<one>)"
    by blast 
  have 3: "\<And> S x. S \<in> Xs \<Longrightarrow> x \<in> S \<Longrightarrow> g S \<in> nonzero Q\<^sub>p \<and> ac e (g S \<otimes> (\<xi> x)) = 1"
  proof-
    fix S x assume A: "S \<in> Xs" "x \<in> S"
    then obtain t where t_def: "t \<in> Units (Zp_res_ring e) \<and> S = G t"
      unfolding Xs_def by blast 
    then have 30: "f S = t"
      using 1[of t] A t_def unfolding Xs_def 
      by (metis empty_iff)
    then have 31: "g S = [(inv\<^bsub>Zp_res_ring e\<^esub> t)]\<cdot>\<one>"
      unfolding g_def by blast 
    have 32: "(inv\<^bsub>Zp_res_ring e\<^esub> t) \<in> Units (Zp_res_ring e)"
      using t_def by (smt assms cring_def neq0_conv of_nat_0 padic_integers.R_cring padic_integers_axioms ring.Units_inverse)
    hence 33: "ac e (g S) = inv\<^bsub>Zp_res_ring e\<^esub> t"
      unfolding 31 using ac_res_Unit_inc[of e] assms  by (smt neq0_conv of_nat_0)
    have 34: "g S \<in> nonzero Q\<^sub>p" using 32 unfolding 31  
      by (smt Qp.int_mult_closed Qp.one_closed Qp_char_0_int assms less_one less_or_eq_imp_le linorder_neqE_nat not_nonzero_Qp of_nat_0 zero_not_in_residue_units)
    then show "g S \<in> nonzero Q\<^sub>p \<and> ac e (g S \<otimes> \<xi> x) = 1"
      using 33 ac_mult[of "g S" "\<xi> x" e ] 32 t_def 31 
      by (smt A(2) DL_2_4_3 DL_2_4_4 function_ring_car_closed G_def Qp.nonzero_closed SA_car_memE(2) ac_inv ac_inv'''(1) assms mem_Collect_eq neq0_conv not_nonzero_Qp of_nat_0 residue_mult_comm)
  qed
  obtain F where F_def: "F = (\<lambda>S. (g S) \<odot>\<^bsub>SA m\<^esub> \<xi>)"
    by blast 
  have F_closed: "\<And>S. S \<in> Xs \<Longrightarrow> F S \<in> carrier (SA m)"
    using 3 unfolding F_def Xs_def using DL_2_4_3 DL_2_4_2 Qp.int_inc_closed SA_smult_closed g_def by presburger
  obtain \<xi>_1 where xi1_def: "\<xi>_1 = parametric_fun_glue m Xs F"
    by blast 
  have xi1_closed: "\<xi>_1 \<in> carrier (SA m)"
    unfolding xi1_def apply(rule parametric_fun_glue_is_SA)       
      using Xs_finite apply blast 
     apply (simp add: Xs_partitions)
    using F_closed apply blast 
   using 2 by blast 
  have xi1_val: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (\<xi> x) = val (\<xi>_1 x)"
  proof-
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    then obtain S where S_def: "S \<in> Xs \<and> x \<in> S"
      using Xs_partitions is_partitionE by blast 
    then have "\<xi>_1 x =  ((g S) \<odot>\<^bsub>SA m\<^esub> \<xi>) x"
      using parametric_fun_glue_formula[of Xs m x S F] Xs_partitions
      unfolding F_def xi1_def by blast
    hence "\<xi>_1 x =  (g S) \<otimes> \<xi> x"
      using A DL_2_4_3 Qp.int_mult_closed SA_smult_formula g_def by blast
    hence *: "val (\<xi>_1 x) = val (g S) + val (\<xi> x)"
      using 3 A val_mult[of "g S" "\<xi> x"] DL_2_4_3 function_ring_car_closed Qp.int_inc_closed SA_car_memE(2) g_def val_mult by presburger
    have "(inv\<^bsub>Zp_res_ring e\<^esub> (f S)) \<in> Units (Zp_res_ring e)"
      by (smt "1" S_def Xs_def assms cring_def imageE mem_Collect_eq neq0_conv of_nat_0 padic_integers.R_cring padic_integers_axioms ring.Units_inverse)
    hence "val (g S) = 0"
      unfolding g_def using val_of_res_Unit by (smt assms gr0I of_nat_0)
    thus "val (\<xi> x) = val (\<xi>_1 x)"
      using * by (metis add.left_neutral)
  qed
  have xi1_ac: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ac e (\<xi>_1 x) = 1"
  proof-
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    then obtain S where S_def: "S \<in> Xs \<and> x \<in> S"
      using Xs_partitions is_partitionE by blast 
    then have "\<xi>_1 x =  ((g S) \<odot>\<^bsub>SA m\<^esub> \<xi>) x"
      using parametric_fun_glue_formula[of Xs m x S F] Xs_partitions
      unfolding F_def xi1_def by blast
    hence "\<xi>_1 x =  (g S) \<otimes> \<xi> x"
      using A DL_2_4_3 Qp.int_mult_closed SA_smult_formula g_def by blast
    thus "ac e (\<xi>_1 x) = 1"
      using 3[of S x] S_def by presburger
  qed
  show ?thesis 
    by (metis xi1_ac xi1_closed xi1_val)
qed

text\<open>The parameter $e$ from the first sentence of the proof:\<close>
definition e where 
"e = nat (ord ([k]\<cdot>\<one>))"

lemma e_eq:
"int e = ord ([k]\<cdot>\<one>)"
  unfolding e_def  by (metis Q\<^sub>p_def Qp.nat_inc_closed Zp_def denef_lemma_2_4.DL_2_4_0 
      denef_lemma_2_4_axioms nat_0_le ord_nonneg padic_fields.Qp_char_0 padic_fields_axioms 
      rel_simps(28) val_of_nat_inc val_ring_memI)

lemma e_eq':
"int (2 * e + 1) = 2 * ord ([k] \<cdot> \<one>) + 1"
  using e_eq by linarith

definition \<xi>_1 where 
"\<xi>_1 = (SOME \<xi>_1. \<xi>_1 \<in> carrier (SA m) \<and> (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<xi>_1 x) = val (\<xi> x) \<and> 
                                      ac (2 * e + 1) (\<xi>_1 x) = 1))"

lemma \<xi>_1_characterization: 
"\<xi>_1 \<in> carrier (SA m)\<and> (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<xi>_1 x) = val (\<xi> x) \<and> ac (2 * e + 1) (\<xi>_1 x) = 1)"
proof-
  have "\<exists>\<xi>_1\<in>carrier (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<xi>_1 x) = val (\<xi> x) \<and> ac (2 * e + 1) (\<xi>_1 x) = 1"
    using e_eq' normalize_ac[of "2*e+1"] by blast
  thus ?thesis unfolding  \<xi>_1_def
    using verit_sko_ex[of "\<lambda> \<xi>_1. \<xi>_1\<in>carrier (SA m) \<and>( \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<xi>_1 x) = val (\<xi> x) \<and> ac (2 * e + 1) (\<xi>_1 x) = 1)"] 
    by blast 
qed

lemma \<xi>_1_closed: 
"\<xi>_1 \<in> carrier (SA m)"
  using \<xi>_1_characterization by blast 

lemma \<xi>_1_val: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "val (\<xi>_1 x) = val (\<xi> x)"
  using assms \<xi>_1_characterization by blast 

lemma \<xi>_1_ac: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "ac (2 * e + 1) (\<xi>_1 x) = 1"
  using assms \<xi>_1_characterization by blast 

lemma \<xi>_1_nonzero: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "\<xi>_1 x \<in> nonzero Q\<^sub>p"
  apply(rule val_nonzero[of  _ "val (\<xi> x) + 1"])
  using \<xi>_1_closed assms function_ring_car_closed SA_car_memE(2) \<xi>_1_closed apply blast
  using \<xi>_1_val[of x] assms by (metis DL_2_4_4 Q\<^sub>p_def Zp_def iless_Suc_eq neq_iff not_less 
        padic_fields.val_def padic_fields_axioms)

lemma \<xi>_1_ord: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "ord (\<xi>_1 x) = ord (\<xi> x)"
  using \<xi>_1_nonzero \<xi>_1_val 
  by (metis (no_types, lifting) DL_2_4_3 DL_2_4_4 function_ring_car_closed Qp.fun_struct_maps
      Qp.nonzero_memI assms eint.inject padic_fields.SA_car padic_fields_axioms
      semialg_functions_memE(2) val_ord)

text\<open>The function $\eta$ is what we will eventually prove to be semialgebraic in Lemma 2.4.\<close>
definition \<eta> where 
"\<eta> = kth_rt m k \<xi>_1"

lemma mod_zero_E:
  assumes "(a::int) mod k = 0"
  shows "\<exists>l. a = l*int k" 
  using assms mult_of_nat_commute by blast

lemma \<eta>_characterization: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" 
  shows "\<eta> x \<in> carrier Q\<^sub>p \<and> (\<eta> x)[^]k = \<xi>_1 x \<and> ac (e+1) (\<eta> x) = 1"
proof-
   obtain l::int where l_def: "ord (\<xi> x) = l*k"
      using assms DL_2_4_5[of x] mod_zero_E[of "ord (\<xi> x)" ] by metis 
    hence  1: "ord (\<xi>_1 x) = l*k" using \<xi>_1_characterization
      by (metis assms DL_2_4_3 function_ring_car_closed Q\<^sub>p_def SA_car_memE(2) Zp_def eint.inject padic_fields.val_nonzero' padic_fields.val_ord padic_fields.val_ord' padic_fields_axioms)
    show "\<eta> x \<in> carrier Q\<^sub>p \<and> (\<eta> x)[^]k = \<xi>_1 x \<and> ac (e+1) (\<eta> x) = 1"
      unfolding \<eta>_def apply(rule henselian_root_function_closed[of _ _ l])
      using DL_2_4_2 apply auto[1] 
        using \<xi>_1_closed apply blast
          using assms apply blast
            using l_def \<xi>_1_nonzero[of x] val_ord[of "\<xi>_1 x"]
              using "1" assms times_eint_simps(1) apply presburger
                using e_def apply blast        
                  using \<xi>_1_ac[of x] assms by blast 
qed                    

lemma \<eta>_closed: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" 
  shows "\<eta> x \<in> carrier Q\<^sub>p"
  using assms \<eta>_characterization by blast

lemma \<eta>_pow: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" 
  shows "(\<eta> x)[^]k = \<xi>_1 x"
  using assms \<eta>_characterization by blast

lemma \<eta>_ac: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" 
  shows "ac (e+1) (\<eta> x) = 1"
  using assms \<eta>_characterization by blast

lemma \<eta>_nonzero: 
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "\<eta> x \<in> nonzero Q\<^sub>p"
  using assms \<eta>_ac[of x] \<eta>_pow[of x]
  by (metis Qp_nonzero_nat_pow \<eta>_closed \<xi>_1_nonzero denef_lemma_2_4.DL_2_4_0 denef_lemma_2_4_axioms neq0_conv not_numeral_le_zero)

lemma \<eta>_val:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "k*val (\<eta> x) = val(\<xi> x)"
proof-
  have "k*val (\<eta> x) = val(\<xi>_1 x)"
    using \<eta>_nonzero[of x] \<eta>_pow[of x] assms val_of_power[of "\<eta> x" k]
    by presburger
  thus ?thesis 
    using \<xi>_1_val assms by presburger
qed

lemma \<eta>_ord:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  shows "k*ord (\<eta> x) = ord(\<xi> x)"
  using assms \<eta>_val 
  by (metis (mono_tags, lifting) Q\<^sub>p_def Zp_def \<eta>_nonzero \<eta>_pow \<xi>_1_nonzero \<xi>_1_val 
      denef_lemma_2_4.DL_2_4_4 denef_lemma_2_4_axioms eint.inject nonzero_nat_pow_ord 
      padic_fields.val_def padic_fields_axioms val_ord)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Six Sublemmas\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text\<open>Following Denef's approach, below we have the facts which he numbers i) through vi) in his 
proof of Lemma 2.4. All of these lemmas pertain to showing that $\eta$ exhibits common traits with 
semialgebraic functions. Facts i) and ii) focus on showing that inverse images by $\eta$ of certain 
important one-dimensional semialgebraic sets are stil semialgebraic, while iii) to vi) focus on 
showing that it is possible to reduce questions of n-th power residues and angular components of 
values of the form $\eta(x)$ to facts which only depend on those quantities computed for related 
semialgebraic functions.\<close>
subsubsection\<open>Fact i)\<close>
lemma fact_i:
  assumes "n > 0"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<eta> x) mod n = \<beta>}"
proof-
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> k*ord (\<eta> x) = ord (\<xi>_1 x)"
    using \<eta>_ord \<xi>_1_ord by presburger
  have 1: "\<And>i. i mod n = \<beta> \<longleftrightarrow> (int k)*i mod ((int k)*n) = (int k)*\<beta>" 
    by (metis DL_2_4_0 mult_cancel_left mult_mod_right nat_int nat_zero_as_int rel_simps(28))
  have 2: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (ord (\<eta> x) mod n = \<beta>  \<longleftrightarrow>  ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>)" 
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" show " (ord (\<eta> x) mod n = \<beta>  \<longleftrightarrow>  ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>)" 
    using A 0[of x] 1[of "ord (\<eta> x)"]  
    by presburger
  qed 
  hence 3: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<eta> x) mod n = \<beta>} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>}"
    by blast
  have 4: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>}"
  proof-
    have 40: " {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>} = 
             {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<xi>_1 x \<in> nonzero Q\<^sub>p \<and> ord (\<xi>_1 x) mod ((int k)*n) = (int k)*\<beta>}"
      using \<xi>_1_nonzero by blast
    have 41: "0 < int k * n"
      using assms DL_2_4_2 DL_2_4_0 
      by (metis gr0I not_numeral_le_zero of_nat_0_less_iff zero_less_mult_iff)
    have 42: "\<xi>_1 \<in> carrier (SA (m + 0))"
      by (simp add: \<xi>_1_closed)
    thus ?thesis unfolding 40 
      using 41 42  assms DL_2_4_2 DL_2_4_0  ord_congruence_set_SA_function[of "int k * n"  \<xi>_1 m 0 "int k * \<beta>"]
      by (smt Collect_cong Nat.add_0_right)     
  qed
  then show ?thesis unfolding  3 by metis 
qed
  
lemma fact_i_take':
  assumes "n > 0"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) mod n = \<beta>}"
proof-
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) mod n = \<beta>} = take m  \<inverse>\<^bsub>m+l\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<eta> x) mod n = \<beta>}"
    by (smt Collect_cong evimage_Collect_eq le_add1 local.take_closed)
  thus ?thesis using fact_i[of n \<beta>] 
    by (metis (no_types, lifting) DL_2_4_2 Q\<^sub>p_def Zp_def add_gr_0 assms le_add1 padic_fields.semialg_map_evimage_is_semialg padic_fields_axioms take_is_semialg_map)
qed

lemma fact_i':
  assumes "g \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). k*val (\<eta> (take m x)) \<le> k*val (g x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). eint (int k) * val (\<eta> (take m x)) \<le> eint (int k) * val (g x)}"
      apply(rule subsetI) using eint_nat_mult_mono by blast
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). eint (int k) * val (\<eta> (take m x)) \<le> eint (int k) * val (g x)}
            \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
      apply(rule subsetI) using eint_nat_mult_mono_rev 
      by (metis (no_types, lifting) DL_2_4_0 add.commute mem_Collect_eq not_gr0 not_numeral_le_zero)
  qed   
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<xi>_1 (take m x)) \<le> val ((g[^]\<^bsub>SA (m+l)\<^esub>k) x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<le> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}"
      apply(rule subsetI)  using 0 unfolding mem_Collect_eq using \<eta>_val 
      by (smt DL_2_4_0 function_ring_car_closed Qp.nat_pow_closed Qp_nonzero_nat_pow SA_car_memE(2) SA_nat_pow \<xi>_1_val add_gr_0 assms eint_nat_mult_mono le_add1 le_add_diff_inverse local.take_closed not_less not_numeral_le_zero val_nonzero val_of_power)
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<le> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
     apply(rule subsetI)  using 0 unfolding mem_Collect_eq using \<eta>_val 
      by (smt DL_2_4_0 function_ring_car_closed SA_car_memE(2) SA_nat_pow \<xi>_1_val add_gr_0 assms eint_nat_mult_mono_rev le_add1 le_add_diff_inverse local.take_closed not_less not_numeral_le_zero val_nonzero val_of_power)
  qed
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<le> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)} = 
                    {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (fun_inc (m + l) m \<xi>_1 x) \<le> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}"
    using fun_inc_eval[of _ "m+l" m \<xi>_1] 
    by (metis (no_types, lifting))
  have 3: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<xi>_1 (take m x)) \<le> val ((g[^]\<^bsub>SA (m+l)\<^esub>k) x)}"
    using semialg_val_ineq_set_is_semialg[of "fun_inc (m+l) m \<xi>_1" "m+l"  "g[^]\<^bsub>SA (m+l)\<^esub>k"] 2 
          DL_2_4_2 \<xi>_1_closed add_gr_0 assms fun_inc_closed le_add1 padic_fields.SA_car_memE(1) 
          padic_fields.SA_nat_pow_closed padic_fields_axioms by presburger
  thus ?thesis unfolding 1 by metis 
qed

lemma fact_i'_geq:
  assumes "g \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). k*val (\<eta> (take m x)) \<ge> k*val (g x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). eint (int k) * val (\<eta> (take m x)) \<ge> eint (int k) * val (g x)}"
      apply(rule subsetI) using eint_nat_mult_mono by blast
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). eint (int k) * val (\<eta> (take m x)) \<ge> eint (int k) * val (g x)}
            \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}"
      apply(rule subsetI) using eint_nat_mult_mono_rev 
      by (metis (no_types, lifting) DL_2_4_0 add.commute mem_Collect_eq not_gr0 not_numeral_le_zero)
  qed   
  have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<xi>_1 (take m x)) \<ge> val ((g[^]\<^bsub>SA (m+l)\<^esub>k) x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<ge> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}"
      apply(rule subsetI)  using 0 unfolding mem_Collect_eq using \<eta>_val 
      by (metis (no_types, lifting) function_ring_car_closed SA_car_memE(2) SA_nat_pow \<eta>_closed \<eta>_nonzero \<xi>_1_val assms eint_nat_mult_mono le_add1 local.take_closed val_ineq val_nonzero' val_of_power val_ord')
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<ge> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}"
     apply(rule subsetI)  using 0 unfolding mem_Collect_eq using \<eta>_val 
      by (smt function_ring_car_closed Qp.nat_pow_closed Qp.nonzero_closed Qp_nonzero_nat_pow SA_car_memE(2) SA_nat_pow \<xi>_1_nonzero \<xi>_1_val assms denef_lemma_2_4.DL_2_4_0 denef_lemma_2_4_axioms eint_nat_mult_mono_rev le_add1 local.take_closed neq0_conv not_numeral_le_zero val_ineq val_nonzero' val_of_power val_ord')
  qed
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<xi>_1 (take m x)) \<ge> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)} = 
                    {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (fun_inc (m + l) m \<xi>_1 x) \<ge> val ((g [^]\<^bsub>SA (m + l)\<^esub> k) x)}"
    using fun_inc_eval[of _ "m+l" m \<xi>_1] 
    by (metis (no_types, lifting))
  have 3: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<xi>_1 (take m x)) \<ge> val ((g[^]\<^bsub>SA (m+l)\<^esub>k) x)}"
    using semialg_val_ineq_set_is_semialg[of  "g[^]\<^bsub>SA (m+l)\<^esub>k" "m+l"  "fun_inc (m+l) m \<xi>_1"] 2 
          DL_2_4_2 \<xi>_1_closed add_gr_0 assms fun_inc_closed le_add1 padic_fields.SA_car_memE(1) 
          padic_fields.SA_nat_pow_closed padic_fields_axioms 
    by presburger         
  thus ?thesis unfolding 1 by metis 
qed

lemma fact_i'_eq:
  assumes "g \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (g x)} = {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (\<eta> (take m x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (\<eta> (take m x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
      apply(rule subsetI) 
      by (metis (mono_tags, lifting) Int_Collect mem_Collect_eq order_le_less)
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (\<eta> (take m x))} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (g x)}"
      apply(rule subsetI)
  by (metis (mono_tags, lifting) Int_Collect mem_Collect_eq not_less order_le_less)
  qed
  show ?thesis unfolding 0  using fact_i'_geq[of g l] fact_i'[of g l] assms
        intersection_is_semialg[of "m+l" " {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (\<eta> (take m x))}" "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"]
    by blast   
qed

lemma fact_i'_le:
  assumes "g \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) < val (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>).  val (\<eta> (take m x)) < val (g x)} =  carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}"
    using linorder_not_le by blast
  show ?thesis unfolding 0
   using assms fact_i'_geq[of g l] complement_is_semialg[of "m+l"] 
   by blast
qed

lemma fact_i'_gr:
  assumes "g \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) > val (g x)}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>).  val (\<eta> (take m x)) > val (g x)} =  carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
    using linorder_not_le by blast
  show ?thesis unfolding 0
   using assms fact_i'[of g l] complement_is_semialg[of "m+l"] 
   by blast
qed

lemma fact_i_take:
  assumes "c \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) = ord (c x) + i}"
proof-
  obtain h where h_def: "h = \<pp>[^]i \<odot>\<^bsub>SA (m+l)\<^esub>c"
    by blast 
  have h_closed: "h \<in> carrier (SA (m+l))"
    using h_def assms SA_smult_closed  
    by (meson DL_2_4_2 add_gr_0 p_intpow_closed(1))
  have h_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> h x = \<pp>[^]i \<otimes> c x"
    unfolding h_def 
    using SA_smult_formula assms p_intpow_closed(1) by blast
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>c x \<in> nonzero Q\<^sub>p\<Longrightarrow> val (h x) = ord (c x) + i"
    using Qp.nonzero_closed h_eval plus_eint_simps(1) times_p_pow_val val_ord by presburger
  have 1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>c x \<in> nonzero Q\<^sub>p\<Longrightarrow> (h x) \<in> nonzero Q\<^sub>p"
    by (meson "0" function_ring_car_closed SA_car_memE(2) h_closed val_nonzero')
  have 2: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (h x) \<Longrightarrow> h x \<in> nonzero Q\<^sub>p"
    by (metis function_ring_car_closed SA_car_memE(2) \<eta>_nonzero h_closed le_add1 local.take_closed val_nonzero' val_ord)
  have 3: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (h x) \<Longrightarrow> c x \<in> nonzero Q\<^sub>p"
    using h_def h_eval 
    by (metis "2" function_ring_car_closed Qp.integral_iff SA_car_memE(2) assms not_nonzero_Qp p_intpow_closed(1))
  have 4: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) = ord (c x) + i}
            = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (h x)} "
    apply(rule subset_antisym)
     apply(rule subsetI)  unfolding mem_Collect_eq using assms 0 1 
     apply (metis \<eta>_nonzero le_add1 local.take_closed val_ord)
    apply(rule subsetI)
    unfolding mem_Collect_eq using assms 2 3 
    by (metis "0" \<eta>_nonzero eint.inject le_add1 local.take_closed val_ord)
  show ?thesis unfolding 4 
    using Q\<^sub>p_def Zp_def denef_lemma_2_4.fact_i'_eq denef_lemma_2_4_axioms h_closed 
    by presburger    
qed

subsubsection\<open>Fact ii)\<close>
   
lemma fact_ii:
  assumes "\<alpha> > 0"
  assumes "t \<in> Units (Zp_res_ring \<alpha>)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t}"
proof-
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (ac \<alpha> (\<eta> x))^k mod p^\<alpha>  = ac \<alpha> (\<xi>_1 x)"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    then have 00: "\<eta> x \<in> nonzero Q\<^sub>p"
      using \<eta>_nonzero by blast
    have 01: "\<eta> x [^]k = \<xi>_1 x"
      using A  \<eta>_pow[of x] by blast 
    show "(ac \<alpha> (\<eta> x))^k mod p^\<alpha>  = ac \<alpha> (\<xi>_1 x)"
      using 00 01 A by (metis ac_nat_pow)
  qed
  have 1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> angular_component (\<eta> x) [^]\<^bsub>Z\<^sub>p\<^esub> k  = angular_component (\<xi>_1 x)"
    using angular_component_nat_pow \<eta>_nonzero \<eta>_pow by metis
  have 2: "\<And>x x'. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ac (e+\<alpha>) (\<xi>_1 x) = ac (e+\<alpha>) (\<xi>_1 x')
                  \<Longrightarrow> ac \<alpha> (\<eta> x) = ac \<alpha> (\<eta> x')"
  proof- fix x x' 
    assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "ac (e+\<alpha>) (\<xi>_1 x) = ac (e+\<alpha>) (\<xi>_1 x')"
    show "ac \<alpha> (\<eta> x) = ac \<alpha> (\<eta> x')"
    proof-
      obtain a where a_def: "a = angular_component (\<eta> x)"
        by blast 
      obtain a' where a'_def: "a' = angular_component (\<eta> x')"
        by blast 
      obtain b where b_def: "b = angular_component (\<xi>_1 x)"
        by blast 
      obtain b' where b'_def: "b' = angular_component (\<xi>_1 x')"
        by blast 
      have a_closed: "a \<in> carrier Z\<^sub>p"
        using A a_def assms angular_component_closed \<eta>_nonzero by blast
      have a'_closed: "a' \<in> carrier Z\<^sub>p"
        using A a'_def assms angular_component_closed \<eta>_nonzero by blast
      have b_closed: "b \<in> carrier Z\<^sub>p"
        using A b_def assms angular_component_closed \<xi>_1_nonzero by blast
      have b'_closed: "b' \<in> carrier Z\<^sub>p"
        using A b'_def assms angular_component_closed \<xi>_1_nonzero by blast
      have a_val: "val_Zp a = 0"
        using A a_def assms angular_component_unit \<eta>_nonzero unit_imp_val_Zp0 by blast
      have a'_val: "val_Zp a' = 0"
        using A a'_def assms angular_component_unit \<eta>_nonzero unit_imp_val_Zp0 by blast
      have b_val: "val_Zp b = 0"
        using A b_def assms angular_component_unit \<xi>_1_nonzero unit_imp_val_Zp0 by blast
      have b'_val: "val_Zp b' = 0"
        using A b'_def assms angular_component_unit \<xi>_1_nonzero unit_imp_val_Zp0 by blast
      have a_pow: "a[^]\<^bsub>Z\<^sub>p\<^esub>k = b"
        unfolding a_def b_def         using "1" A(1) by blast
      have a'_pow: "a'[^]\<^bsub>Z\<^sub>p\<^esub>k = b'"
        unfolding a'_def b'_def using "1" A(2) by blast
      have b_b'_cong: "b (e+\<alpha>) = b' (e+\<alpha>)"
        unfolding b_def b'_def using A \<xi>_1_nonzero unfolding ac_def 
        by (metis Qp.not_nonzero_memI)
      obtain g where g_def: "g = up_ring.monom (UP Z\<^sub>p) \<one>\<^bsub>Z\<^sub>p\<^esub> k \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> up_ring.monom (UP Z\<^sub>p) b 0"
        by blast 
      obtain g' where g'_def: "g' = up_ring.monom (UP Z\<^sub>p) \<one>\<^bsub>Z\<^sub>p\<^esub> k \<ominus>\<^bsub>UP Z\<^sub>p\<^esub> up_ring.monom (UP Z\<^sub>p) b' 0"
        by blast 
      have g_closed: "g \<in> carrier (UP Z\<^sub>p)"
        unfolding g_def 
        by (meson Zp.P.minus_closed Zp.is_UP_monomE(1) Zp.is_UP_monomI Zp.one_closed b_closed)
      have g'_closed: "g' \<in> carrier (UP Z\<^sub>p)"
        unfolding g'_def         
        by (meson Zp.P.minus_closed Zp.is_UP_monomE(1) Zp.is_UP_monomI Zp.one_closed b'_closed)
      have g_eval: "\<And>c. c \<in> carrier Z\<^sub>p \<Longrightarrow> to_function Z\<^sub>p g c = c[^]\<^bsub>Z\<^sub>p\<^esub>k \<ominus>\<^bsub>Z\<^sub>p\<^esub> b"
        using Zp.is_UP_monomE(1) Zp.is_UP_monomI Zp.one_closed b_closed
        unfolding g_def using b_closed Zp.to_fun_minus Zp.to_fun_const Zp.to_fun_monic_monom 
        by (metis Zp.to_fun_def Zp.to_fun_monom to_fun_monom_minus)        
      hence g_at_a: "Zp.to_fun g a = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
        using Zp.r_right_minus_eq a_pow b_closed local.a_closed Zp.to_fun_def by presburger     
      have g_at_a': "Zp.to_fun g a' = a'[^]\<^bsub>Z\<^sub>p\<^esub>k \<ominus>\<^bsub>Z\<^sub>p\<^esub> b"
        using g_eval[of a'] a'_closed  Zp.to_fun_def by presburger    
      have "\<exists>c \<in> carrier Z\<^sub>p. Zp.to_fun g a' =  
          Zp.to_fun g a \<oplus>\<^bsub>Z\<^sub>p\<^esub> (derivative Z\<^sub>p g a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)"
        using UP_cring.taylor_deg_1_expansion[of Z\<^sub>p g a a']
        by (meson Zp.taylor_closed Zp.minus_closed Zp.shift_closed Zp.to_fun_closed Zp_x_is_UP_cring a'_closed g_closed local.a_closed)
      then obtain c where c_def: "c \<in> carrier Z\<^sub>p \<and> 
            Zp.to_fun g a' = (derivative Z\<^sub>p g a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)"
        using g_at_a  by (metis Zp.add.r_cancel_one Zp.deriv_closed Zp.m_closed Zp.minus_closed Zp.to_fun_def 
            Zp.zero_closed a'_closed g_closed local.a_closed)
      have g_deriv: "Zp.pderiv g =  up_ring.monom (UP Z\<^sub>p) ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) (k-1)"
        using UP_cring.pderiv_minus_const 
        by (metis Zp.is_UP_monomE(1) Zp.is_UP_monomI Zp.one_closed Zp.pderiv_monom Zp_x_is_UP_cring b_closed g_def)
      hence 0: "derivative Z\<^sub>p g a = [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)"
        using Zp.pderiv_eval_deriv Zp.to_fun_monom Zp_nat_inc_closed g_closed local.a_closed by presburger
      have 1: "Zp.to_fun g a' = ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)"
        using c_def unfolding 0 by blast 
      have 2: "b' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b  = ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)"
        using 1 unfolding g_at_a' a'_pow  by blast 
      have "a \<alpha> = a' \<alpha>"
      proof(cases "a = a'")
        case True
        then show ?thesis by blast 
      next
        case False
        obtain l where l_def: "val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) = eint l"
          using False Zp.r_right_minus_eq a'_closed local.a_closed val_ord_Zp by blast
        have 3: "a'\<ominus>\<^bsub>Z\<^sub>p\<^esub>a \<in> nonzero Z\<^sub>p"
          using False Zp.not_eq_diff_nonzero a'_closed local.a_closed by metis
        have 4: "val_Zp (c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)) \<ge> val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)+ val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"
        proof-
          have 40: "val_Zp c \<ge> 0"
            using c_def val_pos by blast
          have 41: "val_Zp ((a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat)) = val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)+ val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"
          proof- 
            have "a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p"
              using a'_closed local.a_closed by blast
            have "(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a) [^]\<^bsub>Z\<^sub>p\<^esub> (2::nat) = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"
              using nat_pow_def[of Z\<^sub>p "a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a" "2::nat"] 3  Zp.r_one \<open>a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p\<close>
                  numeral_2_eq_2 pow_0 pow_suc by presburger
            thus ?thesis 
              using val_Zp_mult[of "a'\<ominus>\<^bsub>Z\<^sub>p\<^esub>a" "a'\<ominus>\<^bsub>Z\<^sub>p\<^esub>a"] \<open>a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> a \<in> carrier Z\<^sub>p\<close> by presburger
          qed
          thus ?thesis
            using 40 val_Zp_mult[of c "(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat)"] 3 c_def 
            by (metis Zp.nat_pow_closed Zp.nonzero_closed add.left_neutral add_mono_thms_linordered_semiring(3))
        qed
        have 5: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<in> carrier Z\<^sub>p"
          using a'_closed local.a_closed by blast
        have 50 :  "val_Zp ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) = e"
        proof-
          have 51: "val_Zp (a [^]\<^bsub>Z\<^sub>p\<^esub> (k - 1)) = 0"
            using a_val a_closed Zp.Units_pow_closed unit_imp_val_Zp0 val_Zp_0_imp_unit by blast
          have 52: "val_Zp ([k] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = e"
            using val_ord val_of_inc inc_of_nat e_def 
            by (metis DL_2_4_0 Zp_nat_inc_closed e_eq neq0_conv not_numeral_le_zero val_ord_nat_inc)
          show ?thesis  using val_Zp_mult[of "[k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>" "a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)"] a_closed
                  Zp.nat_pow_closed[of a "k-1"] e_def unfolding 51 52 
            by (metis Zp_nat_inc_closed add.right_neutral)
        qed
        have 6: "val_Zp (([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)) = e + val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"
          using val_Zp_mult[of "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1))" "(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"] e_def val_ord unfolding l_def 50 
          using a'_closed local.a_closed by blast
        have 7: "a (e+1) = a' (e+1)"
          using \<eta>_ac[of x] \<eta>_ac[of x'] A \<xi>_1_nonzero unfolding ac_def a_def a'_def by smt
        hence 8: "val_Zp (a'\<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<ge> e+1"
          using a_closed a'_closed by (metis False Zp_residue_eq2)
        hence 9: "val_Zp (([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)) < val_Zp (c \<otimes>\<^bsub>Z\<^sub>p\<^esub>(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)[^]\<^bsub>Z\<^sub>p\<^esub>(2::nat))"
        proof-
          have 90: "val_Zp (a'\<ominus>\<^bsub>Z\<^sub>p\<^esub>a) > e" using 8 
          by (metis eSuc_eint eSuc_mono iless_Suc_eq of_nat_1 of_nat_add)
          hence "val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)+ val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) > val_Zp (([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> a[^]\<^bsub>Z\<^sub>p\<^esub>(k-1)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a))"
          unfolding 6 l_def using eint_add_mono False 
          by (metis "90" add.commute eint.distinct(2) eint_add_left_cancel_less l_def)
          thus ?thesis using 4  
          by (meson less_le_trans)
        qed
        hence 10: "val_Zp (b'\<ominus>\<^bsub>Z\<^sub>p\<^esub>b) = e + val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a)"
          using 6 2 5 Zp.minus_closed Zp.monom_term_car a'_closed add_comm c_def local.a_closed val_Zp_ultrametric_eq by metis 
        have 11: "val_Zp (b'\<ominus>\<^bsub>Z\<^sub>p\<^esub>b) \<ge> eint e + eint \<alpha>"
          using b_b'_cong b'_closed b_closed val_Zp_dist_def val_Zp_dist_res_eq2 
          by (metis of_nat_add plus_eint_simps(1))
        hence 12: "val_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub>a) \<ge> \<alpha>"
          using A  b_b'_cong  10 by (smt add_strict_mono eint_add_left_cancel_le eint_ord_simps(3) iless_Suc_eq not_less)                 
        thus ?thesis 
         by (metis "3" Zp.nonzero_closed a'_closed local.a_closed res_diff_zero_fact(1) zero_below_val_Zp)
       qed
     thus ?thesis unfolding a_def a'_def ac_def 
       using A(1) A(2) Qp.nonzero_memE(2) \<eta>_nonzero by presburger     
   qed
  qed
  obtain F where F_def: "F = (\<lambda> t. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac (e+\<alpha>) (\<xi>_1 x) = t})" 
    by blast 
  have F_semialg: "\<And>t. t \<in> Units (Zp_res_ring (e+\<alpha>)) \<Longrightarrow> is_semialgebraic m (F t)"
  proof- fix t assume A: "t \<in> Units (Zp_res_ring (e+\<alpha>))" show "is_semialgebraic m (F t)"
    unfolding F_def apply(rule ac_cong_set_SA'') using assms(1) apply presburger 
    apply (simp add: DL_2_4_2) using A apply blast using \<xi>_1_closed apply linarith
    using \<xi>_1_nonzero Qp.not_nonzero_memI by blast
  qed
  obtain S where S_def: "S = {s \<in> Units (Zp_res_ring (e+\<alpha>)). (\<exists> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t \<and> ac (e+\<alpha>) (\<xi>_1 x) = s)}"
    by blast 
  have S_finite: "finite S" proof- have "0 < e + \<alpha>" by (simp add: assms(1))
  hence "finite (Units (residue_ring (p ^ (e + \<alpha>))))" using residues.finite_Units[of "p^(e+\<alpha>)"] p_residues[of "e+\<alpha>"] 
    by metis   thus ?thesis    unfolding S_def by (smt finite_subset mem_Collect_eq subsetI)
  qed
  have 3: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t} = (\<Union> s \<in> S. F s)"
  proof 
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t} \<subseteq> \<Union> (F ` S)"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t}"
      then obtain s where s_def: "s = ac (e+\<alpha>) (\<xi>_1 x)"
        by blast 
      have s_closed: "s \<in> Units (Zp_res_ring (e+\<alpha>))"
        unfolding s_def using A 
        by (metis (no_types, lifting) \<xi>_1_nonzero ac_units add_gr_0 assms(1) mem_Collect_eq)
      have 00: "t = ac \<alpha> (\<eta> x)"
        using A by blast 
      have 01: "x \<in> F s" unfolding F_def using 00 A s_def by blast
      have 02: "s \<in> S"
        using s_def s_closed  unfolding S_def 00 
        using A by blast
      thus "x \<in> \<Union> (F ` S)"
        using "01" by blast
    qed
    show "\<Union> (F ` S) \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t}"
    proof fix x assume A: "x \<in> \<Union> (F ` S)"
      then obtain s where s_def: "s \<in> S \<and> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> ac (e+\<alpha>) (\<xi>_1 x) = s"
        unfolding F_def by blast 
      then obtain y where y_def: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> ac \<alpha> (\<eta> y) = t \<and> ac (e+\<alpha>) (\<xi>_1 y) = s"
        unfolding S_def by blast 
      have "ac \<alpha> (\<eta> x) = ac \<alpha> (\<eta> y)" 
        apply(rule 2)
        using A unfolding F_def apply blast 
        using y_def apply blast 
        using y_def s_def by blast 
      thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t}"
        using s_def y_def by blast
    qed
  qed
  show ?thesis unfolding 3  using finite_union_is_semialgebraic[of "F`S" m] S_finite F_semialg 
    unfolding S_def  
    by (metis (no_types, lifting) finite_imageI image_subsetI is_semialgebraicE mem_Collect_eq)
qed

lemma fact_ii':
  assumes "\<alpha> > 0"
  assumes "t \<in> Units (Zp_res_ring \<alpha>)"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac \<alpha> (\<eta> (take m x)) = t}"
proof-
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac \<alpha> (\<eta> (take m x)) = t} = take m  \<inverse>\<^bsub>m+l\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac \<alpha> (\<eta> x) = t}"
    unfolding evimage_def using take_closed[of m "m+l"] 
    by (smt Collect_cong Int_def le_add1 mem_Collect_eq vimage_eq)
  then show ?thesis using assms fact_ii 
    by (metis (mono_tags, lifting) DL_2_4_2 add_gr_0 le_add1 semialg_map_evimage_is_semialg take_is_semialg_map)
qed

subsubsection\<open>Fact iii)\<close>

lemma fact_iii:
  fixes N::nat fixes n::nat 
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> carrier Q\<^sub>p" 
  assumes "val (\<eta> x) \<ge> N + val c"
  shows   "val (\<eta> x \<ominus> c) = val c"
          "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<ominus> c)"
proof-
  have 00:"val (\<eta> x) > val c" proof- have "eint N > 0"
    using assms eint_pow_int_is_pos of_nat_0_less_iff by blast
  thus ?thesis 
    using assms(1) assms(6) 
    by (smt \<eta>_nonzero add.commute add.right_neutral assms(4) eint.distinct(2)
        eint_add_left_cancel_less less_le_trans linorder_not_less order_le_less val_ord)
  qed
  hence "val (\<eta> x \<ominus> c) = val (\<ominus>c)" 
    by (metis \<eta>_closed assms(4) assms(5) val_minus val_ultrametric_noteq')
  thus "val (\<eta> x \<ominus> c) = val c" 
    using assms(5) val_minus by presburger
  have 0: "\<eta> x \<in> carrier Q\<^sub>p"
    using \<eta>_closed assms(4) by blast
  hence 1: "\<eta> x \<in> nonzero Q\<^sub>p"
    using \<eta>_nonzero assms(4) by blast
  have 2: "c \<in> nonzero Q\<^sub>p"
    using 00 assms  val_nonzero by blast
  have 3: "\<eta> x \<ominus> c = (\<ominus>c)\<otimes>(\<one> \<ominus> (\<eta> x \<div> c))"
    by (smt "0" "2" Qp.l_minus Qp.minus_a_inv Qp.minus_closed Qp.one_closed Qp.r_minus_distr 
        Qp.r_one assms(5) fract_closed local.fract_cancel_right)
  hence 4: "(\<eta> x \<ominus> c) \<div> (\<ominus>c) = \<one> \<ominus> (\<eta> x \<div> c)"
    by (metis "0" "00" Q\<^sub>p_def Qp.add.inv_closed Qp.inv_cancelR(2) Qp.minus_closed Qp.one_closed 
        Zp_def \<open>val (\<eta> x \<ominus> c) = val (\<ominus> c)\<close> \<open>val (\<eta> x \<ominus> c) = val c\<close> assms(5) fract_closed 
        padic_fields.Units_eq_nonzero padic_fields_axioms val_nonzero)
  have 5: "val (\<eta> x \<div> c) \<ge> N"
    using assms  by (smt "0" "00" "2" Groups.add_ac(2) eint_add_left_cancel_less fract_closed 
        linorder_not_less local.fract_cancel_right val_mult)
  hence 6: "val (\<ominus>(\<eta> x \<div> c)) \<ge> N"
    by (metis "0" "2" fract_closed val_minus)
  have 7: "val (\<one> \<ominus> (\<one> \<ominus> (\<eta> x \<div> c))) \<ge> N"
    using 5 2 0 assms fract_closed[of "\<eta> x" c] unfolding a_minus_def  
    by (metis (no_types, lifting) Qp.add.inv_closed Qp.minus_add Qp.minus_minus Qp.one_closed Qp.r_neg1)
  have 8: "val \<one> = val (\<one> \<ominus> (\<eta> x \<div> c))"
    using 7 assms 
    by (metis (no_types, lifting) "0" "00" "4" Q\<^sub>p_def Qp.Units_r_inv Qp.add.inv_closed
        Qp.minus_closed Qp.nonzero_memE(2) Zp_def \<open>val (\<eta> x \<ominus> c) = val (\<ominus> c)\<close> \<open>val (\<eta> x \<ominus> c) = val c\<close> 
        padic_fields.Units_eq_nonzero padic_fields.inv_in_frac(1) padic_fields_axioms val_mult val_nonzero)
  hence 9: "ac N ((\<eta> x \<ominus> c) \<div> (\<ominus>c)) = 1"
    unfolding 4 
    using 7 val_one ac_val[of \<one> "\<one> \<ominus> (\<eta> x) \<otimes>(inv c)" N] 
    by (metis "0" "00" "2" Qp.not_eq_diff_nonzero Qp.one_closed Qp.one_nonzero Qp.r_one
        ac_one add.left_neutral assms(1) assms(5) fract_closed less_one linorder_not_less 
        local.fract_cancel_right neq_iff)
  hence 10: "((\<eta> x \<ominus> c) \<div> (\<ominus>c)) \<in> P_set n"
    using assms by (metis "0" "2" "4" "8" Qp.minus_closed Qp.one_closed fract_closed val_one)
  thus 11: "  pow_res n (\<eta> x \<ominus> c) = pow_res n (\<ominus> c) "
    by (metis "0" "3" "4" Qp.add.inv_closed Qp.minus_closed assms(2) assms(5) equal_pow_resI')
qed

lemma (in padic_fields) nat_inc_nonzero:
  assumes "(k::nat) \<noteq> 0"
  shows "[k]\<cdot>\<one> \<in> nonzero Q\<^sub>p"
  using assms by (simp add: Qp.nonzero_memI Qp_char_0)

lemma fact_iii':
  fixes N::nat fixes n::nat 
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> carrier Q\<^sub>p" 
  assumes "val (\<eta> x) \<le> - N + val c"
  shows   "val (\<eta> x \<ominus> c) = val (\<eta> x)"
          "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x)"
proof-
  have 000: "val (\<eta> x) + N \<le>  val c"
  proof- have  "val (\<eta> x) + N \<le> - N + val c + N"
      using assms add_mono_thms_linordered_semiring(3) by blast
    thus ?thesis 
      by (metis ab_semigroup_add_class.add_ac(1) add.commute add.left_neutral eint.simps(3) eint_add_cancel_fact idiff_0)
  qed
  have 00:"val (\<eta> x) < val c" 
  proof- have "eint N > 0"
    using assms eint_pow_int_is_pos of_nat_0_less_iff by blast
    thus ?thesis 
    using assms(1) assms(6) 000  by (smt \<eta>_nonzero add.commute add.right_neutral assms(4) eint.distinct(2)
        eint_add_left_cancel_less less_le_trans linorder_not_less order_le_less val_ord)
  qed
  hence "val (\<eta> x \<ominus> c) = val (\<eta> x)" 
    using \<eta>_closed assms(4) assms(5) val_ultrametric_noteq'' by blast    
  thus "val (\<eta> x \<ominus> c) = val (\<eta> x)"
    using assms(5) val_minus by presburger
  have 0: "\<eta> x \<in> carrier Q\<^sub>p"
    using \<eta>_closed assms(4) by blast
  hence 1: "\<eta> x \<in> nonzero Q\<^sub>p"
    using \<eta>_nonzero assms(4) by blast
  have 3: "\<eta> x \<ominus> c = (\<eta> x)\<otimes>(\<one> \<ominus> (c \<div> \<eta> x))"
    by (metis "0" "1" Qp.one_closed Qp.r_minus_distr Qp.r_one assms(5) fract_closed local.fract_cancel_right)    
  hence 4: "(\<eta> x \<ominus> c) \<div> (\<eta> x) = \<one> \<ominus> (c \<div> \<eta> x)"
    by (metis "0" "1" Q\<^sub>p_def Qp.inv_cancelR(2) Qp.minus_closed Qp.one_closed Zp_def assms(5) fract_closed padic_fields.Units_eq_nonzero padic_fields_axioms)    
  have 5: "val (c \<div> \<eta> x) \<ge> N"
    using 1 assms 000 val_fract[of c "\<eta> x"] 
    by (metis eint.simps(3) eint_add_cancel_fact eint_add_left_cancel_less linorder_not_less val_ord)    
  have 6: "val (\<one> \<ominus> (\<one> \<ominus> (c \<div> \<eta> x))) \<ge> N"
  proof- have 60: "\<one> \<ominus> (\<one> \<ominus> (c \<div> \<eta> x)) = (c \<div> \<eta> x)"
      using 1 assms fract_closed[of c "\<eta> x"] unfolding a_minus_def  
      by (metis Qp.add.inv_closed Qp.minus_add Qp.minus_minus Qp.one_closed Qp.r_neg1)
    show ?thesis unfolding 60 
    using 5 by blast 
  qed
  have 7: "val \<one> = val (\<one> \<ominus> (c \<div> \<eta> x))"
    using 6 assms 
    by (metis "0" "1" "4" Q\<^sub>p_def Qp.Units_r_inv Qp.minus_closed Qp.not_nonzero_memI Zp_def \<open>val (\<eta> x \<ominus> c) = val (\<eta> x)\<close> padic_fields.Units_eq_nonzero padic_fields.inv_in_frac(1) padic_fields_axioms val_mult)    
  hence 8: "ac N ((\<eta> x \<ominus> c) \<div> (\<eta> x)) = 1"
    unfolding 4 using 7 val_one ac_val[of \<one> "\<one> \<ominus> (c \<div> \<eta> x)" N] 
    by (metis "0" "00" "1" "6" Qp.not_eq_diff_nonzero Qp.one_closed Qp.one_nonzero Qp.r_one ac_one 
        add.left_neutral assms(1) assms(5) fract_closed less_one linorder_not_less local.fract_cancel_right neq_iff)
  hence 9: "((\<eta> x \<ominus> c) \<div> (\<eta> x)) \<in> P_set n"
    using assms by (metis "0" "1" "4" "7" Qp.minus_closed fract_closed val_one)    
  thus "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x)"
    by (metis "0" "3" "4" Qp.minus_closed assms(2) assms(5) equal_pow_resI')
qed


lemma fact_iii'':
  fixes N::nat fixes n::nat 
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "ord (\<eta> x) mod n = ord (\<eta> x') mod n"
  assumes "ac N (\<eta> x) = ac N (\<eta> x')"
  shows "pow_res n (\<eta> x) = pow_res n (\<eta> x')"
proof-
  obtain l where l_def: "ord (\<eta> x) = ord (\<eta> x') + l*int n" using assms(6)
    by (metis mod_eqE mult_of_nat_commute)
  have 0: "ord (\<pp> [^] (l * int n)) = l*int n"
    using ord_p_pow_int by blast
  hence 1: "ord(\<eta> x) = ord ((\<pp>[^](l*n)) \<otimes> \<eta> x')"
    using assms \<eta>_nonzero ord_mult[of "\<pp>[^](l*n)" "\<eta> x'"]  
    by (metis add.commute l_def p_intpow_closed(2))
  have 2: "ac N (\<eta> x) = ac N ((\<pp>[^](l*n)) \<otimes> \<eta> x')"
    using assms \<eta>_nonzero ac_p_int_pow_factor by presburger
  have 3: "val (((\<pp>[^](l*n)) \<otimes> \<eta> x')\<div> (\<eta> x)) = 0"
    using 1 \<eta>_nonzero by (smt Qp.nonzero_mult_closed Qp.one_closed Qp.r_one Qp_int_pow_nonzero 
        \<eta>_closed assms(4) assms(5) fract_closed local.fract_cancel_right p_nonzero 
        plus_eint_simps(1) prod_equal_val_imp_equal_val val_mult0 val_nonzero' val_one val_ord)
  have 4: "ac N (((\<pp>[^](l*n)) \<otimes> \<eta> x')\<div> (\<eta> x)) = 1"
    using 2 ac_mult ac_inv by (metis Q\<^sub>p_def Qp.nonzero_mult_closed Qp.not_nonzero_memI 
        Qp_int_pow_nonzero Z\<^sub>p_def \<eta>_closed \<eta>_nonzero ac_inv'''(1) assms(1) assms(4) assms(5) 
        p_nonzero padic_fields.inv_in_frac(1) padic_fields_axioms)
  hence 5: "pow_res n (\<eta> x) = pow_res n ((\<pp>[^](l*n)) \<otimes> \<eta> x')"
    using assms 
    by (metis "3" Qp.nonzero_mult_closed Qp_int_pow_nonzero \<eta>_closed \<eta>_nonzero equal_pow_resI' fract_closed local.fract_cancel_right p_nonzero)
  thus ?thesis using  pow_res_p_pow_factor \<eta>_closed assms(2) assms(5) by blast
qed


subsubsection\<open>Fact iv)\<close>

lemma fact_iv: 
  fixes N::nat fixes n::nat fixes j::int
  assumes "N > 0"
  assumes "n > 0"
  assumes "j \<in> {1..int N-1}"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> nonzero Q\<^sub>p" 
  assumes "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c' \<in> nonzero Q\<^sub>p"
  assumes "ord c mod n = ord c' mod n"
  assumes "ac N (\<eta> x) = ac N (\<eta> x')"
  assumes "ac N c = ac N c'"
  assumes "ord (\<eta> x) = j + ord c"
  assumes "ord (\<eta> x') = j + ord c'"
  shows "val (\<eta> x \<ominus> c) = val c"
        "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x' \<ominus> c')"
proof-
  obtain a where a_def: "a = angular_component (\<eta> x)"
    by blast 
  obtain b where b_def: "b = angular_component c"
    by blast 
  have ac_eta: "ac N (\<eta> x) = a N"
    unfolding a_def ac_def using assms \<eta>_nonzero by (metis Qp.not_nonzero_memI)
  have c_nonzero: "c \<in> nonzero Q\<^sub>p"
    using assms \<eta>_nonzero by blast
  hence ac_c: "ac N c = b N"
    unfolding b_def ac_def using assms \<eta>_nonzero 
    using Qp.not_nonzero_memI by presburger
  obtain a' where a'_def: "a' = angular_component (\<eta> x')"
    by blast 
  obtain b' where b'_def: "b' = angular_component c'"
    by blast 
  have ac_eta': "ac N (\<eta> x') = a' N"
    unfolding a'_def ac_def using assms \<eta>_nonzero by (metis Qp.not_nonzero_memI)
  have c_nonzero: "c' \<in> nonzero Q\<^sub>p"
    using assms \<eta>_nonzero by blast
  hence ac_c': "ac N c' = b' N"
    unfolding b'_def ac_def using assms \<eta>_nonzero 
    using Qp.not_nonzero_memI by presburger
  have 0: "\<eta> x = \<pp>[^](ord c + j) \<otimes> \<iota> a"
    unfolding a_def using assms by (smt \<eta>_nonzero angular_component_factors_x)
  have 1: "\<eta> x' = \<pp>[^](ord c' + j) \<otimes> \<iota> a'"
    unfolding a'_def using assms by (smt \<eta>_nonzero angular_component_factors_x)
  have 2: "c = \<pp>[^](ord c)\<otimes> \<iota> b"
    unfolding b_def using angular_component_factors_x assms(6) by blast
  have 3: "c' = \<pp>[^](ord c')\<otimes>\<iota> b'"
    unfolding b'_def using angular_component_factors_x assms by blast
  have a_closed: "\<iota> a \<in> carrier Q\<^sub>p" unfolding a_def 
    using Q\<^sub>p_def Zp_def \<eta>_nonzero assms(5) inc_closed padic_fields.angular_component_closed padic_fields_axioms by blast
  have a'_closed: "\<iota> a' \<in> carrier Q\<^sub>p" unfolding a'_def 
    using \<eta>_nonzero angular_component_closed assms(7) inc_closed by blast
  have b_closed: "\<iota> b \<in> carrier Q\<^sub>p" unfolding b_def 
    using angular_component_closed assms(6) inc_closed by blast
  have b'_closed: "\<iota> b' \<in> carrier Q\<^sub>p" unfolding b'_def 
    using angular_component_closed c_nonzero inc_closed by blast
  have 4: "\<eta> x \<ominus> c = \<pp>[^](ord c) \<otimes> (\<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b))"
  proof-
    have 40: "\<eta> x \<ominus> c = (\<pp>[^](ord c) \<otimes> \<pp>[^]j \<otimes> (\<iota> a)) \<ominus> \<pp>[^](ord c)\<otimes> (\<iota> b)"
      unfolding 0 using 2 p_intpow_add by presburger
    hence 41: "\<eta> x \<ominus> c = (\<pp>[^](ord c) \<otimes> \<pp>[^]j \<otimes> (\<iota> a)) \<oplus> \<pp>[^](ord c)\<otimes> (\<ominus> (\<iota> b))"
      unfolding a_minus_def using  Qp.cring_simprules(29)[of "\<pp> [^] ord c" "\<iota> b"] 
      using b_closed p_intpow_closed(1) by presburger
    show ?thesis unfolding 41 unfolding a_minus_def  using Qp.r_distr[of "\<pp> [^] j \<otimes> \<iota> a" "\<ominus> \<iota> b" "\<pp> [^] ord c"]
              Qp.m_assoc[of "\<pp> [^] ord c" "\<pp> [^] j" "\<iota> a"] Qp.add.inv_closed Qp.m_closed b_closed 
              local.a_closed p_intpow_closed(1) by presburger
  qed
  have 5: "\<eta> x' \<ominus> c' = \<pp>[^](ord c') \<otimes> (\<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b'))"
  proof-
    have 50: "\<eta> x' \<ominus> c' = (\<pp>[^](ord c') \<otimes> \<pp>[^]j \<otimes> (\<iota> a')) \<ominus> \<pp>[^](ord c')\<otimes> (\<iota> b')"
      unfolding 1 using 3 p_intpow_add by presburger
    show ?thesis unfolding 50 unfolding a_minus_def  
      using Qp.add.inv_closed Qp.m_assoc Qp.m_closed Qp.r_distr Qp.r_minus a'_closed b'_closed p_intpow_closed(1) by presburger
  qed
  have 6: "ac N (\<eta> x \<ominus> c) = ac N (\<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b))"
    using 4  by (metis Qp.m_closed Qp.m_comm Qp.minus_closed ac_p_int_pow_factor_right b_closed local.a_closed p_intpow_closed(1))
  have 7: "ac N (\<eta> x' \<ominus> c') = ac N (\<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b'))"
    using 5 by (metis Qp.m_closed Qp.m_comm Qp.minus_closed a'_closed ac_p_int_pow_factor_right b'_closed p_intpow_closed(1))
  have 8: "ac N (\<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b)) = ac N (\<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b'))"
  proof-
    have 80: "val (\<iota> b) = 0"
      unfolding b_def using assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 81: "val (\<iota> a) = 0"
      unfolding a_def using \<eta>_nonzero assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 82: "val (\<iota> b') = 0"
      unfolding b'_def using assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 83: "val (\<iota> a') = 0"
      unfolding a'_def using \<eta>_nonzero assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have j_gt: "j > 0"
      using assms(3) by (meson atLeastAtMost_iff int_one_le_iff_zero_less)
    have 84: "val (\<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b)) = 0"
      using 82 83 j_gt by (metis "80" "81" Qp.m_closed add.left_neutral b_closed 
          eint_pow_int_is_pos local.a_closed p_intpow_closed(1) times_p_pow_val val_ultrametric_noteq')
    have 85: "val (\<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b')) = 0"
      using 82 83 j_gt  
      by (metis Qp.m_closed a'_closed add.left_neutral b'_closed eint_pow_int_is_pos
          p_intpow_closed(1) times_p_pow_val val_ultrametric_noteq')
    have 86: "\<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') = \<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b')"
      unfolding a'_def b'_def  using j_gt inc_of_prod inc_of_diff angular_component_closed 
      by (smt Zp.m_closed \<eta>_nonzero assms(7) c_nonzero p_intpow_inc p_pow_car)
    have 87: "\<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) = \<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b)"
      unfolding a_def b_def  using j_gt inc_of_prod inc_of_diff angular_component_closed 
      by (smt (verit, ccfv_threshold) "0" "81" Qp.m_closed Qp_int_pow_nonzero Zp.m_closed add.right_neutral assms(6) equal_val_imp_equal_ord(2) local.a_closed p_intpow_closed(1) p_intpow_inc p_nonzero p_pow_car val_mult)
    have a_closed': "a \<in> carrier Z\<^sub>p"
      unfolding a_def using angular_component_closed \<eta>_nonzero assms(5) by blast
    have b_closed': "b \<in> carrier Z\<^sub>p"
      unfolding b_def using angular_component_closed assms(6) by blast
    have a'_closed': "a' \<in> carrier Z\<^sub>p"
      unfolding a'_def using angular_component_closed \<eta>_nonzero assms by blast
    have b'_closed': "b' \<in> carrier Z\<^sub>p"
      unfolding b'_def using angular_component_closed assms by blast
    have 88: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') N = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) N"
    proof-
      have 880: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') N = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j) N \<otimes>\<^bsub>Zp_res_ring N\<^esub> a' N \<ominus>\<^bsub>Zp_res_ring N\<^esub> b' N"
        using b'_closed' residue_of_diff residue_of_prod by presburger
      have 881: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) N = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j) N \<otimes>\<^bsub>Zp_res_ring N\<^esub> a N \<ominus>\<^bsub>Zp_res_ring N\<^esub> b N"
        using b_closed' residue_of_diff residue_of_prod by presburger
      have 882: "a' N = a N"
        unfolding a'_def a_def using assms a'_def a_def ac_eta ac_eta' by presburger
      have 883: "b' N = b N"
        unfolding b'_def b_def using assms by (metis ac_c ac_c' b'_def b_def)
      show ?thesis using 881 880 unfolding  882 883 by linarith
    qed
    have 89: "\<And>x y. x \<in> carrier Z\<^sub>p \<Longrightarrow> y \<in> carrier Z\<^sub>p \<Longrightarrow> x N = y N \<Longrightarrow> (x \<ominus>\<^bsub>Z\<^sub>p\<^esub>y) N = 0"
    proof- fix x y assume A: "x \<in> carrier Z\<^sub>p"  " y \<in> carrier Z\<^sub>p" " x N = y N"
      have 00: "(x \<ominus>\<^bsub>Z\<^sub>p\<^esub> y) N = (x N - y N) mod p ^ N" using residue_of_diff'[of y x N] A by blast 
      show "(x \<ominus>\<^bsub>Z\<^sub>p\<^esub>y) N = 0" unfolding 00 using A(3) 
        by (metis eq_iff_diff_eq_0 mod_0)
    qed
    have "((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')) N = 0"
    apply(rule 89) using a_closed' b_closed'  apply (smt Zp.m_closed Zp.minus_closed j_gt p_pow_car)
      using a'_closed' b'_closed' apply (smt Zp.m_closed Zp.minus_closed j_gt p_pow_car)
      using 88 by metis 
    hence 90: "val_Zp ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')) \<ge> N"
    proof(cases "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')")
      case True
      then have T0: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>j \<otimes>\<^bsub>Z\<^sub>p\<^esub> a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
        using a'_closed' b'_closed' a_closed' b_closed' 
        by (smt Zp.m_closed Zp.minus_closed Zp.r_right_minus_eq j_gt p_pow_car)
      show ?thesis unfolding T0 val_Zp_def 
        using eint_ord_code(3) by presburger
    next
      case False
      then show ?thesis using Zp_residue_eq2 a'_closed' b'_closed' a_closed' b_closed' 
        by (smt "88" Zp.m_closed Zp.minus_closed j_gt p_pow_car)
    qed
    hence 91: "val ((\<pp>[^]j \<otimes> (\<iota> a) \<ominus> (\<iota> b)) \<ominus> (\<pp>[^]j \<otimes> (\<iota> a') \<ominus> (\<iota> b'))) \<ge> N"
      using 86 87 
      by (smt Zp.m_closed Zp.minus_closed a'_closed' a_closed' b'_closed' b_closed' inc_of_diff j_gt p_pow_car val_of_inc)
    thus "ac N (\<pp> [^] j \<otimes> \<iota> a \<ominus> \<iota> b) = ac N (\<pp> [^] j \<otimes> \<iota> a' \<ominus> \<iota> b')"
      using 84 85 ac_val  
      by (metis Qp.m_closed Qp.minus_closed a'_closed add.commute add.right_neutral b'_closed b_closed local.a_closed p_intpow_closed(1) val_nonzero' zero_eint_def)
  qed
  hence 10: "ac N (\<eta> x \<ominus> c) = ac N (\<eta> x' \<ominus> c')"
    unfolding 6 7 by blast 
  obtain l where l_def: "ord c = ord c' + l*int n" using assms
    by (metis mod_eqE mult_of_nat_commute)
  have 11: "ord (\<pp> [^] (l * int n)) = l*int n"
    using ord_p_pow_int by blast
  hence 12: "ord c = ord ((\<pp>[^](l*n)) \<otimes> c')"
    using assms \<eta>_nonzero ord_mult[of "\<pp>[^](l*n)" "c'"]  
    by (metis add.commute l_def p_intpow_closed(2))
  have j_gt: "j > 0"
    by (meson assms(3) atLeastAtMost_iff less_le_trans zero_less_one)
  show 13: "val (\<eta> x \<ominus> c) = val c"
  proof-
    have "ord (\<eta> x) > ord c"
      using assms j_gt \<eta>_nonzero by linarith
    hence "val (\<eta> x) > val c"
      using assms  \<eta>_nonzero val_ord 
      by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero eint.inject neq_iff ord_ultrametric_noteq' ultrametric_equal_eq')
    thus ?thesis using assms 
      by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_nonzero j_gt ord_ultrametric_noteq' val_ord)
  qed
  have 14: "val (\<eta> x' \<ominus> c') = val c'"
  proof-
    have "ord (\<eta> x') > ord c'"
      using assms j_gt \<eta>_nonzero by linarith
    hence "val (\<eta> x') > val c'"
      using assms  \<eta>_nonzero val_ord 
      by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero eint.inject neq_iff ord_ultrametric_noteq' ultrametric_equal_eq')
    thus ?thesis using assms 
      by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_nonzero j_gt ord_ultrametric_noteq' val_ord)
  qed
  have 15: "(\<eta> x' \<ominus> c') \<in> nonzero Q\<^sub>p"
    using 14 assms by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed j_gt)
  have 16: "(\<eta> x \<ominus> c) \<in> nonzero Q\<^sub>p"
    using 13 assms by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed j_gt)
  have 17: "ac N (\<eta> x \<ominus> c) = ac N (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    unfolding 10 using "15" ac_p_int_pow_factor by presburger
  have 170 : "val ((\<eta> x \<ominus> c)) = val (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))" using 13 14 12  assms
    by (smt "5" Qp.m_closed Qp.minus_closed Qp.nonzero_mult_closed a'_closed b'_closed p_intpow_closed(1) plus_eint_simps(1) val_mult0 val_nonzero' val_ord val_p_int_pow) 
  have 18: "(\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c')) \<in> nonzero Q\<^sub>p"
    using 15 170 
    by (metis "13" Qp.nonzero_mult_closed Qp_int_pow_nonzero assms(6) p_nonzero val_nonzero' val_ord)
  hence 19: "ac N ((\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))) = 1"
    using 16 18 17 
    by (metis Q\<^sub>p_def Qp.nonzero_closed Qp.nonzero_memE(2) Zp_def ac_inv'''(1) ac_mult assms(1) padic_fields.inv_in_frac(1) padic_fields_axioms)
  have 20: "val ((\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))) = 0"
    using 13 14 12 170 
    by (metis (no_types, lifting) "16" "18" Qp.nonzero_closed Qp.one_closed Qp.r_one fract_closed local.fract_cancel_right prod_equal_val_imp_equal_val val_one)
  have 21: "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    apply(rule equal_pow_resI'[of _ _ "(\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))" ])
    using "16" Qp.nonzero_closed apply blast
    using "18" Qp.nonzero_closed apply blast
    using assms(4) 19 20 16 18 Qp.nonzero_closed fract_closed apply blast
    using "16" "18" Qp.nonzero_closed local.fract_cancel_right apply blast
    by (simp add: assms(2))
  have 22: "pow_res n (\<eta> x' \<ominus> c') = pow_res n (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    using "15" Qp.nonzero_closed assms(2) pow_res_p_pow_factor by blast
  show "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x' \<ominus> c')"
    unfolding 21 22 by blast 
qed

lemma fact_iv': 
  fixes N::nat fixes n::nat fixes j::int
  assumes "N > 0"
  assumes "n > 0"
  assumes "j \<in> {-N+1..-1}"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> nonzero Q\<^sub>p" 
  assumes "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c' \<in> nonzero Q\<^sub>p"
  assumes "ord (\<eta> x) mod n = ord (\<eta> x') mod n"
  assumes "ac N (\<eta> x) = ac N (\<eta> x')"
  assumes "ac N c = ac N c'"
  assumes "ord (\<eta> x) = j + ord c"
  assumes "ord (\<eta> x') = j + ord c'"
  shows "val (\<eta> x \<ominus> c) = val (\<eta> x)"
        "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x' \<ominus> c')"
proof-
  obtain a where a_def: "a = angular_component (\<eta> x)"
    by blast 
  obtain b where b_def: "b = angular_component c"
    by blast 
  have ac_eta: "ac N (\<eta> x) = a N"
    unfolding a_def ac_def using assms \<eta>_nonzero by (metis Qp.not_nonzero_memI)
  have c_nonzero: "c \<in> nonzero Q\<^sub>p"
    using assms \<eta>_nonzero by blast
  hence ac_c: "ac N c = b N"
    unfolding b_def ac_def using assms \<eta>_nonzero 
    using Qp.not_nonzero_memI by presburger
  obtain a' where a'_def: "a' = angular_component (\<eta> x')"
    by blast 
  obtain b' where b'_def: "b' = angular_component c'"
    by blast 
  have ac_eta': "ac N (\<eta> x') = a' N"
    unfolding a'_def ac_def using assms \<eta>_nonzero by (metis Qp.not_nonzero_memI)
  have c_nonzero: "c' \<in> nonzero Q\<^sub>p"
    using assms \<eta>_nonzero by blast
  hence ac_c': "ac N c' = b' N"
    unfolding b'_def ac_def using assms \<eta>_nonzero 
    using Qp.not_nonzero_memI by presburger
  have 0: "\<eta> x = \<pp>[^](ord (\<eta> x)) \<otimes> \<iota> a"
    unfolding a_def using assms by (smt \<eta>_nonzero angular_component_factors_x)
  have 1: "\<eta> x' = \<pp>[^](ord (\<eta> x')) \<otimes> \<iota> a'"
    unfolding a'_def using assms by (smt \<eta>_nonzero angular_component_factors_x)
  have 2: "c = \<pp>[^](ord (\<eta> x) - j)\<otimes> \<iota> b"
    unfolding b_def using angular_component_factors_x[of c] assms 
    by (metis (no_types, opaque_lifting) Groups.add_ac(2) Groups.add_ac(3) add.right_neutral
        add_uminus_conv_diff b_def ord_one ord_p_pow_int p_intpow_add p_intpow_inv)
  have 3: "c' = \<pp>[^](ord (\<eta> x') - j )\<otimes>\<iota> b'"
    unfolding b'_def using angular_component_factors_x[of c'] assms 
    by (metis (no_types, opaque_lifting) Groups.add_ac(2) Groups.add_ac(3) add.right_neutral
        add_uminus_conv_diff ord_one ord_p_pow_int p_intpow_add p_intpow_inv)
  have a_closed: "\<iota> a \<in> carrier Q\<^sub>p" unfolding a_def 
    using Q\<^sub>p_def Zp_def \<eta>_nonzero assms(5) inc_closed padic_fields.angular_component_closed padic_fields_axioms by blast
  have a'_closed: "\<iota> a' \<in> carrier Q\<^sub>p" unfolding a'_def 
    using \<eta>_nonzero angular_component_closed assms(7) inc_closed by blast
  have b_closed: "\<iota> b \<in> carrier Q\<^sub>p" unfolding b_def 
    using angular_component_closed assms(6) inc_closed by blast
  have b'_closed: "\<iota> b' \<in> carrier Q\<^sub>p" unfolding b'_def 
    using angular_component_closed c_nonzero inc_closed by blast
  have 4: "\<eta> x \<ominus> c = \<pp>[^](ord (\<eta> x)) \<otimes> ( (\<iota> a) \<ominus> \<pp>[^]-j \<otimes>(\<iota> b))"
  proof-
    have 40: "\<eta> x \<ominus> c = \<pp>[^](ord (\<eta> x)) \<otimes>  (\<iota> a) \<ominus> \<pp>[^](ord (\<eta> x)) \<otimes> \<pp>[^]-j \<otimes> (\<iota> b)"
      by (metis (no_types, opaque_lifting) "0" "2"  diff_conv_add_uminus p_intpow_add)
    hence 41: "\<eta> x \<ominus> c = \<pp>[^](ord (\<eta> x)) \<otimes>  (\<iota> a) \<oplus> \<pp>[^](ord (\<eta> x))\<otimes> \<pp>[^]-j \<otimes> (\<ominus> (\<iota> b))"
      unfolding a_minus_def using  Qp.cring_simprules(29)[of _  "\<iota> b"]  b_closed p_intpow_closed(1) Qp.m_closed by presburger      
    show ?thesis unfolding 41 unfolding a_minus_def 
      using Qp.add.inv_closed Qp.m_assoc Qp.m_closed Qp.r_distr Qp.r_minus b_closed local.a_closed p_intpow_closed(1) by presburger
  qed
  have 5: "\<eta> x' \<ominus> c' = \<pp>[^](ord (\<eta> x')) \<otimes> ( (\<iota> a') \<ominus> \<pp>[^]-j \<otimes>(\<iota> b'))"
  proof-
    have 40: "\<eta> x' \<ominus> c' = \<pp>[^](ord (\<eta> x')) \<otimes>  (\<iota> a') \<ominus> \<pp>[^](ord (\<eta> x')) \<otimes> \<pp>[^]-j \<otimes> (\<iota> b')"
      by (metis (no_types, opaque_lifting) 1 3  diff_conv_add_uminus p_intpow_add)
    hence 41: "\<eta> x' \<ominus> c' = \<pp>[^](ord (\<eta> x')) \<otimes>  (\<iota> a') \<oplus> \<pp>[^](ord (\<eta> x'))\<otimes> \<pp>[^]-j \<otimes> (\<ominus> (\<iota> b'))"
      unfolding a_minus_def using  Qp.cring_simprules(29)[of _  "\<iota> b"]  b'_closed p_intpow_closed(1) Qp.m_closed 
      Qp.r_minus by presburger            
    show ?thesis unfolding 41 unfolding a_minus_def 
      using Qp.add.inv_closed Qp.m_assoc Qp.m_closed Qp.r_distr Qp.r_minus b'_closed a'_closed p_intpow_closed(1) by presburger
  qed
  have 6: "ac N (\<eta> x \<ominus> c) = ac N (\<iota> a \<ominus> \<pp>[^]-j \<otimes> \<iota> b)"
    using 4  by (metis Qp.m_closed Qp.m_comm Qp.minus_closed ac_p_int_pow_factor_right b_closed local.a_closed p_intpow_closed(1))
  have 7: "ac N (\<eta> x' \<ominus> c') = ac N (\<iota> a' \<ominus> \<pp>[^]-j \<otimes> \<iota> b')"
    using 5 by (metis Qp.m_closed Qp.m_comm Qp.minus_closed a'_closed ac_p_int_pow_factor_right b'_closed p_intpow_closed(1))
  have 8: "ac N (\<iota> a \<ominus> \<pp>[^]-j \<otimes> \<iota> b) = ac N (\<iota> a' \<ominus> \<pp>[^]-j \<otimes> \<iota> b')"
  proof-
    have 80: "val (\<iota> b) = 0"
      unfolding b_def using assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 81: "val (\<iota> a) = 0"
      unfolding a_def using \<eta>_nonzero assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 82: "val (\<iota> b') = 0"
      unfolding b'_def using assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have 83: "val (\<iota> a') = 0"
      unfolding a'_def using \<eta>_nonzero assms angular_component_unit val_of_inc 
      by (metis angular_component_closed unit_imp_val_Zp0)
    have j_le: "j < 0"
      using assms(3) 
      by (metis add.comm_neutral atLeastAtMost_iff uminus_add_conv_diff zle_diff1_eq)     
    have 84: "val (\<iota> a \<ominus> \<pp>[^]-j \<otimes> \<iota> b) = 0"
      using 82 83 j_le by (metis "80" "81" Qp.m_closed add.inverse_inverse b_closed 
          eint_pow_int_is_pos idiff_0 local.a_closed neg_less_0_iff_less p_intpow_closed(1) 
          times_p_pow_neg_val val_ultrametric_noteq'')      
    have 85: "val (\<iota> a' \<ominus> \<pp>[^]-j \<otimes> \<iota> b') = 0"
      using 82 83 j_le by (metis (no_types, opaque_lifting) Qp.m_closed a'_closed add.left_neutral
          add.right_neutral b'_closed eint_pow_int_is_pos less_add_same_cancel2 minus_add_cancel 
          p_intpow_closed(1) times_p_pow_val val_ultrametric_noteq'')      
    have 86: "\<iota> ( a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b') = (\<iota> a' \<ominus> \<pp>[^]-j \<otimes> \<iota> b')"
      unfolding a'_def b'_def  using j_le inc_of_prod inc_of_diff angular_component_closed
    proof -
      have f1: "- j = - 1 * j"
        by presburger
      have "\<not> 0 \<le> j"
        using j_le by linarith
      then have f2: "j \<le> 0"
        by linarith
      have "(0 \<le> - 1 * j) = (j \<le> 0)"
        by linarith
      then show "\<iota> (angular_component (\<eta> x') \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> - j \<otimes>\<^bsub>Z\<^sub>p\<^esub> angular_component c') = \<iota> (angular_component (\<eta> x')) \<ominus> \<pp> [^] - j \<otimes> \<iota> (angular_component c')"
        using f2 f1 Zp.m_closed \<eta>_nonzero angular_component_closed assms(7) c_nonzero inc_of_diff inc_of_prod p_intpow_inc p_pow_car by presburger
    qed 
    have 87: "\<iota> (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) = (\<iota> a \<ominus> \<pp>[^]-j \<otimes> \<iota> b)"
      unfolding a_def b_def  using j_le inc_of_prod inc_of_diff angular_component_closed
    proof -
      have f1: "- j = - 1 * j"
        by linarith
      have "\<not> 0 \<le> j"
        using j_le by linarith
      then have f2: "j \<le> 0"
        by linarith
      have "(0 \<le> - 1 * j) = (j \<le> 0)"
        by linarith
      then show "\<iota> (angular_component (\<eta> x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> - j \<otimes>\<^bsub>Z\<^sub>p\<^esub> angular_component c) = \<iota> (angular_component (\<eta> x)) \<ominus> \<pp> [^] - j \<otimes> \<iota> (angular_component c)"
        using f2 f1 Zp.m_closed \<eta>_nonzero angular_component_closed assms(5) assms(6) inc_of_diff inc_of_prod p_intpow_inc p_pow_car by presburger
    qed
    have a_closed': "a \<in> carrier Z\<^sub>p"
      unfolding a_def using angular_component_closed \<eta>_nonzero assms(5) by blast
    have b_closed': "b \<in> carrier Z\<^sub>p"
      unfolding b_def using angular_component_closed assms(6) by blast
    have a'_closed': "a' \<in> carrier Z\<^sub>p"
      unfolding a'_def using angular_component_closed \<eta>_nonzero assms by blast
    have b'_closed': "b' \<in> carrier Z\<^sub>p"
      unfolding b'_def using angular_component_closed assms by blast
    have 88: "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) N = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b') N"
    proof-
      have 880: "(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b') N = a' N \<ominus>\<^bsub>Zp_res_ring N\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j) N \<otimes>\<^bsub>Zp_res_ring N\<^esub> b' N "
        using a'_closed b'_closed' residue_of_diff residue_of_prod
      proof -
        have f1: "j \<le> 0"
          using j_le by linarith
        have "(0 \<le> - 1 * j) = (j \<le> 0)"
          by presburger
        then have f2: "(a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b') N = a' N \<ominus>\<^bsub>residue_ring (p ^ N)\<^esub> ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j)) N \<otimes>\<^bsub>residue_ring (p ^ N)\<^esub> b' N"
          using f1 by (metis (no_types) Zp.m_closed b'_closed' p_pow_car residue_of_diff residue_of_prod)
        have "- j = - 1 * j"
          by presburger
        then show ?thesis
          using f2 by presburger
      qed        
      have 881: "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) N = a N \<ominus>\<^bsub>Zp_res_ring N\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j) N \<otimes>\<^bsub>Zp_res_ring N\<^esub> b N "
        using b_closed' residue_of_diff residue_of_prod
      proof -
        have f1: "j \<le> 0"
          using j_le by linarith
        have "(0 \<le> - 1 * j) = (j \<le> 0)"
          by linarith
        then have f2: "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) N = a N \<ominus>\<^bsub>residue_ring (p ^ N)\<^esub> ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j)) N \<otimes>\<^bsub>residue_ring (p ^ N)\<^esub> b N"
          using f1 by (metis Zp.m_closed b_closed' p_pow_car residue_of_diff residue_of_prod)
        have "- j = - 1 * j"
          by presburger
        then show ?thesis
          using f2 by presburger
      qed 
      have 882: "a' N = a N"
        unfolding a'_def a_def using assms a'_def a_def ac_eta ac_eta' by presburger
      have 883: "b' N = b N"
        unfolding b'_def b_def using assms by (metis ac_c ac_c' b'_def b_def)
      show ?thesis using 881 880 unfolding  882 883 by linarith
    qed
    have 89: "\<And>x y. x \<in> carrier Z\<^sub>p \<Longrightarrow> y \<in> carrier Z\<^sub>p \<Longrightarrow> x N = y N \<Longrightarrow> (x \<ominus>\<^bsub>Z\<^sub>p\<^esub>y) N = 0"
    proof- fix x y assume A: "x \<in> carrier Z\<^sub>p"  " y \<in> carrier Z\<^sub>p" " x N = y N"
      have 00: "(x \<ominus>\<^bsub>Z\<^sub>p\<^esub> y) N = (x N - y N) mod p ^ N" using residue_of_diff'[of y x N] A by blast 
      show "(x \<ominus>\<^bsub>Z\<^sub>p\<^esub>y) N = 0" unfolding 00 using A(3) 
        by (metis eq_iff_diff_eq_0 mod_0)
    qed
    have "((a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b')) N = 0"
      apply(rule 89) unfolding a_minus_def
        apply(intro Zp.ring_simprules a_closed' b_closed' )
        apply (metis (no_types, opaque_lifting)  add.inverse_inverse add.inverse_neutral int.lless_eq j_le neg_le_iff_le p_pow_car)    
       apply(intro Zp.ring_simprules a'_closed' b'_closed' )
        apply (metis (no_types, opaque_lifting)  add.inverse_inverse add.inverse_neutral int.lless_eq j_le neg_le_iff_le p_pow_car)    
      using 88 unfolding a_minus_def by auto       
    hence 90: "val_Zp ((a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b')) \<ge> N"
    proof(cases "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b')")
      case True
      then have T0: "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<p>[^]\<^bsub>Z\<^sub>p\<^esub>-j \<otimes>\<^bsub>Z\<^sub>p\<^esub> b') = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
        using a'_closed' b'_closed' a_closed' b_closed' 
        by (metis Zp.m_closed Zp.minus_closed Zp.r_right_minus_eq int.lless_eq j_le mult_comm neg_0_le_iff_le p_pow_car)        
      show ?thesis unfolding T0 val_Zp_def 
        using eint_ord_code(3) by presburger
    next
      case False
      then show ?thesis using Zp_residue_eq2 a'_closed' b'_closed' a_closed' b_closed' 
        by (meson "88" Zp.m_closed Zp.minus_closed int.lless_eq j_le neg_0_le_iff_le p_pow_car)        
    qed
    hence 91: "val ((\<iota> a \<ominus> \<pp>[^]-j \<otimes> \<iota> b) \<ominus> (\<iota> a' \<ominus> \<pp>[^]-j \<otimes> \<iota> b')) \<ge> N"
      using 86 87
    proof -
      have f1: "- j = - 1 * j"
        by presburger
      have f2: "\<forall>f fa. (f \<notin> carrier Z\<^sub>p \<or> fa \<notin> carrier Z\<^sub>p) \<or> \<iota> (f \<ominus>\<^bsub>Z\<^sub>p\<^esub> fa) = \<iota> f \<ominus> \<iota> fa"
        by (meson inc_of_diff)
      have f3: "\<forall>f fa. f \<notin> carrier Z\<^sub>p \<or> fa \<notin> carrier Z\<^sub>p \<or> f \<ominus>\<^bsub>Z\<^sub>p\<^esub> fa \<in> carrier Z\<^sub>p"
        by blast
      have f4: "j \<le> 0"
        using j_le by linarith
      have f5: "(0 \<le> - 1 * j) = (j \<le> 0)"
        by presburger
      then have f6: "a \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b \<in> carrier Z\<^sub>p"
        using f4 f3 Zp.m_closed a_closed' b_closed' p_pow_car by presburger
      have f7: "a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (- 1 * j) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b' \<in> carrier Z\<^sub>p"
        using f5 f4 f3 Zp.m_closed a'_closed' b'_closed' p_pow_car by presburger
      have "\<forall>f. f \<notin> carrier Z\<^sub>p \<or> val_Zp f = val (\<iota> f)"
        by (meson val_of_inc)
      then show ?thesis
        using f7 f6 f3 f2 f1 "86" "87" "90" by presburger
    qed      
    thus "ac N (\<iota> a \<ominus> \<pp> [^] - j \<otimes> \<iota> b) = ac N (\<iota> a' \<ominus> \<pp> [^] - j \<otimes> \<iota> b')"
      using 84 85 ac_val  
      by (metis Qp.m_closed Qp.minus_closed a'_closed add.commute add.right_neutral b'_closed b_closed local.a_closed p_intpow_closed(1) val_nonzero' zero_eint_def)
  qed
  hence 10: "ac N (\<eta> x \<ominus> c) = ac N (\<eta> x' \<ominus> c')"
    unfolding 6 7 by blast 
  obtain l where l_def: "ord (\<eta> x) = ord (\<eta> x') + l*int n" using assms
    by (metis mod_eqE mult_of_nat_commute)
  have 11: "ord (\<pp> [^] (l * int n)) = l*int n"
    using ord_p_pow_int by blast
  hence 12: "ord (\<eta> x) = ord ((\<pp>[^](l*n)) \<otimes> (\<eta> x'))"
    using assms \<eta>_nonzero ord_mult[of "\<pp>[^](l*n)" "(\<eta> x')"]  
    by (metis add.commute l_def p_intpow_closed(2))
  have j_le: "j < 0"
    by (metis add.left_neutral add_mono_thms_linordered_semiring(3) assms(3) atLeastAtMost_iff 
        int.lless_eq int_nat_eq le_0_eq less_linear nat_int nat_mono nat_zero_as_int 
        nonneg_int_cases of_nat_0 pos_int_cases uminus_add_conv_diff zle_diff1_eq)   
  show 13: "val (\<eta> x \<ominus> c) = val (\<eta> x)"
  proof-
    have "ord (\<eta> x) < ord c"
      using assms j_le \<eta>_nonzero by linarith
    hence "val (\<eta> x) < val c"
      using assms  \<eta>_nonzero val_ord 
      by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero eint.inject neq_iff ord_ultrametric_noteq' ultrametric_equal_eq')
    hence "val (\<eta> x) < val (\<ominus>c)"
      by (metis Qp.nonzero_closed assms(6) val_minus)
    thus ?thesis using assms unfolding a_minus_def  
      using Qp.minus_eq Qp.nonzero_closed \<eta>_closed \<open>val (\<eta> x) < val c\<close> val_ultrametric_noteq'' by presburger    
  qed
  have 14: "val (\<eta> x' \<ominus> c') = val (\<eta> x') "
  proof-
    have "ord (\<eta> x') < ord c'"
      using assms j_le \<eta>_nonzero by linarith
    hence "val (\<eta> x') < val c'"
      using assms  \<eta>_nonzero val_ord 
      by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero eint.inject neq_iff ord_ultrametric_noteq' ultrametric_equal_eq')
    thus ?thesis using assms 
            using Qp.minus_eq Qp.nonzero_closed \<eta>_closed \<open>val (\<eta> x') < val c'\<close> val_ultrametric_noteq'' by presburger    
  qed
  have 15: "(\<eta> x' \<ominus> c') \<in> nonzero Q\<^sub>p"
    using 14 assms by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed j_le)
  have 16: "(\<eta> x \<ominus> c) \<in> nonzero Q\<^sub>p"
    using 13 assms by (smt Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed j_le)
  have 17: "ac N (\<eta> x \<ominus> c) = ac N (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    unfolding 10 using "15" ac_p_int_pow_factor by presburger
  have 170 : "val ((\<eta> x \<ominus> c)) = val (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))" unfolding 13 using 14 15 16 12 val_ord
    by (smt Qp.nonzero_mult_closed Qp_int_pow_nonzero \<eta>_nonzero assms(5) assms(7) p_nonzero plus_eint_simps(1) val_mult0 val_nonzero')
  have 18: "(\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c')) \<in> nonzero Q\<^sub>p"
    using 15 170 by (metis "13" Qp.nonzero_mult_closed Qp_int_pow_nonzero \<eta>_nonzero assms(5) p_nonzero val_nonzero' val_ord)    
  hence 19: "ac N ((\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))) = 1"
    using 16 18 17 
    by (metis Q\<^sub>p_def Qp.nonzero_closed Qp.nonzero_memE(2) Zp_def ac_inv'''(1) ac_mult assms(1) padic_fields.inv_in_frac(1) padic_fields_axioms)
  have 20: "val ((\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))) = 0"
    using 13 14 12 170 
    by (metis (no_types, lifting) "16" "18" Qp.nonzero_closed Qp.one_closed Qp.r_one fract_closed local.fract_cancel_right prod_equal_val_imp_equal_val val_one)
  have 21: "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    apply(rule equal_pow_resI'[of _ _ "(\<eta> x \<ominus> c) \<div> (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))" ])
    using "16" Qp.nonzero_closed apply blast
    using "18" Qp.nonzero_closed apply blast
    using assms(4) 19 20 16 18 Qp.nonzero_closed fract_closed apply blast
    using "16" "18" Qp.nonzero_closed local.fract_cancel_right apply blast
    by (simp add: assms(2))
  have 22: "pow_res n (\<eta> x' \<ominus> c') = pow_res n (\<pp>[^](l*n)\<otimes> (\<eta> x' \<ominus> c'))"
    using "15" Qp.nonzero_closed assms(2) pow_res_p_pow_factor by blast
  show "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x' \<ominus> c')"
    unfolding 21 22 by blast 
qed

subsubsection\<open>Fact v)\<close>

lemma fact_v: 
  fixes N::nat fixes n::nat 
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> nonzero Q\<^sub>p" 
  assumes "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c' \<in> nonzero Q\<^sub>p"
  assumes "ord (\<eta> x) =  ord c"
  assumes "ord (\<eta> x') =  ord c'"
  assumes "ac (e + N) (\<eta> x) \<noteq> ac (e + N) c"
  assumes "ac (e + N) (\<eta> x') \<noteq> ac (e + N) c'"
  assumes "ac (e + N) (\<eta> x) = ac (e + N) (\<eta> x')"
  assumes "ac (e + N) c = ac (e + N) c'"
  shows "val (\<eta> x \<ominus> c) - val c = val (\<eta> x' \<ominus> c') - val c'"
proof-
  obtain a where a_def: "a = angular_component (\<eta> x)"
    by blast 
  obtain a' where a'_def: "a' = angular_component (\<eta> x')"
    by blast 
  obtain b where b_def: "b = angular_component c"
    by blast 
  obtain b' where b'_def: "b' = angular_component c'"
    by blast 
  have val_a: "val (\<iota> a) = 0"
    unfolding a_def using assms 
    by (smt Qp.one_closed Qp.r_one \<eta>_closed \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_intpow_closed(1) prod_equal_val_imp_equal_val val_mult val_one val_ord val_p_int_pow)
  have val_a': "val (\<iota> a') = 0"
    unfolding a'_def using assms 
    by (smt Qp.one_closed Qp.r_one \<eta>_closed \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_intpow_closed(1) prod_equal_val_imp_equal_val val_mult val_one val_ord val_p_int_pow)
  have val_b: "val (\<iota> b) = 0"
    unfolding b_def using assms 
    by (metis angular_component_closed angular_component_unit unit_imp_val_Zp0 val_of_inc)
  have val_b': "val (\<iota> b') = 0"
    unfolding b'_def using assms a'_def val_a' 
    by (metis Qp_int_pow_nonzero \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_nonzero prod_equal_val_imp_equal_val val_ord)    
  have a_id: "\<eta> x = \<pp>[^](ord (\<eta> x))\<otimes>(\<iota> a)"
    using \<eta>_nonzero a_def angular_component_factors_x assms(4) by blast
  have a'_id: "\<eta> x' = \<pp>[^](ord (\<eta> x'))\<otimes>(\<iota> a')"
    using \<eta>_nonzero a'_def angular_component_factors_x assms(6) by blast
  have b_id: "c = \<pp>[^](ord c)\<otimes>(\<iota> b)"
    using angular_component_factors_x assms(5) b_def by blast
  have b'_id: "c' = \<pp>[^](ord c')\<otimes>(\<iota> b')"
    using angular_component_factors_x assms(7) b'_def by blast
  have a_closed: "a \<in> carrier Z\<^sub>p"
    unfolding a_def using \<eta>_nonzero angular_component_closed assms(4) by blast
  have a'_closed: "a' \<in> carrier Z\<^sub>p"
    unfolding a'_def  using \<eta>_nonzero angular_component_closed assms(6) by blast
  have b_closed: "b \<in> carrier Z\<^sub>p"
    unfolding b_def using angular_component_closed assms(5) by blast
  have b'_closed: "b' \<in> carrier Z\<^sub>p"
    unfolding b'_def using angular_component_closed assms(7) by blast
  have 0: "(\<eta> x \<ominus> c) = \<pp>[^]ord c \<otimes> (\<iota> a \<ominus> \<iota> b)"
    using assms a_id b_id by (metis Qp.r_minus_distr \<eta>_nonzero a_def angular_component_closed b_def inc_closed p_intpow_closed(1))
  have 1: "(\<eta> x' \<ominus> c') = \<pp>[^]ord c' \<otimes> (\<iota> a' \<ominus> \<iota> b')"
    using assms a'_id b'_id by (metis Qp.r_minus_distr \<eta>_nonzero a'_def angular_component_closed b'_def inc_closed p_intpow_closed(1))
  have 2: "ord (\<eta> x \<ominus> c) = ord c + ord (\<iota> a \<ominus> \<iota> b)"
    using 0  by (metis Qp.not_eq_diff_nonzero Qp_int_pow_nonzero \<eta>_nonzero a_def a_id angular_component_closed assms(10) assms(4) assms(5) assms(8) b_def b_id inc_closed ord_mult ord_p_pow_int p_nonzero)
  have 3: "ord (\<eta> x' \<ominus> c') = ord c' + ord (\<iota> a' \<ominus> \<iota> b')"
    using 1 by (metis Qp.not_eq_diff_nonzero Qp_int_pow_nonzero \<eta>_nonzero a'_def a'_id angular_component_closed assms(10) assms(12) assms(13) assms(6) assms(7) assms(9) b'_def b'_id inc_closed ord_mult ord_p_pow_int p_nonzero)
  have 4: "ord (\<iota> a \<ominus> \<iota> b) = ord (\<iota> a' \<ominus> \<iota> b')"
  proof-
    have "ord_Zp (a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) = ord_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')"
    proof(rule equal_res_imp_equal_ord_Zp[of "e+N"])
      show "0 < e+N"
        using assms(1) by blast
      show "a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b \<in> carrier Z\<^sub>p"
        using b_closed local.a_closed by blast
      show "a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b' \<in> carrier Z\<^sub>p"
        using a'_closed b'_closed by blast
      have 40: "a (e+N) = a' (e+N)"
        unfolding a_def a'_def using assms \<eta>_nonzero unfolding ac_def by (metis Qp.not_nonzero_memI)
      have 41: "b (e+N) = b' (e+N)"
        unfolding b_def b'_def using assms unfolding ac_def by (metis Qp.not_nonzero_memI) 
      show "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) (e+N) = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') (e+N)"
        using residue_of_diff[of a b "e+N"] residue_of_diff[of a' b' "e+N"] a_closed a'_closed 
        unfolding 40 41 using "40" "41" b'_closed b_closed residue_of_diff by presburger
      show "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) (e + N) \<noteq> 0"
        using assms by (metis Q\<^sub>p_def Qp.nonzero_memE(2) Zp_def \<eta>_nonzero a_def b_closed b_def local.a_closed padic_fields.ac_def padic_fields_axioms res_diff_zero_fact(1))
    qed
    thus ?thesis 
      by (metis Zp.not_eq_diff_nonzero a'_closed a'_id a_id assms(10) assms(12) assms(13) assms(8) assms(9) b'_closed b'_id b_closed b_id inc_of_diff local.a_closed ord_of_inc)
  qed
  have 5: "ord (\<eta> x \<ominus> c) - ord c = ord (\<eta> x' \<ominus> c') - ord c'"
    unfolding 2 3 4 by linarith 
  have 6: "(\<eta> x \<ominus> c) \<in> nonzero Q\<^sub>p"
    by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(10) assms(4) assms(5))
  have 7: "(\<eta> x' \<ominus> c') \<in> nonzero Q\<^sub>p"
    by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(11) assms(6) assms(7))
  show ?thesis using assms val_ord 5 6 7 
    by (smt "0" "1" "4" Q\<^sub>p_def Qp.nonzero_closed Qp.not_eq_diff_nonzero Qp_int_pow_nonzero Z\<^sub>p_def \<eta>_nonzero a'_def a'_id a_def a_id angular_component_closed b'_def b'_id b_def b_id eint.simps(3) eint_add_cancel_fact fract_closed inc_closed p_intpow_closed(1) p_nonzero padic_fields.val_fract padic_fields_axioms prod_equal_val_imp_equal_val val_mult val_p_int_pow)
qed

lemma fact_v': 
  fixes N::nat fixes n::nat 
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> nonzero Q\<^sub>p" 
  assumes "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c' \<in> nonzero Q\<^sub>p"
  assumes "ord (\<eta> x) =  ord c"
  assumes "ord (\<eta> x') =  ord c'"
  assumes "ac (e + N) (\<eta> x) \<noteq> ac (e + N) c"
  assumes "ac (e + N) (\<eta> x') \<noteq> ac (e + N) c'"
  assumes "ord c mod n = ord c' mod n"
  assumes "ac (e + 2*N) (\<eta> x) = ac (e + 2*N) (\<eta> x')"
  assumes "ac (e + 2*N) c = ac (e + 2*N) c'"
  shows "pow_res n (\<eta> x \<ominus> c) = pow_res n (\<eta> x' \<ominus> c') "
proof-
  obtain a where a_def: "a = angular_component (\<eta> x)"
    by blast 
  obtain a' where a'_def: "a' = angular_component (\<eta> x')"
    by blast 
  obtain b where b_def: "b = angular_component c"
    by blast 
  obtain b' where b'_def: "b' = angular_component c'"
    by blast 
  have val_a: "val (\<iota> a) = 0"
    unfolding a_def using assms 
    by (smt Qp.one_closed Qp.r_one \<eta>_closed \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_intpow_closed(1) prod_equal_val_imp_equal_val val_mult val_one val_ord val_p_int_pow)
  have val_a': "val (\<iota> a') = 0"
    unfolding a'_def using assms 
    by (smt Qp.one_closed Qp.r_one \<eta>_closed \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_intpow_closed(1) prod_equal_val_imp_equal_val val_mult val_one val_ord val_p_int_pow)
  have val_b: "val (\<iota> b) = 0"
    unfolding b_def using assms 
    by (metis angular_component_closed angular_component_unit unit_imp_val_Zp0 val_of_inc)
  have val_b': "val (\<iota> b') = 0"
    unfolding b'_def using assms a'_def val_a' 
    by (metis Qp_int_pow_nonzero \<eta>_nonzero angular_component_closed angular_component_factors_x inc_closed p_nonzero prod_equal_val_imp_equal_val val_ord)    
  have a_id: "\<eta> x = \<pp>[^](ord (\<eta> x))\<otimes>(\<iota> a)"
    using \<eta>_nonzero a_def angular_component_factors_x assms(4) by blast
  have a'_id: "\<eta> x' = \<pp>[^](ord (\<eta> x'))\<otimes>(\<iota> a')"
    using \<eta>_nonzero a'_def angular_component_factors_x assms(6) by blast
  have b_id: "c = \<pp>[^](ord c)\<otimes>(\<iota> b)"
    using angular_component_factors_x assms(5) b_def by blast
  have b'_id: "c' = \<pp>[^](ord c')\<otimes>(\<iota> b')"
    using angular_component_factors_x assms(7) b'_def by blast
  have a_closed: "a \<in> carrier Z\<^sub>p"
    unfolding a_def using \<eta>_nonzero angular_component_closed assms(4) by blast
  have a'_closed: "a' \<in> carrier Z\<^sub>p"
    unfolding a'_def  using \<eta>_nonzero angular_component_closed assms(6) by blast
  have b_closed: "b \<in> carrier Z\<^sub>p"
    unfolding b_def using angular_component_closed assms(5) by blast
  have b'_closed: "b' \<in> carrier Z\<^sub>p"
    unfolding b'_def using angular_component_closed assms(7) by blast
  have 0: "(\<eta> x \<ominus> c) = \<pp>[^]ord c \<otimes> (\<iota> a \<ominus> \<iota> b)"
    using assms a_id b_id by (metis Qp.r_minus_distr \<eta>_nonzero a_def angular_component_closed b_def inc_closed p_intpow_closed(1))
  have 1: "(\<eta> x' \<ominus> c') = \<pp>[^]ord c' \<otimes> (\<iota> a' \<ominus> \<iota> b')"
    using assms a'_id b'_id by (metis Qp.r_minus_distr \<eta>_nonzero a'_def angular_component_closed b'_def inc_closed p_intpow_closed(1))
  have 2: "ord (\<eta> x \<ominus> c) = ord c + ord (\<iota> a \<ominus> \<iota> b)"
    using 0  by (metis Qp.not_eq_diff_nonzero Qp_int_pow_nonzero \<eta>_nonzero a_def a_id angular_component_closed assms(10) assms(4) assms(5) assms(8) b_def b_id inc_closed ord_mult ord_p_pow_int p_nonzero)
  have 3: "ord (\<eta> x' \<ominus> c') = ord c' + ord (\<iota> a' \<ominus> \<iota> b')"
    using 1 by (metis Qp.not_eq_diff_nonzero Qp_int_pow_nonzero a'_closed a'_id assms(11) assms(9) b'_closed b'_id inc_closed ord_mult ord_p_pow_int p_nonzero)    
  have 4: "val ((\<iota> a \<ominus> \<iota> b) \<ominus> (\<iota> a' \<ominus> \<iota> b')) \<ge> e + 2*N"
  proof-
    have 40: "a (e+2*N) = a' (e+2*N)"
      unfolding a_def a'_def using assms \<eta>_nonzero unfolding ac_def by (metis Qp.not_nonzero_memI)
    have 41: "b (e+2*N) = b' (e+2*N)"
      unfolding b_def b'_def using assms unfolding ac_def by (metis Qp.not_nonzero_memI) 
    have 42:  "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) (e+2*N) = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') (e+2*N)"
      using residue_of_diff[of a b "e+2*N"] residue_of_diff[of a' b' "e+2*N"] a_closed a'_closed 
      unfolding 40 41 using "40" "41" b'_closed b_closed residue_of_diff by presburger
    have 43: "val_Zp ((a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')) \<ge> e+2*N"
      using 42 Zp.minus_closed a'_closed b'_closed b_closed local.a_closed val_Zp_dist_def val_Zp_dist_res_eq2 by presburger 
    thus ?thesis 
      by (metis Zp.minus_closed a'_closed b'_closed b_closed inc_of_diff local.a_closed val_of_inc)
  qed
  have 5: "ord (\<iota> a \<ominus> \<iota> b) = ord (\<iota> a' \<ominus> \<iota> b')"
  proof-
    have "ord_Zp (a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) = ord_Zp (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b')"
    proof(rule equal_res_imp_equal_ord_Zp[of "e+N"])
      show "0 < e+N"
        using assms(1) by blast
      show "a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b \<in> carrier Z\<^sub>p"
        using b_closed local.a_closed by blast
      show "a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b' \<in> carrier Z\<^sub>p"
        using a'_closed b'_closed by blast
      have 50: "a (e+2*N) = a' (e+2*N)"
      unfolding a_def a'_def using assms \<eta>_nonzero unfolding ac_def by (metis Qp.not_nonzero_memI)
      have 51: "b (e+2*N) = b' (e+2*N)"
      unfolding b_def b'_def using assms unfolding ac_def by (metis Qp.not_nonzero_memI) 
      have A: "e+N < e+2*N"
      by (simp add: assms(1))    
      have 52: "a (e+N) = a' (e+N)"
      using A 50 a_closed a'_closed equal_res_mod by blast
      have 53: "b (e+N) = b' (e+N)"
        using A 51 b_closed b'_closed equal_res_mod by blast
      show "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub>b) (e+N) = (a' \<ominus>\<^bsub>Z\<^sub>p\<^esub> b') (e+N)"
        using residue_of_diff[of a b "e+N"] residue_of_diff[of a' b' "e+N"] a_closed a'_closed 
        unfolding 52 53 using "52" "53" b'_closed b_closed residue_of_diff by presburger
      show "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) (e + N) \<noteq> 0"
        using assms by (metis Q\<^sub>p_def Qp.nonzero_memE(2) Zp_def \<eta>_nonzero a_def b_closed b_def local.a_closed padic_fields.ac_def padic_fields_axioms res_diff_zero_fact(1))
    qed
    thus ?thesis 
      by (metis Zp.not_eq_diff_nonzero a'_closed a'_id a_id assms(10) assms(11) assms(8) assms(9) b'_closed b'_id b_closed b_id inc_of_diff local.a_closed ord_of_inc)
  qed
  have 6: "val (\<iota> a \<ominus> \<iota> b) = val (\<iota> a' \<ominus> \<iota> b')" 
    by (metis (no_types, lifting) "5" Qp.minus_closed Qp.r_right_minus_eq a'_closed a'_id a_id 
        assms(10) assms(11) assms(8) assms(9) b'_closed b'_id b_closed b_id inc_closed local.a_closed val_ord')
  have 7: "(\<eta> x \<ominus> c) \<in> nonzero Q\<^sub>p"
    by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(10) assms(4) assms(5))
  have 8: "(\<eta> x' \<ominus> c') \<in> nonzero Q\<^sub>p"
    by (metis Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(11) assms(6) assms(7))
  have 9: "ord (\<iota> a \<ominus> \<iota> b) \<le> e + N"
  proof-
    have "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) (e + N) \<noteq> 0"
      using assms by (metis Q\<^sub>p_def Qp.nonzero_memE(2) Zp_def \<eta>_nonzero a_def b_closed b_def local.a_closed padic_fields.ac_def padic_fields_axioms res_diff_zero_fact(1))
    hence "ord_Zp(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) \<le> e + N"
      by (smt Zp.minus_closed b_closed local.a_closed zero_below_ord)
    thus ?thesis 
      by (metis Zp.not_eq_diff_nonzero \<open>(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) (e + N) \<noteq> 0\<close> b_closed inc_of_diff local.a_closed ord_of_inc res_diff_zero_fact'')
  qed
  hence 10: "val (\<iota> a \<ominus> \<iota> b) \<le> e + N"
    by (metis Qp.not_eq_diff_nonzero a_id assms(10) assms(8) b_closed b_id eint_ord_simps(1) inc_closed local.a_closed val_ord)
  have "e+2*N \<ge> val (\<iota> a \<ominus> \<iota> b) + N"
  proof-
    have "val (\<iota> a \<ominus> \<iota> b) + N \<le> e + N + eint N" using 10 
      using add_mono_thms_linordered_semiring(3) by blast
    hence "val (\<iota> a \<ominus> \<iota> b) + N \<le> e + N + N" 
      by (metis of_nat_add plus_eint_simps(1))
    thus ?thesis 
      by (metis ab_semigroup_add_class.add_ac(1) mult_2)
  qed
  hence 11: "val ((\<iota> a \<ominus> \<iota> b) \<ominus> (\<iota> a' \<ominus> \<iota> b')) \<ge> val (\<iota> a \<ominus> \<iota> b) + N"
    using 4 by (smt Q\<^sub>p_def Qp.minus_closed Qp.not_eq_diff_nonzero Qp.r_right_minus_eq Zp_def 
        a'_closed a'_id add.commute assms(1) assms(11) assms(9) b'_closed b'_id b_closed eint_ile 
        eint_ord_simps(1) inc_closed local.a_closed padic_fields.ac_ord_prop padic_fields_axioms val_ord')
  hence 12: "ac N (\<iota> a \<ominus> \<iota> b) = ac N (\<iota> a' \<ominus> \<iota> b')"
    using 6 by (metis Qp.not_eq_diff_nonzero a'_closed a'_id a_id ac_val assms(10) assms(11)
        assms(8) assms(9) b'_closed b'_id b_closed b_id inc_closed local.a_closed)
  hence 13: "ac N ((\<iota> a \<ominus> \<iota> b)\<div>(\<iota> a' \<ominus> \<iota> b')) = 1"
    by (metis (no_types, lifting) Q\<^sub>p_def Qp.minus_closed Qp.not_eq_diff_nonzero Qp.r_right_minus_eq Zp_def a'_closed a'_id ac_inv'''(1) ac_mult assms(1) assms(11) assms(9) b'_closed b'_id b_closed inc_closed local.a_closed padic_fields.inv_in_frac(1) padic_fields_axioms)
  have 14: "val ((\<iota> a \<ominus> \<iota> b)\<div>(\<iota> a' \<ominus> \<iota> b')) = 0" 
    by (metis "6" Q\<^sub>p_def Qp.Units_inv_closed Qp.Units_r_inv Qp.minus_closed Qp.not_eq_diff_nonzero Z\<^sub>p_def a'_closed a'_id assms(11) assms(9) b'_closed b'_id b_closed inc_closed local.a_closed padic_fields.Units_eq_nonzero padic_fields_axioms val_mult val_one)
  hence "((\<iota> a \<ominus> \<iota> b)\<div>(\<iota> a' \<ominus> \<iota> b')) \<in> P_set n"
    using 13 assms 
    by (metis Qp.minus_closed Qp.not_eq_diff_nonzero a'_closed a'_id b'_closed b'_id b_closed fract_closed inc_closed local.a_closed)
  hence 15: "pow_res n (\<iota> a \<ominus> \<iota> b) = pow_res n (\<iota> a' \<ominus> \<iota> b')" using equal_pow_resI'[of  "(\<iota> a \<ominus> \<iota> b)"" (\<iota> a' \<ominus> \<iota> b')"" (\<iota> a \<ominus> \<iota> b)\<div>(\<iota> a' \<ominus> \<iota> b')" n]
    by (metis Qp.not_eq_diff_nonzero a'_closed a'_id a_id assms(10) assms(11) assms(2) assms(8) assms(9) b'_closed b'_id b_closed b_id equal_pow_resI'' inc_closed local.a_closed)
  have 16: "pow_res n (\<pp>[^]ord c) = pow_res n (\<pp>[^]ord c')"
  proof-
    obtain l where l_def: "ord c = ord c' + l* int n"
      using assms by (metis mod_eqE mult_of_nat_commute)
    have "\<pp> [^] (l * int n) = (\<pp>[^]l)[^]n"
      using Qp_p_int_nat_pow_pow by blast
    hence "\<pp> [^] (l * int n) \<in> P_set n "
      using P_set_memI 
      by (metis Qp.nonzero_memE(2) Qp_int_pow_nonzero p_intpow_closed(1) p_nonzero)
    thus ?thesis  using equal_pow_resI'[of "\<pp>[^]ord c" "\<pp>[^]ord c'" "\<pp>[^](l*n)" n] unfolding l_def
      using assms(2) p_intpow_add p_intpow_closed(1) by blast
  qed
  show ?thesis unfolding 0 1 using 15 16 
    by (meson Qp.minus_closed a'_closed assms(2) b'_closed b_closed inc_closed local.a_closed p_intpow_closed(1) pow_res_mult)
qed

end 

subsubsection\<open>Fact vi)\<close>

text\<open>The proof of fact vi) requires some basic information about geometric sums\<close>
context cring
begin

fun geom_sum where
"geom_sum 0 a = \<one>"|
"geom_sum (Suc n) a = geom_sum n a \<oplus> a[^](Suc n)"

lemma geom_sum_closed:
  assumes "a \<in> carrier R"
  shows "geom_sum n a \<in> carrier R"
  apply(induction n) 
   apply simp 
  by(simp , intro ring_simprules, auto simp: assms)
  
lemma geom_sum_factor:
  assumes "a \<in> carrier R"
  shows "a[^](Suc n) \<ominus> \<one> = (a \<ominus> \<one>)\<otimes>(geom_sum n a)"
proof(induction n)
  case 0
  then show ?case 
    by (simp add: assms)
next
  case (Suc n)
  have 0: "(a \<ominus> \<one>) \<otimes> geom_sum (Suc n) a = (a \<ominus> \<one>) \<otimes> geom_sum n a \<oplus> (a \<ominus> \<one>) \<otimes>a[^](Suc n)"
    using assms unfolding geom_sum.simps(2) 
    by (simp add: geom_sum_closed r_distr)
  hence 1: "(a \<ominus> \<one>) \<otimes> geom_sum (Suc n) a = a [^] Suc n \<ominus> \<one> \<oplus> (a \<ominus> \<one>) \<otimes>a[^](Suc n)"
    unfolding Suc by auto 
  have 11: "(a \<oplus> \<ominus> \<one>) \<otimes> a [^] Suc n = a \<otimes> a [^] Suc n \<oplus> \<ominus> \<one> \<otimes> a [^] Suc n"
    using l_distr[of a "\<ominus> \<one>" "a [^] Suc n"] assms by blast
  have 12: "(a \<oplus> \<ominus> \<one>) \<otimes> a [^] Suc n = a [^] Suc (Suc n) \<oplus> \<ominus> \<one> \<otimes> a [^] Suc n"
    using assms 11  by (simp add: cring.cring_simprules(14) is_cring)
  have 13: " \<ominus> \<one> \<otimes> (a [^] Suc n) =  \<ominus> (a [^] Suc n)"
    unfolding 12 using assms by (simp add: l_minus)
  have 2: "(a \<ominus> \<one>) \<otimes> geom_sum (Suc n) a = a [^] Suc n \<ominus> \<one> \<oplus> a[^](Suc (Suc n)) \<ominus> a[^](Suc n)"
    using assms 
    unfolding 1 unfolding a_minus_def 12 unfolding 13 
    using a_assoc  by force
  then show ?case using assms a_comm unfolding a_minus_def
    by (smt add.inv_closed add.m_assoc add.m_closed nat_pow_closed one_closed r_neg1)
qed

lemma geom_sum_iter:
  assumes "a \<in> carrier R"
  shows "geom_sum (Suc n) a = \<one> \<oplus> a \<otimes>(geom_sum n a)"
proof(induction n)
  case 0
  then show ?case using assms  by simp 
next
  case (Suc n)
  have 0: "geom_sum (Suc (Suc n)) a = a[^](Suc (Suc n)) \<oplus> (\<one> \<oplus> a \<otimes> (geom_sum n a))"
    using Suc.IH add.m_comm assms geom_sum_closed by auto
  hence 1: "geom_sum (Suc (Suc n)) a = \<one> \<oplus> (a[^](Suc (Suc n)) \<oplus>  a \<otimes> (geom_sum n a))"
    by (simp add: add.m_lcomm assms geom_sum_closed)
  hence 2: "geom_sum (Suc (Suc n)) a = \<one> \<oplus> a \<otimes>(a[^](Suc n) \<oplus> (geom_sum n a))"
    by (metis assms geom_sum_closed nat_pow_Suc2 nat_pow_closed r_distr)
  thus ?case  using assms a_comm 
    by (simp add: geom_sum_closed)
qed

lemma geom_sum_factor':
  assumes "a \<in> carrier R"
  shows "a[^](Suc (Suc n)) \<ominus> \<one> = (a \<ominus> \<one>)\<otimes>(\<one> \<oplus> a \<otimes>(geom_sum n a))"
  using assms geom_sum_iter geom_sum_factor by metis 

lemma geom_sum_factor'':
  assumes "a \<in> carrier R"
  assumes "(k::nat) \<ge> 2"
  shows "\<exists>b \<in> carrier R. a[^]k \<ominus> \<one> = (a \<ominus> \<one>)\<otimes>(\<one> \<oplus> (a\<otimes>b))"
proof-
  obtain n where n_def: "Suc (Suc n) = k"
    using assms nat_le_iff_add by auto
  thus ?thesis using geom_sum_factor'[of a n] geom_sum_closed[of a n] assms unfolding n_def  by blast 
qed

lemma(in ring_hom_ring) equal_image:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "h a = h b"
  shows "\<exists>c \<in> carrier R. h c = \<zero>\<^bsub>S\<^esub> \<and> a = b \<oplus> c"
  using assms 
  by (metis R.add.inv_mult_group R.add.m_closed R.add.m_comm R.add.r_inv_ex R.minus_minus R.minus_zero R.r_neg1 R.r_zero 
      R.zero_closed hom_add hom_zero )

lemma geom_sum_ring_hom:
  assumes "a \<in> carrier R"
  assumes "ring_hom_ring R S \<phi>"
  assumes "\<phi> a = \<one>\<^bsub>S\<^esub>"
  shows "\<exists>s \<in> carrier R. \<phi> s = \<zero>\<^bsub>S\<^esub> \<and> geom_sum n a = [(Suc n)]\<cdot>\<one> \<oplus> s"
proof(induction n)
  case 0
  show?case using assms unfolding geom_sum.simps 
    using ring_hom_ring.equal_image by fastforce
next
  case (Suc n)
  obtain b where b_def: "b \<in> carrier R \<and> \<phi> b = \<zero>\<^bsub>S\<^esub> \<and> a = \<one> \<oplus> b"
    using ring_hom_ring.equal_image[of R S \<phi> a \<one>] ring_hom_one assms 
    by (metis one_closed ring_hom_ring.homh)
  obtain s where s_def: "s \<in> carrier R \<and> \<phi> s = \<zero>\<^bsub>S\<^esub> \<and> geom_sum n a = [Suc n] \<cdot> \<one> \<oplus> s"
   using Suc.IH by blast
  have I0: "geom_sum (Suc n) a = [Suc n] \<cdot> \<one> \<oplus> s \<oplus> a[^](Suc n)"
    unfolding geom_sum.simps using s_def by simp
  have I1: "\<phi> (a[^](Suc n)) = \<one>\<^bsub>S\<^esub>"
    using  ring_hom_ring.hom_nat_pow[of R S \<phi> a "Suc n"] assms unfolding assms(3)
    by (metis (full_types) Group.nat_pow_0 local.ring_axioms monoid.nat_pow_one one_closed ring_def ring_hom_ring.hom_nat_pow)
  then obtain s' where s'_def: "s' \<in> carrier R \<and> \<phi> s' = \<zero>\<^bsub>S\<^esub> \<and> a[^](Suc n) = \<one> \<oplus> s'"
    using ring_hom_ring.equal_image[of R S \<phi> "a[^](Suc n)" \<one>] 
    by (metis assms(1) assms(2) nat_pow_closed one_closed ring_hom_one ring_hom_ring.homh)    
  hence I2: "geom_sum (Suc n) a = [Suc n] \<cdot> \<one> \<oplus> s \<oplus> \<one> \<oplus> s'" 
    by (simp add: add.m_assoc s_def)
  hence I3: "geom_sum (Suc n) a = [Suc n] \<cdot> \<one> \<oplus> \<one> \<oplus> (s' \<oplus> s)" 
    by (simp add: add.m_comm local.ring_axioms ring.ring_simprules(22) s'_def s_def)
  hence I4: "geom_sum (Suc n) a = [(Suc (Suc n))] \<cdot> \<one> \<oplus> (s' \<oplus> s)" 
    by simp
  have "s' \<oplus> s \<in> carrier R \<and> \<phi> (s \<oplus>s') = \<zero>\<^bsub>S\<^esub>"
    using assms s_def s'_def ring_hom_add[of \<phi> R S s s'] 
    by (metis add.m_closed ring.ring_simprules(15) ring.ring_simprules(2) ring_hom_ring.axioms(2) ring_hom_ring.homh)
  then show ?case using I4 s_def s'_def 
    by (simp add: add.m_comm) 
qed


lemma fractional_id: 
  assumes "a \<in> carrier R"
  assumes "b \<in> Units R"
  assumes "c \<in> Units R"
  shows "a \<otimes> inv b = (c \<otimes> a) \<otimes> inv (c \<otimes> b)"
  by (metis (no_types, lifting) Units_closed Units_inv_closed assms(1) assms(2) assms(3)
                                inv_cancelR(2) inv_of_prod m_assoc m_closed)

lemma equal_fractionI:
  assumes "a = c" 
  assumes "b = d"
  shows "a \<otimes> inv b = c \<otimes> inv d"
  using assms by auto 

lemma(in field) geom_sum_fractional_identity:
  assumes "\<eta> \<in> carrier R"
  assumes "c \<in> Units R"
  assumes "\<eta> \<noteq> c"
  assumes "k > 0"
  shows "((\<eta> \<otimes> inv c)[^](k::nat) \<ominus> \<one>)\<otimes> inv ((\<eta> \<otimes> inv c) \<ominus> \<one>) = 
            (\<eta>[^]k \<ominus> c[^]k)\<otimes> inv (c[^](k-1) \<otimes>(\<eta> \<ominus> c))"
proof- 
  have 0: "((\<eta> \<otimes> inv c)[^]k \<ominus> \<one>)\<otimes> inv ((\<eta> \<otimes> inv c) \<ominus> \<one>) = 
            (c[^]k \<otimes> ((\<eta> \<otimes> inv c)[^]k \<ominus> \<one>))\<otimes> inv (c[^]k \<otimes>((\<eta> \<otimes> inv c) \<ominus> \<one>))"
    apply(intro fractional_id[of _ _ "c[^]k"] ring_simprules nat_pow_closed assms)
    apply (simp add: assms(2))
     apply (metis (no_types, lifting) UnitsI(2) Units_inv_closed Units_inv_inv assms(1) assms(2) 
                  assms(3) field_inv(1) field_inv(3) invI(2) m_closed minus_closed one_closed 
                  r_right_minus_eq)
    using assms by (simp add: Units_pow_closed)
  have 1: " c [^] k \<otimes> (\<eta> \<otimes> inv c \<ominus> \<one>) =  c [^] k \<otimes> \<eta> \<otimes> inv c \<ominus> c [^] k "
    by (metis Units_closed Units_inv_closed Units_pow_closed assms(1) assms(2) m_assoc 
              m_closed one_closed r_minus_distr r_one)
  have 2: "c [^] (k - 1) \<otimes> (\<eta> \<ominus> c) = c [^] (k - 1) \<otimes> \<eta> \<ominus> c[^]k"
    using assms r_minus_distr 
    by (metis (no_types, lifting) Suc_pred Units_closed add.right_neutral local.nat_pow_Suc
        nat_pow_closed plus_1_eq_Suc)
  have 3: "c [^]k \<otimes> inv c = c [^](k-1) \<otimes> c \<otimes> inv c"
    using assms 
    by (metis Suc_pred' local.nat_pow_Suc)
  have 4: "c [^]k \<otimes> inv c = c [^](k-1)"
    unfolding 3 
    by (meson Units_closed assms(2) inv_cancelL(2) m_closed nat_pow_closed)
  have 4: "c [^] k \<otimes> \<eta> \<otimes> inv c = c [^] (k-1) \<otimes> \<eta>"
    using assms m_comm[of \<eta> "inv c"] 3 
    by (metis "4" Units_closed Units_inv_closed m_assoc nat_pow_closed)   
  show ?thesis unfolding 0 1 2 4 
    apply(rule equal_fractionI)
     apply (smt (verit) Units_inv_closed Units_inv_inv Units_inverse assms(1) assms(2) inv_cancelL(1)
        m_closed nat_pow_closed nat_pow_distrib one_closed r_minus_distr r_one)
    by auto 
qed

end

context denef_lemma_2_4
begin

lemma fact_vi:
  fixes N::nat fixes n::nat fixes j::int
  assumes "N > 0"
  assumes "n > 0"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "c \<in> nonzero Q\<^sub>p" 
  assumes "ord (\<eta> x) =  ord c"
  assumes "ac (e + N) (\<eta> x) = ac (e + N) c"
  shows "val (\<eta> x \<ominus> c) = val ((\<xi>_1 x \<ominus> c[^]k) \<div> ([k]\<cdot>(c[^](k-1))))"
        "pow_res n (\<eta> x \<ominus> c) = pow_res n ((\<xi>_1 x \<ominus> c[^]k) \<div> ([k]\<cdot>(c[^](k-1))))"
proof-
  obtain a where a_def: "a = angular_component (\<eta> x)"
    by blast 
  obtain b where b_def: "b = angular_component c"
    by blast
  have a_closed: "a \<in> carrier Z\<^sub>p"
    unfolding a_def using assms  \<eta>_nonzero angular_component_closed by blast
  have b_closed: "b \<in> carrier Z\<^sub>p"
    unfolding b_def using assms angular_component_closed by blast
  have val_Zp_a: "val_Zp a = 0"
    unfolding a_def using assms \<eta>_nonzero angular_component_unit unit_imp_val_Zp0 by blast
  have val_Zp_b: "val_Zp b = 0"
    unfolding b_def using assms angular_component_unit unit_imp_val_Zp0 by blast
  obtain d where d_def: "d = angular_component ((\<eta> x) \<div> c)"
    by blast 
  have d_closed: "d \<in> carrier Z\<^sub>p" 
    unfolding d_def by (metis Qp.nonzero_closed Qp.not_nonzero_memE Qp.not_nonzero_memI Qp.r_null \<eta>_characterization \<eta>_nonzero angular_component_closed assms(4) assms(5) fract_closed local.fract_cancel_right)    
  have d_mult: "a = d \<otimes>\<^bsub>Z\<^sub>p\<^esub> b"
    unfolding a_def d_def b_def using assms 
    by (smt Q\<^sub>p_def Qp.m_assoc Qp.one_nonzero \<eta>_closed \<eta>_nonzero angular_component_mult 
        frac_nonzero_inv(2) frac_nonzero_inv_closed local.fract_cancel_left mult_assoc nonzero_inverse_Qp)
  obtain \<phi> where \<phi>_def: "\<phi> = (\<lambda>(x::padic_int). x (e+N))"
    by blast 
  have \<phi>_hom: "ring_hom_ring Z\<^sub>p (Zp_res_ring (e+N)) \<phi>"
    unfolding \<phi>_def using res_map_is_hom add_gr_0 assms(1) by blast
  have "\<phi> d = \<one>\<^bsub>Zp_res_ring (e+N)\<^esub>"
  proof-
    have 0: "d (e+N) = ac (e+N) (\<eta> x \<div> c)"
      unfolding d_def 
      by (smt Qp.Units_inv_closed Units_eq_nonzero \<eta>_closed ac_inv'''(1) ac_mult add_gr_0 assms(1) assms(4) assms(5) assms(7) padic_fields.ac_def padic_fields_axioms)
    have  "d (e+N) = ac (e+N)(\<eta> x) \<otimes>\<^bsub>Zp_res_ring (e+N)\<^esub> inv\<^bsub>Zp_res_ring (e+N)\<^esub> ac (e+N) c"
      unfolding 0  using assms ac_of_fraction[of "e+N" "\<eta> x" c] \<eta>_nonzero by blast
    thus ?thesis using assms 0 \<eta>_nonzero \<phi>_def ac_inv'''(1) ac_mult' add_gr_0 nonzero_inverse_Qp p_res_ring_one by presburger
  qed
  then obtain  s where s_def: "s \<in> carrier Z\<^sub>p \<and> \<phi> s = \<zero>\<^bsub>Zp_res_ring (e+N)\<^esub> \<and> Zp.geom_sum (k-1) d = [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> s"
    using Zp.geom_sum_ring_hom[of d "Zp_res_ring (e+N)" \<phi> "k-1"] \<phi>_hom 
    by (metis One_nat_def Suc_pred d_closed denef_lemma_2_4.DL_2_4_0 denef_lemma_2_4_axioms not_gr0 not_numeral_le_zero)    
  have 0: "d[^]\<^bsub>Z\<^sub>p\<^esub>k \<ominus>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> = (d \<ominus>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)\<otimes>\<^bsub>Z\<^sub>p\<^esub>([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> s)"
    using Zp.geom_sum_iter   by (metis One_nat_def Suc_pred Zp.geom_sum_factor d_closed denef_lemma_2_4.DL_2_4_0 
        denef_lemma_2_4_axioms not_gr0 not_numeral_le_zero s_def)
  show "val (\<eta> x \<ominus> c) = val ((\<xi>_1 x \<ominus> c[^]k) \<div> ([k]\<cdot>(c[^](k-1))))"
 proof(cases "\<eta> x = c")
  case True
  then have "\<xi>_1 x \<ominus> c [^] k = \<zero>"
    by (metis Qp.nat_pow_closed Qp.nonzero_closed Qp.r_right_minus_eq \<eta>_pow assms(4) assms(5))
  then show ?thesis using True 
    by (metis (no_types, lifting) Q\<^sub>p_def Qp.add_pow_ldistr Qp.integral_iff Qp.nat_mult_closed 
        Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_pow_nonzero Qp.r_right_minus_eq 
        Qp.zero_closed Qp_char_0 Zp_def assms(5) denef_lemma_2_4.DL_2_4_0 denef_lemma_2_4_axioms
        field_inv(2) not_numeral_le_zero padic_fields.inv_in_frac(1) padic_fields_axioms zero_fract)    
next
    case False
    then have "a \<noteq> b"
      unfolding  a_def b_def by (metis \<eta>_nonzero angular_component_factors_x assms(4) assms(5) assms(6))
    then have F0:"d \<noteq> \<one>\<^bsub>Z\<^sub>p\<^esub>"
      unfolding d_def by (metis Zp.l_one b_closed d_def d_mult)
    have F1: "d \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      unfolding d_def by (metis \<eta>_ac a_def ac_def assms(4) d_def d_mult mult_zero_r residue_of_zero(2) zero_neq_one)
    have F2: "\<iota> d[^]k \<ominus> \<one> = (\<iota> d \<ominus> \<one>)\<otimes>([k]\<cdot>\<one> \<oplus> \<iota> s)"
    proof-
      have F20: "\<iota> (d[^]\<^bsub>Z\<^sub>p\<^esub>k) = \<iota> d [^] k"
        using d_closed F1 inc_pow not_nonzero_Zp by blast
      have F21: "\<iota> ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> s) = [k]\<cdot>\<one> \<oplus> \<iota> s"
        using Zp_nat_inc_closed inc_of_nat inc_of_sum s_def by presburger
      show ?thesis using F21 F20 0 
        by (metis Zp.add.m_closed Zp.minus_closed Zp.nat_pow_closed Zp.one_closed Zp_nat_inc_closed d_closed inc_of_diff inc_of_one inc_of_prod s_def)
    qed
    have F3: "\<iota> d \<ominus> \<one>\<noteq> \<zero> "
      using F0 by (metis Qp.r_right_minus_eq Zp.one_closed \<iota>_def d_closed inc_closed inc_inj2 inc_of_one)
    hence F4: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = ([k]\<cdot>\<one> \<oplus> \<iota> s)"
      by (metis F2 Q\<^sub>p_def Qp.add.m_closed Qp.inv_cancelR(2) Qp.m_closed Qp.minus_closed
          Qp.nat_inc_closed Qp.not_eq_diff_nonzero Qp.one_closed Qp.r_right_minus_eq Zp_def
          d_closed inc_closed padic_fields.Units_eq_nonzero padic_fields_axioms s_def)
    have F5: "val (\<eta> x \<div> c) = 0"
      by (metis False Qp.nonzero_closed \<eta>_characterization \<eta>_nonzero assms(4) assms(5) assms(6) 
          field_inv(2) idiff_0_right ord_fract ord_one val_fract val_one val_ord zero_eint_def zero_fract)
    have F6: "\<iota> d = (\<eta> x \<div> c)"
      unfolding d_def a_def  b_def 
      apply(rule angular_component_ord_zero) 
      using val_ord assms \<eta>_nonzero F5 ord_fract apply presburger
      by (metis F5 \<eta>_closed assms(4) assms(5) fract_closed val_nonzero' zero_eint_def)
    have F7: "\<iota> d \<in> nonzero Q\<^sub>p"
      unfolding F6 by (metis F5 \<eta>_closed assms(4) assms(5) fract_closed val_nonzero' zero_eint_def)
    have F8: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c)))"
    proof-
      have F80:  "\<iota> d[^]k \<ominus> \<one> = (\<eta> x \<div> c)[^]k \<ominus> \<one>"
        unfolding F6 using assms F7 by blast
      hence F81:  "\<iota> d[^]k \<ominus> \<one> =(\<eta> x  [^]k\<div> c [^]k) \<ominus> \<one>"
        using Qp.Units_inv_closed Qp.nat_pow_distrib Qp.nonzero_closed Qp.nonzero_memE(2) 
          Units_eq_nonzero \<eta>_closed assms(4) assms(5) field_nat_pow_inv by presburger
      have F82:  "c[^]k \<otimes> (\<iota> d[^]k \<ominus> \<one>) = (\<eta> x [^]k \<ominus> c[^]k)"
        unfolding F6 by (smt Qp.Units_r_inv Qp.nat_pow_closed Qp.nat_pow_distrib Qp.nonzero_closed 
            Qp.r_minus_distr Qp_nat_pow_nonzero Units_eq_nonzero \<eta>_closed assms(4) assms(5) 
            fract_closed local.fract_cancel_right)
      have F83: "c \<otimes>(\<iota> d \<ominus> \<one>) = \<eta> x  \<ominus> c"
        unfolding F6 using assms by (metis Qp.Units_r_inv Qp.nonzero_closed Qp.r_minus_distr 
            Units_eq_nonzero \<eta>_closed fract_closed local.fract_cancel_right)
      have F84: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = ((c[^]k \<otimes> (\<iota> d[^]k \<ominus> \<one>)) \<div> (c[^]k \<otimes>(\<iota> d \<ominus> \<one>)))"
        using assms by (smt F0 F2 F3 F4 Q\<^sub>p_def Qp.Units_r_inv Qp.m_assoc Qp.m_comm Qp.minus_closed
            Qp.nat_pow_closed Qp.nonzero_closed Qp.not_eq_diff_nonzero Qp_nat_pow_nonzero
            Units_eq_nonzero Zp.one_closed Zp_def \<iota>_def d_closed inc_closed inc_inj2 inc_of_one 
            local.fract_mult padic_fields.inv_in_frac(1) padic_fields_axioms)
      have F85: "c[^]k = c[^](k-1)\<otimes>c" by (metis DL_2_4_0 One_nat_def Qp.nat_pow_Suc Suc_pred 
            neq0_conv not_numeral_le_zero)
      hence F86: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = ((\<eta> x [^]k \<ominus> c[^]k) \<div> (c[^](k-1)\<otimes>c \<otimes>(\<iota> d \<ominus> \<one>)))"
        using F84 unfolding F85 by (metis F82 F85)
      thus F87: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = ((\<eta> x [^]k \<ominus> c[^]k) \<div> (c[^](k-1)\<otimes>(\<eta> x  \<ominus> c)))"
        using F7 F83 Qp.m_assoc Qp.minus_closed Qp.nat_pow_closed Qp.nonzero_closed Qp.one_closed assms(5) by presburger
    qed
    hence F9: " (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) = ([k]\<cdot>\<one> \<oplus> \<iota> s)"
      unfolding F4 by blast 
    hence F10: " (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =[k]\<cdot>\<one> \<otimes> (\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      by (smt DL_2_4_0 Q\<^sub>p_def Qp.m_closed Qp.nat_mult_closed Qp.one_closed Qp.r_distr Qp_char_0 
          Zp_def field_inv(2) inc_closed local.fract_cancel_right not_nonzero_Qp not_numeral_le_zero
          padic_fields.inv_in_frac(1) padic_fields_axioms s_def)
    hence F11: "(\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =[k]\<cdot>\<one> \<otimes> (\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      by blast
    have F12: "val (\<iota> s) \<ge> e + N"
    proof-
      have "val_Zp s \<ge> e+N" apply(cases "s = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
        using val_Zp_def eint_ord_code(3) apply presburger
        using s_def ord_Zp_geq[of s "e+N"] unfolding \<phi>_def val_Zp_def ord_Zp_def  
        using eint_ord_simps(1) padic_simps(1) padic_zero_simp(2) by presburger
      then show ?thesis by (metis s_def val_of_inc)
    qed
    have F13: "val (\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>)) = 0"
    proof-
      have "val (\<iota> s \<div> [k]\<cdot>\<one>) = val (\<iota> s) - e"
        unfolding e_def by (metis DL_2_4_0 Q\<^sub>p_def Qp.nat_inc_closed Zp_def e_def e_eq inc_closed 
            neq0_conv not_nonzero_Qp not_numeral_le_zero padic_fields.Qp_char_0 padic_fields_axioms 
            s_def val_fract val_ord_nat_inc)
      hence "val (\<iota> s \<div> [k]\<cdot>\<one>) \<ge> e + N - eint e"
      proof -
        have "\<forall>e i ia. eint i \<le> e - eint ia \<or> \<not> eint (ia + i) \<le> e"
          by (metis add_cancel_eint_geq eint_add_cancel_fact not_eint_eq plus_eint_simps(1)) 
        then show ?thesis
          by (metis F12 \<open>val (\<iota> s \<div> [k] \<cdot> \<one>) = val (\<iota> s) - eint (int e)\<close> add.commute add_diff_cancel idiff_eint_eint of_nat_add)
      qed       
      hence "val (\<iota> s \<div> [k]\<cdot>\<one>) \<ge> N"
      proof -
        show ?thesis
          by (metis (no_types) \<open>eint (int (e + N)) - eint (int e) \<le> val (\<iota> s \<div> [k] \<cdot> \<one>)\<close> add.commute add_diff_cancel idiff_eint_eint of_nat_add)
      qed
      thus ?thesis
        by (smt DL_2_4_0 Q\<^sub>p_def Qp.add.m_comm Qp.m_closed Qp.nat_inc_closed Qp.one_closed Zp_def assms(1) eint_pow_int_is_pos inc_closed less_le_trans not_numeral_le_zero of_nat_0_less_iff padic_fields.Qp_char_0 padic_fields.inv_in_frac(1) padic_fields_axioms s_def val_one val_ultrametric_noteq) 
    qed
    have F14: "val (\<eta> x [^]k \<ominus> c[^]k) -( val (c[^](k-1)) + val  (\<eta> x \<ominus> c)) =val ([k]\<cdot>\<one> )"
      using F10 F13 val_mult by (metis (no_types, lifting) DL_2_4_0 False Q\<^sub>p_def Qp.add.m_closed 
          Qp.integral Qp.m_closed Qp.minus_closed Qp.nat_inc_closed Qp.nat_pow_closed 
          Qp.nonzero_closed Qp.nonzero_pow_nonzero Qp.one_closed Qp.r_right_minus_eq Qp_char_0 
          Zp_def \<eta>_closed add.right_neutral assms(4) assms(5) inc_closed not_nonzero_Qp 
          not_numeral_le_zero padic_fields.inv_in_frac(1) padic_fields_axioms s_def val_fract)
    have F15: "c[^](k-1) \<in> nonzero Q\<^sub>p"
      using Qp_nat_pow_nonzero assms(5) by blast
    have F16: "(\<eta> x \<ominus> c) \<in> nonzero Q\<^sub>p"
      using False Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(4) assms(5) by blast
    have F17: "[k]\<cdot>\<one> \<in> nonzero Q\<^sub>p"
      using DL_2_4_0 by (metis Q\<^sub>p_def Qp.nat_inc_closed Zp_def not_nonzero_Qp not_numeral_le_zero
          padic_fields.Qp_char_0 padic_fields_axioms)
    have F18: "(\<eta> x [^]k \<ominus> c[^]k) \<in> nonzero Q\<^sub>p"
      by (metis (no_types, lifting) F10 F13 F15 F16 F17 Q\<^sub>p_def Qp.add.m_closed Qp.integral_iff
          Qp.m_closed Qp.nat_pow_closed Qp.nonzero_closed Qp.not_eq_diff_nonzero Qp.one_closed
          Qp.r_right_minus_eq Qp.zero_closed Zp_def \<eta>_closed assms(4) assms(5) inc_closed 
          padic_fields.inv_in_frac(1) padic_fields_axioms s_def val_nonzero' zero_eint_def)
    hence F19: "val (\<eta> x [^]k \<ominus> c[^]k) - val (c[^](k-1)) -  val  (\<eta> x \<ominus> c) =val ([k]\<cdot>\<one> )"
      using F14 F15 F16 F17 F18 val_ord eint_minus_plus val_ord by metis 
    hence F20: "val (\<eta> x [^]k \<ominus> c[^]k) - val (c[^](k-1)) -  val ([k]\<cdot>\<one> ) = val  (\<eta> x \<ominus> c)"
      using eint_minus_plus''[of "val (\<eta> x [^] k \<ominus> c [^] k)" "ord (c[^](k-1))" "ord (\<eta> x \<ominus> c)" ] 
            F15 F16 F17 val_ord by metis 
    have F21: "val (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = val (\<xi>_1 x \<ominus> c[^]k) - val ([k] \<cdot> (c [^] (k - 1)))"
      by (metis (no_types, lifting) F17 F18 Q\<^sub>p_def Qp.Units_inv_closed Qp.Units_r_inv Qp.add_pow_ldistr Qp.nat_mult_closed Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_pow_nonzero Units_eq_nonzero Z\<^sub>p_def \<eta>_characterization assms(4) assms(5) padic_fields.val_def padic_fields_axioms val_fract val_nonzero' zero_fract)
    have F22: "[k]\<cdot>\<one> \<otimes>  c [^] (k - 1) = [k] \<cdot> (c [^] (k - 1))"
      using nat_add_pow_mult_assoc[of "c[^](k-1)" k] F15 Qp.nonzero_closed by blast
    hence "val (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = val (\<xi>_1 x \<ominus> c[^]k) - val ([k]\<cdot>\<one> \<otimes>  c [^] (k - 1))"
      using F21 by presburger
    hence "val (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = val (\<xi>_1 x \<ominus> c[^]k)  - val (c [^] (k - 1)) - val ([k]\<cdot>\<one>)"
      using F15 F17 eint_minus_plus val_mult0 val_ord eint_minus_plus' by presburger
    hence "val (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = val (\<eta> x [^]k \<ominus> c[^]k) - val (c [^] (k - 1)) - val ([k]\<cdot>\<one>)"
      using assms \<eta>_pow by presburger
    hence F15: "val (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = val  (\<eta> x \<ominus> c)"
      using F20 by presburger      
    then show ?thesis by metis 
   qed
  show " pow_res n (\<eta> x \<ominus> c) = pow_res n (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1)))"
   proof(cases "\<eta> x = c")
    case True
    then have "\<xi>_1 x \<ominus> c [^] k = \<zero>"
      by (metis Qp.nat_pow_closed Qp.nonzero_closed Qp.r_right_minus_eq \<eta>_pow assms(4) assms(5))
    then show ?thesis using True 
      by (metis (no_types, lifting) Q\<^sub>p_def Qp.add_pow_ldistr Qp.integral_iff Qp.nat_mult_closed 
          Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_pow_nonzero Qp.r_right_minus_eq 
          Qp.zero_closed Qp_char_0 Zp_def assms(5) denef_lemma_2_4.DL_2_4_0 denef_lemma_2_4_axioms
          field_inv(2) not_numeral_le_zero padic_fields.inv_in_frac(1) padic_fields_axioms zero_fract)    
   next
    case False
    then have "a \<noteq> b"
      unfolding  a_def b_def by (metis \<eta>_nonzero angular_component_factors_x assms(4) assms(5) assms(6))
    then have F0:"d \<noteq> \<one>\<^bsub>Z\<^sub>p\<^esub>"
      unfolding d_def by (metis Zp.l_one b_closed d_def d_mult)
    have F1: "d \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
      unfolding d_def by (metis \<eta>_ac a_def ac_def assms(4) d_def d_mult mult_zero_r residue_of_zero(2) zero_neq_one)
    have F2: "\<iota> d[^]k \<ominus> \<one> = (\<iota> d \<ominus> \<one>)\<otimes>([k]\<cdot>\<one> \<oplus> \<iota> s)"
    proof-
      have F20: "\<iota> (d[^]\<^bsub>Z\<^sub>p\<^esub>k) = \<iota> d [^] k"
        using d_closed F1 inc_pow not_nonzero_Zp by blast
      have F21: "\<iota> ([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<oplus>\<^bsub>Z\<^sub>p\<^esub> s) = [k]\<cdot>\<one> \<oplus> \<iota> s"
        using Zp_nat_inc_closed inc_of_nat inc_of_sum s_def by presburger
      show ?thesis using F21 F20 0 
        by (metis Zp.add.m_closed Zp.minus_closed Zp.nat_pow_closed Zp.one_closed Zp_nat_inc_closed d_closed inc_of_diff inc_of_one inc_of_prod s_def)
    qed
    have F3: "\<iota> d \<ominus> \<one>\<noteq> \<zero> "
      using F0 by (metis Qp.r_right_minus_eq Zp.one_closed \<iota>_def d_closed inc_closed inc_inj2 inc_of_one)
    hence F4: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = ([k]\<cdot>\<one> \<oplus> \<iota> s)"
      by (metis F2 Q\<^sub>p_def Qp.add.m_closed Qp.inv_cancelR(2) Qp.m_closed Qp.minus_closed
          Qp.nat_inc_closed Qp.not_eq_diff_nonzero Qp.one_closed Qp.r_right_minus_eq Zp_def
          d_closed inc_closed padic_fields.Units_eq_nonzero padic_fields_axioms s_def)
    have F5: "val (\<eta> x \<div> c) = 0"
      by (metis False Qp.nonzero_closed \<eta>_characterization \<eta>_nonzero assms(4) assms(5) assms(6) 
          field_inv(2) idiff_0_right ord_fract ord_one val_fract val_one val_ord zero_eint_def zero_fract)
    have F6: "\<iota> d = (\<eta> x \<div> c)"
      unfolding d_def a_def  b_def 
      apply(rule angular_component_ord_zero) 
      using val_ord assms \<eta>_nonzero F5 ord_fract apply presburger
      by (metis F5 \<eta>_closed assms(4) assms(5) fract_closed val_nonzero' zero_eint_def)
    have F7: "\<iota> d \<in> nonzero Q\<^sub>p"
      unfolding F6 by (metis F5 \<eta>_closed assms(4) assms(5) fract_closed val_nonzero' zero_eint_def)
    have F8: "\<iota> d[^]k \<ominus> \<one> \<div> (\<iota> d \<ominus> \<one>) = (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c)))"
     apply(unfold F6, rule Qp.geom_sum_fractional_identity)
        using \<eta>_closed assms(4)Units_eq_nonzero assms(5)False DL_2_4_0 by auto 
    hence F9: " (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) = ([k]\<cdot>\<one> \<oplus> \<iota> s)"
      unfolding F4 by blast 
    hence F10: " (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =[k]\<cdot>\<one> \<otimes> (\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      by (smt DL_2_4_0 Q\<^sub>p_def Qp.m_closed Qp.nat_mult_closed Qp.one_closed Qp.r_distr Qp_char_0 
          Zp_def field_inv(2) inc_closed local.fract_cancel_right not_nonzero_Qp not_numeral_le_zero
          padic_fields.inv_in_frac(1) padic_fields_axioms s_def)
    hence F11: "(\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =[k]\<cdot>\<one> \<otimes> (\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      by blast
    hence F12: "(inv ([k]\<cdot>\<one>)) \<otimes> (\<eta> x [^]k \<ominus> c[^]k \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =(\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      using DL_2_4_0 by (metis (no_types, lifting) Q\<^sub>p_def Qp.add.m_closed Qp.inv_cancelR(2) 
          Qp.m_closed Qp.m_comm Qp.nat_inc_closed Qp.one_closed Units_eq_nonzero Z\<^sub>p_def inc_closed
          not_nonzero_Qp not_numeral_le_zero padic_fields.Qp_char_0 padic_fields.inv_in_frac(1) padic_fields_axioms s_def)
    hence F13: "(\<eta> x [^]k \<ominus> c[^]k) \<otimes> ((inv ([k]\<cdot>\<one>)) \<div> (c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =(\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      by (smt DL_2_4_0 False Q\<^sub>p_def Qp.Units_inv_closed Qp.integral Qp.m_lcomm Qp.minus_closed 
          Qp.nat_inc_closed Qp.nat_pow_closed Qp.nonzero_closed Qp.nonzero_mult_closed 
          Qp.not_eq_diff_nonzero Qp_nat_pow_nonzero Units_eq_nonzero Z\<^sub>p_def \<eta>_closed assms(4)
          assms(5) not_numeral_le_zero padic_fields.Qp_char_0 padic_fields.inv_in_frac(1) padic_fields_axioms)
    hence F14: "(\<eta> x [^]k \<ominus> c[^]k \<div> (([k]\<cdot>\<one>)\<otimes>c[^](k-1)\<otimes>(\<eta> x \<ominus> c))) =(\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      using DL_2_4_0 Qp.inv_of_prod[of "[k]\<cdot>\<one>" "c[^](k-1)\<otimes>(\<eta> x \<ominus> c)"] 
      by (metis False Q\<^sub>p_def Qp.Units_m_closed Qp.Units_pow_closed Qp.m_assoc Qp.nat_inc_closed 
          Qp.nonzero_closed Qp.not_eq_diff_nonzero Units_eq_nonzero Z\<^sub>p_def \<eta>_closed assms(4) 
          assms(5) not_nonzero_Qp not_numeral_le_zero padic_fields.Qp_char_0 padic_fields_axioms)
    have F15: "val (\<iota> s \<div> [k]\<cdot>\<one>) = val (\<iota> s) - e"
      unfolding e_def by (metis DL_2_4_0 Q\<^sub>p_def Qp.nat_inc_closed Zp_def e_def e_eq inc_closed
          neq0_conv not_nonzero_Qp not_numeral_le_zero padic_fields.Qp_char_0 padic_fields_axioms
          s_def val_fract val_ord_nat_inc)
    have F16: "val (\<iota> s) \<ge> e + eint N"
    proof-
      have "s (e+N) = 0"
        using s_def unfolding \<phi>_def using p_res_ring_zero by presburger
      hence "val_Zp s \<ge> e + N"
        using s_def eint_ord_code(3) eint_ord_simps(1) ord_Zp_def ord_Zp_geq val_Zp_def by presburger
      thus ?thesis 
        by (metis of_nat_add plus_eint_simps(1) s_def val_of_inc)
    qed
    have F17: "val (\<iota> s \<div> [k]\<cdot>\<one>) \<ge> N"
      unfolding F15 using F16 
      by (metis add_cancel_eint_geq eint.simps(3) eint_add_cancel_fact)       
    have F18: "\<eta> x \<ominus> c \<in> nonzero Q\<^sub>p"
      using False Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed assms(4) assms(5) by blast
    have F19: "\<eta> x [^]k \<ominus> c[^]k \<in> carrier Q\<^sub>p"
      by (meson Qp.minus_closed Qp.nat_pow_closed Qp.nonzero_closed \<eta>_closed assms(4) assms(5))
    have F20: "([k]\<cdot>\<one>)\<otimes>c[^](k-1) \<in> nonzero Q\<^sub>p"
    proof- 
      have 0: "\<And> a b. a \<in> nonzero Q\<^sub>p \<Longrightarrow> b \<in> nonzero Q\<^sub>p \<Longrightarrow> a \<otimes> b  \<in> nonzero Q\<^sub>p"
        by (metis Qp.integral_iff Qp.nonzero_memE(1) Qp.nonzero_memI Qp.nonzero_mult_closed)
      show ?thesis apply(intro 0 Qp.nat_pow_nonzero assms nat_inc_nonzero)
        using DL_2_4_0 by auto 
    qed
    hence F21: "(\<eta> x [^]k \<ominus> c[^]k \<div> (([k]\<cdot>\<one>)\<otimes>c[^](k-1))) =(\<eta> x \<ominus> c)\<otimes>(\<one> \<oplus> (\<iota> s \<div> [k]\<cdot>\<one>))"
      using F13 F17 F18 F19
      by (smt F14 Qp.l_one Qp.nonzero_closed Qp.one_closed fract_closed local.fract_cancel_right local.fract_mult nonzero_inverse_Qp) 
    have "pow_res n (\<xi>_1 x \<ominus> c [^] k \<div> [k] \<cdot> (c [^] (k - 1))) = pow_res n (\<eta> x \<ominus> c)"
      apply(rule equal_pow_res_criterion[of N _ _ _  "\<iota> s \<div> [k]\<cdot>\<one>"])
             apply (simp add: assms(1))
            apply (simp add: assms(2))
           using assms(3) apply blast
          apply (metis F19 F20 Qp.nat_pow_closed Qp.nonzero_closed \<eta>_pow assms(4) assms(5) fract_closed nat_add_pow_mult_assoc)
         using F18 Qp.nonzero_closed apply blast
        apply (metis DL_2_4_0 Qp.m_closed Qp.nat_inc_closed Qp_char_0 inc_closed inv_in_frac(1) not_numeral_le_zero s_def)
       apply (metis F21 Qp.nat_pow_closed Qp.nonzero_closed \<eta>_pow assms(4) assms(5) nat_add_pow_mult_assoc)
      using F17 by blast
    thus ?thesis 
      by blast
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>The Disjunction over iii) - vi)\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Lemma 2.4 is inferred by noting that the conditions in facts iii) to vi) form a semialgebraic
     partition of the set $carrier (\mathbb{Q}_p^{m+l})$. This section makes this semi-algebraic
     partition explicit. \<close>

context denef_lemma_2_4
begin

definition below_center_set where 
"below_center_set l (N::nat) c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (c x) - N }" 

lemma below_center_set_is_semialgebraic: 
  assumes "c \<in> carrier (SA (m + l))"
  shows "is_semialgebraic (m + l) (below_center_set l N c)"
proof-
  obtain g where g_def: "g = \<pp>[^]-N \<odot>\<^bsub>SA (m+l)\<^esub>c"
    by blast 
  have g_closed: "g \<in> carrier (SA (m+l))"
    using assms unfolding g_def by (meson DL_2_4_2 SA_smult_closed add_gr_0 p_intpow_closed(1))
  hence 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (g x) = val (c x) - N"
    unfolding g_def 
    using function_ring_car_closed SA_car_memE(2) SA_smult_formula assms p_intpow_closed(1) times_p_pow_neg_val by presburger
  hence 1: "below_center_set l N c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (g x)}"
    unfolding below_center_set_def 
    by (metis (no_types, lifting))
  show ?thesis unfolding 1 using g_closed fact_i' by blast   
qed

lemma below_center_set_closed:
  "below_center_set l N c \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
unfolding below_center_set_def by blast 

definition above_center_set where 
"above_center_set l (N::nat) c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (c x) + N }" 

lemma above_center_set_is_semialgebraic: 
  assumes "c \<in> carrier (SA (m + l))"
  shows "is_semialgebraic (m + l) (above_center_set l N c)"
proof-
  obtain g where g_def: "g = \<pp>[^]N \<odot>\<^bsub>SA (m+l)\<^esub>c"
    by blast 
  have g_closed: "g \<in> carrier (SA (m+l))"
    using assms unfolding g_def 
    by (meson DL_2_4_2 SA_smult_closed add_gr_0 p_natpow_closed(1))    
  hence 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (g x) = val (c x) + N"
    unfolding g_def 
    by (metis function_ring_car_closed SA_car_memE(2) SA_smult_formula assms int_pow_int p_natpow_closed(1) times_p_pow_val)
  hence 1: "above_center_set l N c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<ge> val (g x)}"
    unfolding above_center_set_def 
    by (metis (no_types, lifting))
  show ?thesis unfolding 1 using g_closed fact_i'_geq by blast   
qed

lemma above_center_set_closed: 
"above_center_set l N c \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  unfolding above_center_set_def by blast 

definition near_center_set where 
"near_center_set l (j::int) c  = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x) + j}" 

lemma near_center_set_is_semialgebraic: 
  assumes "c \<in> carrier (SA (m + l))"
  shows "is_semialgebraic (m + l) (near_center_set l j c)"
proof-
  obtain g where g_def: "g = \<pp>[^]j \<odot>\<^bsub>SA (m+l)\<^esub>c"
    by blast 
  have g_closed: "g \<in> carrier (SA (m+l))"
    using assms unfolding g_def 
    by (meson DL_2_4_2 SA_smult_closed add_gr_0 p_intpow_closed(1))    
  hence 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (g x) = val (c x) + j"
    unfolding g_def 
    using function_ring_car_closed SA_car_memE(2) SA_smult_formula assms p_intpow_closed(1) times_p_pow_val by presburger    
  hence 1: "near_center_set l j c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (g x)}"
    unfolding near_center_set_def 
    by (metis (no_types, lifting))
  show ?thesis unfolding 1 using g_closed fact_i'_eq by blast   
qed

lemma near_center_set_closed: 
"near_center_set l j c \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  unfolding near_center_set_def by blast 

definition at_center_set_eq_ac where 
"at_center_set_eq_ac l N c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x) \<and> ac (e+N) (\<eta> (take m x)) = ac (e+N) (c x) }" 

lemma at_center_set_eq_ac_is_semialgebraic:
  assumes "N > 0"
  assumes "c \<in> carrier (SA (m + l))"
  shows "is_semialgebraic (m + l) (at_center_set_eq_ac l N c)"
proof-
  obtain F where F_def: "F = (\<lambda>t.  {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x) \<and> 
                                      ac (e+N) (\<eta> (take m x)) = t \<and> ac (e+N) (c x) = t })"
    by blast
  have F_semialg: "\<And>t. t \<in> Units (Zp_res_ring (e+N)) \<Longrightarrow> is_semialgebraic (m+l) (F t)"
  proof- fix t assume A: "t \<in> Units (Zp_res_ring (e+N))"
    have 0: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x)}"
      using fact_i'_eq assms by blast 
    have 1: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<noteq> \<zero> \<and> ac (e+N) (c x) = t }"
    proof-
      have 10: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<noteq> \<zero> \<and> ac (e+N) (c x) = t } = c  \<inverse>\<^bsub>m+l\<^esub> ac_cong_set (e+N) t"
        unfolding ac_cong_set_def 
        by (smt Collect_cong function_ring_car_closed SA_car_memE(2) assms evimage_Collect_eq)
      have 11: "is_univ_semialgebraic (ac_cong_set (e+N) t)"
        using A ac_cong_set_is_univ_semialg[of "e+N" t] assms by blast
      thus ?thesis 
        using 10 A assms  evimage_is_semialg by presburger
    qed
    have 2: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e+N) (\<eta> (take m x)) = t }"
    proof-
      have 20: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac (e+N) (\<eta> x) = t}"
        using fact_ii assms A add_gr_0 by presburger
      have 21: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e+N) (\<eta> (take m x)) = t } = 
                    take m  \<inverse>\<^bsub>m+l\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac (e+N) (\<eta> x) = t}"
      proof
        show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ac (e + N) (\<eta> (take m x)) = t} \<subseteq> 
              take m \<inverse>\<^bsub>m + l\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac (e + N) (\<eta> x) = t}"
          unfolding evimage_def using take_closed[of m "m+l"] 
          by auto 
        show "take m \<inverse>\<^bsub>m + l\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac (e + N) (\<eta> x) = t} \<subseteq>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ac (e + N) (\<eta> (take m x)) = t}"
          unfolding evimage_def using take_closed[of m "m+l"] by blast
      qed
      show ?thesis unfolding 21 
        by(intro semialg_map_evimage_is_semialg[of _ m] take_is_semialg_map 20, auto)
    qed
    have 3: "F t = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x)} \<inter> 
                   {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<noteq> \<zero> \<and> ac (e+N) (c x) = t } \<inter>
                   {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e+N) (\<eta> (take m x)) = t }"
    proof
      show "F t
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (c x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). c x \<noteq> \<zero> \<and> ac (e + N) (c x) = t} \<inter>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ac (e + N) (\<eta> (take m x)) = t}"
      proof fix x assume A: "x \<in> F t"
        then have 30: "val (\<eta> (take m x)) = val (c x)"
          unfolding F_def by blast 
        have 31: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using A take_closed unfolding F_def by (metis (no_types, lifting) le_add1 mem_Collect_eq)
        hence "val (\<eta> (take m x)) \<noteq> \<infinity>"
          by (metis Qp.not_nonzero_memI Qp.zero_closed \<eta>_nonzero local.val_zero val_nonzero' val_ord)
        then have "c x \<noteq> \<zero>" using 30 
          by (metis local.val_zero)
        then show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (c x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). c x \<noteq> \<zero> \<and> ac (e + N) (c x) = t} \<inter>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ac (e + N) (\<eta> (take m x)) = t}"
          using A unfolding F_def by blast
      qed
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (c x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). c x \<noteq> \<zero> \<and> ac (e + N) (c x) = t} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ac (e + N) (\<eta> (take m x)) = t} \<subseteq> F t "
        unfolding F_def by blast 
    qed
    show "is_semialgebraic (m + l) (F t)"
      unfolding 3 using 0 1 2 intersection_is_semialg by blast
  qed
  have F_covers: "at_center_set_eq_ac l N c = \<Union> (F ` (Units (Zp_res_ring (e+N))))"
  proof
    show "\<Union> (F ` Units (residue_ring (p ^ (e + N)))) \<subseteq> at_center_set_eq_ac l N c"
      unfolding F_def at_center_set_eq_ac_def by (smt UN_iff mem_Collect_eq subsetI)
    show "at_center_set_eq_ac l N c \<subseteq> \<Union> (F ` Units (residue_ring (p ^ (e + N))))"
    proof fix x assume A: "x \<in> at_center_set_eq_ac l N c"
      then have "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        unfolding at_center_set_eq_ac_def using le_add1 local.take_closed by blast
      then have "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
        using \<eta>_nonzero by blast
      then have 0: "ac (e+N) (\<eta> (take m x)) \<in> Units (Zp_res_ring (e+N))"
        using ac_units add_gr_0 assms(1) by blast
      then have "x \<in> F (ac (e+N) (\<eta> (take m x)))"
        using A unfolding F_def 
        by (smt Q\<^sub>p_def Zp_def denef_lemma_2_4.at_center_set_eq_ac_def denef_lemma_2_4_axioms mem_Collect_eq)
      then show "x \<in> \<Union> (F ` Units (residue_ring (p ^ (e + N))))"
        using 0 by blast
    qed
  qed
  have "finite (Units (Zp_res_ring (e+N)))"
    by (metis add_eq_0_iff_both_eq_0 assms(1) nat_neq_iff prime residues.finite_Units residues_n)
  thus ?thesis
    using F_covers F_semialg 
          finite_union_is_semialgebraic[of "F ` (Units (Zp_res_ring (e+N)))" "m+l"] 
    by (metis finite_imageI image_subsetI is_semialgebraicE)
qed

lemma at_center_set_eq_ac_closed: 
"at_center_set_eq_ac l N c \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  unfolding at_center_set_eq_ac_def by blast 

definition at_center_set_diff_ac where 
"at_center_set_diff_ac l N c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x) \<and> ac (e+N) (\<eta> (take m x)) \<noteq> ac (e+N) (c x) }" 

lemma at_center_set_diff_ac_is_semialgebraic:
  assumes "N > 0"
  assumes "c \<in> carrier (SA (m + l))"
  shows "is_semialgebraic (m + l) (at_center_set_diff_ac l N c)"
proof-
  have 0: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x)}"
    using fact_i'_eq assms by blast 
  have 1: "at_center_set_diff_ac l N c = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) = val (c x)} - at_center_set_eq_ac l N c"
    unfolding at_center_set_diff_ac_def at_center_set_eq_ac_def by blast 
  then show ?thesis using 0 at_center_set_eq_ac_is_semialgebraic 
    using assms(1) assms(2) diff_is_semialgebraic by presburger
qed

lemma at_center_set_diff_ac_closed:
"at_center_set_diff_ac l N c \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  unfolding at_center_set_diff_ac_def by blast 

text\<open>The semialgebraic decomposition of the carrier set:\<close>
lemma carrier_decomp_around_center:
  assumes "N > 0"
  assumes "c \<in> carrier (SA (m + l))"
  shows "carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) = (below_center_set l N c) \<union> (above_center_set l N c) \<union> 
                        (at_center_set_eq_ac l N c) \<union> (at_center_set_diff_ac l N c) \<union>
                        (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)"
proof
  show "carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<subseteq> below_center_set l N c \<union> above_center_set l N c \<union>
                           at_center_set_eq_ac l N c \<union> at_center_set_diff_ac l N c \<union>
                          (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
    show "x \<in> below_center_set l N c \<union> above_center_set l N c \<union> at_center_set_eq_ac l N c \<union> at_center_set_diff_ac l N c \<union>
              (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)"
    proof(cases "x \<in> below_center_set l N c")
      case True
      then show ?thesis by blast 
    next
      case F0: False
      show ?thesis 
      proof(cases "x \<in> above_center_set l N c")
        case True
        then show ?thesis by blast 
      next
        case F1: False
        show ?thesis 
        proof(cases "x \<in> at_center_set_eq_ac l N c")
          case True
          then show ?thesis by blast 
        next
          case F2: False
          show ?thesis 
          proof(cases "x \<in> at_center_set_diff_ac l N c")
            case True
            then show ?thesis by blast 
          next
            case F3: False
            have 0: "val (\<eta> (take m x)) > val (c x) - N"
              using A F0 unfolding below_center_set_def 
              by (metis (no_types, lifting) mem_Collect_eq not_less)
            have 1: "val (\<eta> (take m x)) < val (c x) + N"
              using A F1 unfolding above_center_set_def 
              by (metis (no_types, lifting) mem_Collect_eq not_less)
            have 2: "val (c x) \<noteq>  \<infinity>"
              using 0 by (metis eint_ord_simps(6) idiff_infinity)
            then obtain n::int where n_def: "val (c x) = n"
              by (metis eint.exhaust)
            have 3: "val (\<eta> (take m x)) \<noteq> \<infinity>"
              using 1 by (metis eint_ord_simps(6))
            then obtain M::int where M_def: "val (\<eta> (take m x)) = M"
              by (metis eint.exhaust)
            obtain j::int where j_def: "j = M - n"
              by blast 
            have 4: "val (\<eta> (take m x)) = val (c x) + j"
              using 0 1 eint_add_cancel_fact unfolding M_def n_def 
              by (metis add.commute add_diff_assoc_eint eint_iless eint_minus_comm ex_val_less 
                  idiff_eint_eint idiff_infinity idiff_infinity_right j_def less_le_trans order_le_less order_less_irrefl)
            have 5: "val (\<eta> (take m x)) \<noteq> val (c x)"
              using A F3 F2 unfolding at_center_set_diff_ac_def at_center_set_eq_ac_def by blast 
            have 6: "j \<noteq> 0"
              using 4 5 by (metis add.right_neutral zero_eint_def)
            have 7: "M > n - N"
              using 0 unfolding M_def n_def by (metis eint_ord_simps(2) idiff_eint_eint)
            have 8: "M < n + N"
              using 1 unfolding M_def n_def by (metis eint_ord_simps(2) plus_eint_simps(1))
            hence 9: "j < N"
              unfolding j_def by presburger 
            have 10: "j > -N"
              using 7 unfolding j_def by presburger 
            have 9: "j \<in> {- int N + 1..- 1} \<union> {1..((int N) - 1)}"
              using 6 9 10 
              by (metis Un_iff add_neg_numeral_special(8) atLeastAtMost_iff 
                  atLeastPlusOneAtMost_greaterThanAtMost_int diff_add_cancel greaterThanAtMost_iff 
                  less_add_same_cancel2 linorder_neqE_linordered_idom zle_add1_eq_le)
            hence "x \<in> (\<Union>i\<in>{- int N + 1..- 1} \<union> {1..(int N)-1}. near_center_set l i c)"
              using A 4 unfolding near_center_set_def 
              by blast
            hence "x \<in> (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)"
              by blast
            thus "x \<in> below_center_set l N c \<union> above_center_set l N c \<union> at_center_set_eq_ac l N c \<union> at_center_set_diff_ac l N c \<union>
         (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)"
              by blast 
          qed
        qed
      qed
    qed
  qed
  show "below_center_set l N c \<union> above_center_set l N c \<union> at_center_set_eq_ac l N c \<union> at_center_set_diff_ac l N c \<union>
    (\<Union>i\<in>{- int N + 1..- 1}.  near_center_set l i c) \<union> (\<Union>i\<in>{1..int N - 1}. near_center_set l i c)
    \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
    unfolding below_center_set_def above_center_set_def at_center_set_eq_ac_def at_center_set_diff_ac_def 
      near_center_set_def by blast 
qed

text\<open>The carrier decomposition clearly induces similar partitions of any semialgebraic subset:\<close>
lemma decomp_around_center:
  assumes "N > 0"
  assumes "c \<in> carrier (SA (m + l))"
  assumes "S \<subseteq> carrier  (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  shows "S = (S \<inter> (below_center_set l N c)) \<union> (S \<inter>(above_center_set l N c)) \<union> 
                        (S \<inter>(at_center_set_eq_ac l N c)) \<union> (S \<inter>(at_center_set_diff_ac l N c)) \<union>
                        (\<Union>i\<in>{- N+1..-1}. S \<inter> near_center_set l i c) \<union>(\<Union>i\<in>{1..(int N)-1}. S \<inter> near_center_set l i c) "
  using assms carrier_decomp_around_center[of N c l]
  by blast 

text\<open>This lemma formalizes the structure of the main proof. One can check that a set is semialgebraic 
by checking that each piece of the above partition is semialgebraic:\<close>

lemma decomp_around_center_semialg_test:
  assumes "N > 0"
  assumes "c \<in> carrier (SA (m + l))"
  assumes "S \<subseteq> carrier  (Q\<^sub>p\<^bsup>m+l\<^esup>)"
  assumes "is_semialgebraic (m+l) (S \<inter> below_center_set l N c)" 
  assumes "is_semialgebraic (m+l) (S \<inter> above_center_set l N c)" 
  assumes "is_semialgebraic (m+l) (S \<inter> at_center_set_diff_ac l N c)" 
  assumes "is_semialgebraic (m+l) (S \<inter> at_center_set_eq_ac l N c)" 
  assumes "\<And>i. i\<in>{- N+1..-1} \<Longrightarrow> is_semialgebraic (m+l) (S \<inter> near_center_set l i c)" 
  assumes "\<And>i. i\<in>{1..(int N)-1} \<Longrightarrow> is_semialgebraic (m+l) (S \<inter> near_center_set l i c)" 
  shows "is_semialgebraic (m+l) S"
proof-
  have 0:"is_semialgebraic (m+l) (\<Union>i\<in>{- N+1..-1}. S \<inter> near_center_set l i c)"
  proof-
    have "finite ((\<lambda>i. S \<inter> near_center_set l i c) ` ({- int N + 1..- 1}))"
      by blast
    thus ?thesis 
      using finite_union_is_semialgebraic[of "(\<lambda>i. S \<inter> near_center_set l i c) ` ({- N+1..-1})" "m+l"]
            assms by (meson image_subsetI is_semialgebraicE)
  qed   
  have 1: "is_semialgebraic (m+l) (\<Union>i\<in>{1..(int N)-1}. S \<inter> near_center_set l i c)"
  proof-
    have "finite ((\<lambda>i. S \<inter> near_center_set l i c) ` ({1..(int N)-1}))"
      by blast
    thus ?thesis 
      using finite_union_is_semialgebraic[of "(\<lambda>i. S \<inter> near_center_set l i c) ` ({1..(int N)-1})" "m+l"]
            assms by (meson image_subsetI is_semialgebraicE)
  qed 
  thus ?thesis
    using 0 assms decomp_around_center[of N c l S] union_is_semialgebraic 
   by metis
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Finishing the Proof\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>This section compiles the data from the six facts proved in the prior section and derives the 
necessary lemmas to apply the proof template laid out in the lemma \texttt{SA\_fun\_test}. Denef's 
Lemma 2.4 is deduced from there.\<close>

lemma(in padic_fields) pow_res_pow:
  assumes "n > 0"
  assumes "k > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p" 
  assumes "pow_res n a = pow_res n b"
  shows "pow_res (n*k) (a[^]k) = pow_res (n*k) (b[^]k)"
proof- 
  obtain c where c_def: "c \<in> P_set n \<and> a = b \<otimes> c"
    using assms by (meson equal_pow_resE) 
  have c_closed: "c \<in> carrier Q\<^sub>p"
    using c_def 
    by (meson P_set_nonzero'(2)) 
  have c_nonzero: "c \<noteq> \<zero>"
    using c_def  P_set_nonzero' nonzero_memE by blast 
  hence 1: "c[^]k \<noteq> \<zero>"
    using c_closed 
    by (simp add: Qp.nonzero_pow_nonzero) 
  show ?thesis 
    apply(intro equal_pow_resI'[of _ _ "c[^]k"] 
              Qp.nat_pow_closed assms P_set_pow) 
    using c_def apply blast 
    apply (simp add: Qp.nat_pow_distrib c_def assms c_closed) 
    using assms by simp     
qed

lemma eta_pow_res_set_semialg:
  assumes "n > 0"
  assumes "b \<in> carrier Q\<^sub>p" 
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b}"
proof(cases "b = \<zero>")
  case True
  then have "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b} = {}"
    using \<eta>_nonzero pow_res_zero[of n] 
    by (smt Qp.not_nonzero_memI Qp.zero_closed assms(1) empty_Collect_eq pow_res_nonzero)
  then show ?thesis 
    using empty_is_semialgebraic by presburger
next
  case False
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using assms nth_power_fact' by blast
  obtain F where F_def: "F = (\<lambda>ps. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac N (\<eta> x) = fst ps \<and> ord (\<eta> x) mod n = snd ps})"
    by blast 
  have F_semialg: "\<And>ps. ps \<in> Units (Zp_res_ring N) \<times> {0..<int n} \<Longrightarrow> is_semialgebraic m (F ps)"
  proof- fix ps assume A: "ps \<in> Units (residue_ring (p ^ N)) \<times> {0..<int n}"
    then obtain s t where st_def: "s \<in> Units (Zp_res_ring N) \<and> t \<in> {0..< int n} \<and> ps = (s,t)"
      by blast 
    have 0: "fst ps = s"
      using st_def by (meson fstI)
    have 1: "snd ps = t"
      using st_def by (meson sndI)
    have 2: "F ps = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac N (\<eta> x) = s} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<eta> x) mod n = t}"
      unfolding F_def 0 1  by blast
    have 3: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ac N (\<eta> x) = s}"
      using fact_ii[of N s] st_def N_def by blast
    have 4: "is_semialgebraic m  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<eta> x) mod n = t}"
      using fact_i[of n t] assms(1) of_nat_0_less_iff by blast
    show "is_semialgebraic m (F ps)"
      unfolding 2  using 3 4 intersection_is_semialg by blast
  qed
  obtain S where S_def: "S = {ps \<in> Units (Zp_res_ring N) \<times> {0..<int n}. (\<exists>x \<in> F ps. pow_res n (\<eta> x) = pow_res n b) }"
    by blast 
  have F_covers: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b} = (\<Union> s \<in> S. F s)"
  proof show "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b} \<subseteq> \<Union> (F ` S)"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b}"
      obtain ps where ps_def: "ps = (ac N (\<eta> x), ord (\<eta> x) mod n)"
        by blast
      have 0: "ac N (\<eta> x) \<in> Units (residue_ring (p ^ N))"
        using A \<eta>_nonzero[of x] ac_units[of "\<eta> x" N] N_def by blast
      have 1: "ord (\<eta> x) mod n \<in> {..< int n}"
        by (meson assms(1) lessThan_iff of_nat_0_less_iff pos_mod_conj)
      have 2: "x \<in> F ps"
        using 0 1 unfolding ps_def 
        by (smt A fstI local.F_def mem_Collect_eq sndI)   
      have 3: "\<exists>x\<in>F ps. pow_res n (\<eta> x) = pow_res n b"
        using A 2 by blast
      have 4: "fst ps = (ac N (\<eta> x))"
        using fstI unfolding ps_def by metis  
      have 5: "snd ps = ord (\<eta> x) mod n"
        using sndI unfolding ps_def by metis  
      have 6: "ps \<in> Units (residue_ring (p ^ N)) \<times> {0..<int n}"
        using 1 2 SigmaI unfolding ps_def 
        by (metis "0" assms(1) atLeastLessThan_iff of_nat_0_less_iff pos_mod_conj)        
      have "ps \<in> S"
        using 3 6 unfolding S_def by blast 
      thus "x \<in> \<Union> (F ` S)"
        using "2" by blast
    qed
    show "\<Union> (F ` S) \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b}"
    proof fix x assume A: "x \<in> \<Union> (F ` S)"
      then obtain ps where ps_def: "ps \<in> S \<and> x \<in> F ps" by blast 
      then obtain s t where st_def: "ps = (s,t) \<and> s \<in> Units (Zp_res_ring N) \<and> t \<in> {0..<int n}"
        unfolding S_def by blast    
      have 0: "\<And>y. y \<in> F ps \<Longrightarrow> pow_res n (\<eta> x) = pow_res n (\<eta> y)"
      proof- fix y assume A0: "y \<in> F ps"
        show "pow_res n (\<eta> x) = pow_res n (\<eta> y)"
          apply(rule fact_iii''[of N])
                apply (simp add: N_def)
               apply (simp add: assms(1))
              using N_def apply blast
             using A unfolding F_def apply blast
            using A0 unfolding F_def apply blast 
           using ps_def A0 st_def unfolding F_def apply (metis (mono_tags, lifting) mem_Collect_eq)
          using ps_def A0 st_def unfolding F_def by(metis (mono_tags, lifting) mem_Collect_eq)
      qed
      obtain y where y_def: "y \<in> F ps \<and> pow_res n (\<eta> y) = pow_res n b"
        using ps_def unfolding S_def by blast
      hence "pow_res n (\<eta> x) = pow_res n b"
        using 0 y_def by blast
      thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). pow_res n (\<eta> x) = pow_res n b}"
        using A unfolding F_def by blast 
    qed
  qed
  have finite: "finite (Units (Zp_res_ring N) \<times> {0..<int n})"
    using residues.finite_Units[of ] p_residues[of N] N_def by blast
  show ?thesis 
    unfolding F_covers apply(rule finite_union_is_semialgebraic'')
    unfolding S_def using finite apply (metis (no_types, lifting) S_def finite_subset mem_Collect_eq subsetI)
    using F_semialg by blast
qed    

lemma(in padic_fields) semialg_take_fact:
  assumes "m > 0"
  assumes "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). P x}"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). P (take m x)}"
proof-
  have "take m  \<inverse>\<^bsub>m+l\<^esub>{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). P x} =  {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). P (take m x)}"
    using assms 
    by (smt Collect_cong evimage_Collect_eq le0 le_add_same_cancel1 local.take_closed)
  thus ?thesis using assms 
    by (metis (no_types, lifting) add_gr_0 le_add1 semialg_map_evimage_is_semialg take_is_semialg_map)
qed

lemma eta_pow_res_set_semialg':
  assumes "n > 0"
  assumes "b \<in> carrier Q\<^sub>p" 
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (\<eta> (take m x)) = pow_res n b}"
  apply(rule semialg_take_fact) 
  apply (simp add: DL_2_4_2) using assms eta_pow_res_set_semialg by blast 

lemma eta_minus_c_pow_res_set_semialg:
  assumes "n > 0"
  assumes "c \<in> carrier (SA (m+l))"
  assumes "b \<in> carrier Q\<^sub>p" 
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (\<eta> (take m x) \<ominus> c x) \<in>  pow_res n b}"
proof-
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b}"
    by blast 
  have trans_closed: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> (\<eta> (take m x) \<ominus> c x) \<in> carrier Q\<^sub>p"
  proof(intro Qp.ring_simprules)
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
    have 0: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A take_closed by (meson le_add1)      
    show "\<eta> (take m x)\<in> carrier Q\<^sub>p"
      by(intro \<eta>_closed 0) 
    show "c x \<in> carrier Q\<^sub>p"
      by(intro SA_car_closed[of _ "m+l"] A assms)
  qed
  have S_eq: "S =  {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (\<eta> (take m x) \<ominus> c x) \<in>  pow_res n b}"
    unfolding S_def 
    by(intro equivalent_pow_res_sets[of _ "(\<lambda> x. (\<eta> (take m x) \<ominus> c x))"] assms trans_closed, auto)
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using assms(1) nth_power_fact' by blast
  have "is_semialgebraic (m+l) S" 
  proof(rule decomp_around_center_semialg_test[of N c])
    show " 0 < N"
      using N_def by blast 
    show "c \<in> carrier (SA (m + l))"
      using assms by blast 
    show "S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
      unfolding S_def by blast 
    show "is_semialgebraic (m + l) (S \<inter> below_center_set l N c)"
    proof-
      have bcsE: "\<And>x . x \<in> below_center_set l N c \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N"
      proof- fix x assume "x \<in> below_center_set l N c"
        show "val (\<eta> (take m x)) \<le> val (c x) - eint (int N)"
        proof-
          show "val (\<eta> (take m x)) \<le> val (c x) - eint (int N)"
            using \<open>x \<in> below_center_set l N c\<close> below_center_set_def by blast
      qed
      qed      
      have bcsI: "\<And>x . x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N \<Longrightarrow> 
                       x \<in> below_center_set l N c"
        unfolding below_center_set_def by blast
      obtain T where T_def: "T = S \<inter> below_center_set l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N"
        unfolding assms using T_def S_def apply blast
          using T_def S_def apply blast
           using T_def bcsE by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N
                      \<Longrightarrow> x \<in> T"
           unfolding T_def using S_def bcsI by blast
         have 0: "\<And>x. x \<in> below_center_set l N c \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> (c x)) = pow_res n (\<eta> (take m x))"
         proof- fix x assume A: "x \<in> below_center_set l N c" 
           show "pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n (\<eta> (take m x))"
             apply(rule fact_iii'[of N]) 
                  apply (simp add: \<open>0 < N\<close>)
                using assms(1)  apply simp 
               using N_def assms(1) apply linarith
              using A below_center_set_closed le_add1 local.take_closed apply blast
             using A function_ring_car_closed SA_car_memE(2) assms(2) below_center_set_closed apply blast
         by (metis (mono_tags, lifting) A below_center_set_def comm_monoid_add_class.add_0 eint_minus_comm idiff_0 mem_Collect_eq)
         qed
         have 1: "\<And>x. x \<in> below_center_set l N c \<Longrightarrow> pow_res n (\<eta> (take m x)) = pow_res n b \<Longrightarrow> x \<in> T"
         proof- fix x assume A0: "x \<in> below_center_set l N c" assume A1: "pow_res n (\<eta> (take m x)) = pow_res n b"
           show "x \<in> T"
             apply(rule T_memI)
               apply (metis (no_types, lifting) A0 add.commute below_center_set_def mem_Collect_eq)
                using 0[of x] A0 unfolding A1 apply blast 
                 using A0 bcsE by blast
         qed
         have 2: "T = below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (\<eta> (take m x)) = pow_res n b}"
         proof
           show "T \<subseteq> below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n (\<eta> (take m x)) = pow_res n b}"
             by (smt "0" Int_Collect T_memE(1) T_memE(2) T_memE(3) bcsI subsetI)
           show "below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n (\<eta> (take m x)) = pow_res n b} \<subseteq> T"
             using "1" by blast
         qed
         have "is_semialgebraic (m+l)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (\<eta> (take m x)) = pow_res n b}"
           using eta_pow_res_set_semialg'[of n b] assms(1) assms(3) by blast
         thus ?thesis using 2 unfolding T_def 
           using assms(2) below_center_set_is_semialgebraic intersection_is_semialg by presburger
    qed
    show "is_semialgebraic (m + l) (S \<inter> above_center_set l N c)"
    proof-
      have acsE: "\<And>x . x \<in> above_center_set l N c \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N"
      proof- fix x assume "x \<in> above_center_set l N c"
        thus "val (\<eta> (take m x)) \<ge> val (c x) + eint (int N)"
            using  above_center_set_def by blast
      qed      
      have acsI: "\<And>x . x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N \<Longrightarrow> 
                       x \<in> above_center_set l N c"
        unfolding above_center_set_def by blast
      obtain T where T_def: "T = S \<inter> above_center_set l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N"
        unfolding assms using T_def S_def apply blast
          using T_def S_def apply blast
           using T_def acsE by blast
         have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N
                      \<Longrightarrow> x \<in> T"
           unfolding T_def using S_def acsI by blast
         have 0: "\<And>x. x \<in> above_center_set l N c \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> (c x)) = pow_res n (\<ominus>(c x))"
         proof- fix x assume A: "x \<in> above_center_set l N c" 
           show "pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n (\<ominus>(c x))" 
             apply(rule fact_iii[of N]) 
                  apply (simp add: \<open>0 < N\<close>)
                using assms(1)  apply simp 
               using N_def assms(1) apply linarith
              using take_closed' A DL_2_4_2 unfolding above_center_set_def apply blast                          
             using A function_ring_car_closed SA_car_memE(2) assms(2) above_center_set_closed apply blast
            by (metis A acsE add.commute)
         qed
         have 1: "\<And>x. x \<in> above_center_set l N c \<Longrightarrow> pow_res n (\<ominus> c x) = pow_res n b \<Longrightarrow> x \<in> T"
         proof- fix x assume A0: "x \<in> above_center_set l N c" assume A1: "pow_res n (\<ominus> c x) = pow_res n b"
           show "x \<in> T"
             apply(rule T_memI)
             using A0 unfolding above_center_set_def apply blast 
              using A0 0[of x] A1 apply blast 
                using A0 acsE by blast
         qed
         have 2: "T = above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n ((\<ominus>\<^bsub>SA (m+l)\<^esub> c) x) = pow_res n b}"
         proof
           show "T \<subseteq> above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n ((\<ominus>\<^bsub>SA (m+l)\<^esub> c) x) = pow_res n b}"
             by (smt "0" DL_2_4_2 Int_Collect SA_a_inv_eval T_memE(1) T_memE(2) T_memE(3) acsI add_gr_0 assms(2) subsetI)            
           show "above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n ((\<ominus>\<^bsub>SA (m+l)\<^esub> c) x) = pow_res n b} \<subseteq> T"
             using "1" by (smt DL_2_4_2 Int_Collect SA_a_inv_eval add_gr_0 assms(2) subsetI)            
         qed
         have 3: "is_semialgebraic (m+l)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n ((\<ominus>\<^bsub>SA (m+l)\<^esub> c) x) = pow_res n b}"
         proof-
           have "\<ominus>\<^bsub>SA (m+l)\<^esub> c \<in> carrier (SA (m+l))"
             by (meson DL_2_4_2 add_gr_0 assms(2) cring.cring_simprules(3) padic_fields.SA_is_cring padic_fields_axioms)
           thus ?thesis 
             using pow_res_eq_rel evimage_is_semialg[of "\<ominus>\<^bsub>SA (m+l)\<^esub> c" "m+l" "pow_res n b"]
             by (smt Collect_cong function_ring_car_closed SA_car_memE(2) assms(1) assms(3) evimage_Collect_eq pow_res_is_univ_semialgebraic')
         qed
         thus ?thesis using 2 unfolding T_def 
           using above_center_set_is_semialgebraic assms(2) intersection_is_semialg by presburger
    qed
    show "is_semialgebraic (m + l) (S \<inter> at_center_set_diff_ac l N c)"
    proof-
      have acdaE: "\<And>x. x \<in> at_center_set_diff_ac l N c \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                  "\<And>x. x \<in> at_center_set_diff_ac l N c \<Longrightarrow> ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x)"
        unfolding at_center_set_diff_ac_def apply blast 
        unfolding at_center_set_diff_ac_def by blast 
      have  acdaI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) \<Longrightarrow>
               ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x) \<Longrightarrow> x \<in> at_center_set_diff_ac l N c"
        unfolding at_center_set_diff_ac_def by blast 
      obtain T where T_def: "T = S \<inter> at_center_set_diff_ac l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                   "\<And>x. x \<in> T \<Longrightarrow> ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x)"
        unfolding T_def assms at_center_set_diff_ac_def S_def
           apply blast apply blast apply blast by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) \<Longrightarrow> 
            ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x) \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> x \<in> T"
        unfolding T_def assms at_center_set_diff_ac_def  S_def by blast 
      obtain F where F_def: "F = (\<lambda> (i,s,t). at_center_set_diff_ac l N c \<inter> 
                                           {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = i \<and> 
                                                                    ac (e+2*N) (c x) = s \<and> ac (e + 2*N) (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> ps \<in> {0..< int n}\<times>Units (Zp_res_ring (e+2*N)) \<times> Units (Zp_res_ring (e+2*N)). T \<inter> F ps)"
      proof
        show "T \<subseteq> (\<Union>ps\<in>{0..<int n} \<times> Units (residue_ring (p ^ (e + 2 * N))) \<times> Units (residue_ring (p ^ (e + 2 * N))). T \<inter> F ps)"
        proof fix x assume A: "x \<in> T "
          then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding T_def assms  S_def by blast 
          have etax_closed: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
            using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
          have cx_closed: "c x \<in> nonzero Q\<^sub>p"
            using etax_closed assms A T_memE 
            by (metis (no_types, lifting) function_ring_car_closed Qp.nonzero_closed SA_car_memE(2) not_nonzero_Qp order_le_less val_ineq)
          obtain i where i_def: "i = ord (c x) mod n" by blast
          obtain s where s_def: "s = ac (e+2*N) (c x)" by blast 
          obtain t where t_def: "t = ac (e+2*N) (\<eta> (take m x))" by blast 
          have 0: "i \<in> {0..< int n }"
            unfolding  i_def by (meson assms(1) atLeastLessThan_iff of_nat_0_less_iff pos_mod_conj)
          have 1: "s \<in> Units (Zp_res_ring (e+2*N))"
            unfolding s_def using cx_closed 
            by (metis \<open>0 < N\<close> ac_units add_gr_0 mult_2)
          have 2: "t \<in> Units (Zp_res_ring (e+2*N))"
            unfolding t_def using etax_closed 
            by (metis \<open>0 < N\<close> ac_units add_gr_0 mult_2)
          have 3: "(i,s,t) \<in>  {0..< int n}\<times>Units (Zp_res_ring (e+2*N)) \<times> Units (Zp_res_ring (e+2*N))"
            using 0 1 2 
            by blast
          have  4: "x \<in> at_center_set_diff_ac l N c"
            using A T_def by blast
          have "F (i,s,t) =  at_center_set_diff_ac l N c \<inter>
            {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>).
             c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = i \<and> ac (e + 2 * N) (c x) = s \<and> ac (e + 2 * N) (\<eta> (take m x)) = t}"
            unfolding F_def by blast 
          hence 5: "x \<in> F (i,s,t)"
            unfolding i_def s_def t_def using 4 x_closed cx_closed by blast
          show "x \<in> (\<Union>ps\<in>{0..<int n} \<times> Units (residue_ring (p ^ (e + 2 * N))) \<times> Units (residue_ring (p ^ (e + 2 * N))). T \<inter> F ps)"
            using 3 i_def s_def t_def A 5 by blast
        qed   
        show "(\<Union>ps\<in>{0..<int n} \<times> Units (residue_ring (p ^ (e + 2 * N))) \<times> Units (residue_ring (p ^ (e + 2 * N))). T \<inter> F ps) \<subseteq> T"
          by blast 
      qed
      have F_semialg: "\<And>ps. ps \<in> {0..< int n}\<times>Units (Zp_res_ring (e+2*N)) \<times> Units (Zp_res_ring (e+2*N))
                  \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
      proof- fix ps assume A: "ps \<in> {0..< int n}\<times>Units (Zp_res_ring (e+2*N)) \<times> Units (Zp_res_ring (e+2*N))"
        show "is_semialgebraic (m+l) (T \<inter> F ps)"
        proof(cases "T \<inter> F ps = {}")
          case True
          then show ?thesis 
            by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F ps"
            by blast
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using x_def unfolding T_def  S_def assms by blast 
          have x_in_acda: "x \<in> at_center_set_diff_ac l N c"
            using x_def unfolding T_def by blast 
          have F0: "\<And>y. y \<in> F ps \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> c y) = pow_res n (\<eta> (take m x) \<ominus> c x)"
          proof- fix y assume A0: " y \<in> F ps"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def by blast 
            have y_in_acda: "y \<in> at_center_set_diff_ac l N c"
              using A0 unfolding F_def by blast 
            obtain i s t where ist_def: "ps = (i,s,t)"
              using A0 prod_cases3 by blast
            have F_alt_def: "F ps = at_center_set_diff_ac l N c \<inter>
            {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>).
             c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = i \<and> ac (e + 2 * N) (c x) = s \<and> ac (e + 2 * N) (\<eta> (take m x)) = t}"
              using ist_def unfolding F_def by blast 
            show "pow_res n (\<eta> (take m y) \<ominus> c y) = pow_res n (\<eta> (take m x) \<ominus> c x)"
              apply(rule fact_v'[of N])
              using \<open>0 < N\<close> apply auto[1]
                          apply (simp add: assms(1))
              using N_def apply blast
              using y_closed take_closed' 
              using DL_2_4_2 apply blast
              using function_ring_car_closed SA_car_memE(2) assms(2) y_closed A0 F_alt_def apply blast              
              using denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms take_closed' x_closed apply blast
              using x_def function_ring_car_closed SA_car_memE(2) assms(2) x_closed unfolding F_alt_def apply blast
              apply (metis (no_types, lifting) Qp.nonzero_memE(2) Qp.zero_closed acdaE(1) eint.inject padic_fields.val_def padic_fields_axioms val_nonzero' y_in_acda)
              apply (metis (no_types, lifting) Qp.nonzero_memE(2) Qp.zero_closed acdaE(1) eint.inject padic_fields.val_def padic_fields_axioms val_nonzero' x_in_acda)
              using acdaE(2) y_in_acda apply blast
              using acdaE(2) x_in_acda apply blast
              using A0 x_def unfolding F_alt_def  apply (metis (mono_tags, lifting) IntE Int_Collect)
              using A0 x_def unfolding F_alt_def  apply (metis (mono_tags, lifting) IntE Int_Collect)
              using A0 x_def unfolding F_alt_def  by (metis (mono_tags, lifting) IntE Int_Collect)
          qed
          have F1: "pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
            using x_def T_memE by blast 
          have F2: "\<And>y. y \<in> F ps \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> c y) = pow_res n b"
            using F0 unfolding F1 by blast                                                                            
          have F3: "F ps \<subseteq> T"
          proof fix x assume "x \<in> F ps" 
            obtain i s t where ist_def: "ps = (i,s,t)"
              using prod_cases3 by blast
            have F30: "F ps = at_center_set_diff_ac l N c \<inter> 
                                           {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = i \<and> 
                                                                    ac (e+2*N) (c x) = s \<and> ac (e + 2*N) (\<eta> (take m x)) = t}"
              unfolding ist_def F_def by blast
            show "x \<in> T"
              apply(rule T_memI) 
              using \<open>x \<in> F ps\<close> local.F_def apply blast
              using F30 \<open>x \<in> F ps\<close> acdaE(1) apply blast
              apply (metis (no_types, lifting) F30 IntE \<open>x \<in> F ps\<close> acdaE(2))
              using F2 \<open>x \<in> F ps\<close> by blast
          qed 
          hence "F ps = F ps \<inter> T"  by blast 
          have F4: "is_semialgebraic (m+l) (F ps)"
          proof-
            obtain i s t where ist_def: "ps = (i,s,t)"
              using prod_cases3 by blast
            have F40: "F ps = at_center_set_diff_ac l N c \<inter> 
                                           {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = i \<and> 
                                                                    ac (e+2*N) (c x) = s \<and> ac (e + 2*N) (\<eta> (take m x)) = t}"
              unfolding ist_def F_def by blast
            have F41: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = i}"
              using assms ord_congruence_set_SA_function[of n c m l i] DL_2_4_2 by linarith
            have F42: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> ac (e+2*N) (c x) = s}"
              using assms ac_cong_set_SA[of "e+2*N" s c m l] ist_def A 
              by (metis (no_types, lifting) DL_2_4_2 \<open>0 < N\<close> add_is_0 gr0I mem_Sigma_iff mult_is_0 of_nat_0 of_nat_zero_less_power_iff zero_power2)
            have F43: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e + 2*N) (\<eta> (take m x)) = t}"
              using assms fact_ii'[of "e+2*N" t l] ist_def A 
              by (smt DL_2_4_2 F40 IntE Int_Collect \<eta>_nonzero \<open>0 < N\<close> ac_units add_is_0 gr0I mult_is_0 of_nat_0 of_nat_zero_less_power_iff take_closed' x_def zero_power2)
            have "F ps =   at_center_set_diff_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = i} \<inter>
                                                          {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> ac (e+2*N) (c x) = s} \<inter>
                                                            {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e + 2*N) (\<eta> (take m x)) = t}"
              unfolding F40 by blast 
            thus ?thesis using intersection_is_semialg  F40 F41 F42 F43 
              by (metis (no_types, lifting) \<open>0 < N\<close> assms(2) at_center_set_diff_ac_is_semialgebraic)
          qed 
          then show ?thesis 
            by (simp add: F3 Int_absorb1)        
        qed
      qed
      have F_finite: "finite ((\<lambda>ps. T \<inter> F ps) ` ({0..<int n} \<times> Units (residue_ring (p ^ (e + 2 * N))) \<times> Units (residue_ring (p ^ (e + 2 * N)))))"
      proof-
        have 0: "finite (Units (residue_ring (p ^ (e + 2 * N))))"
          using residues.finite_Units[of "e+2*N"] 
          by (metis \<open>0 < N\<close> add_eq_0_iff_both_eq_0 mult_is_0 nat_neq_iff padic_fields.prime padic_fields_axioms residues.finite_Units residues_n zero_neq_numeral)
        have 1: "finite {0..<int n}" by blast
        show ?thesis using 0 1 by blast
      qed
      then have "is_semialgebraic (m + l) T"
        using F_covers finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps) `( {0..< int n}\<times>Units (Zp_res_ring (e+2*N)) \<times> Units (Zp_res_ring (e+2*N)))" "m+l"]
              F_semialg  by (metis image_subsetI is_semialgebraicE)
      thus ?thesis unfolding T_def by blast 
    qed
    show "is_semialgebraic (m + l) (S \<inter> at_center_set_eq_ac l N c)"
    proof-
      have aceaE: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                  "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x)"
        unfolding at_center_set_eq_ac_def apply blast 
        unfolding at_center_set_eq_ac_def by blast 
      have  aceaI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) \<Longrightarrow>
               ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x) \<Longrightarrow> x \<in> at_center_set_eq_ac l N c"
        unfolding at_center_set_eq_ac_def by blast 
      obtain T where T_def: "T = S \<inter> at_center_set_eq_ac l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                   "\<And>x. x \<in> T \<Longrightarrow> ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x)"                   
        unfolding T_def assms at_center_set_eq_ac_def  S_def 
           apply blast apply blast apply blast by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) \<Longrightarrow> 
            ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x) \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> x \<in> T"
        unfolding T_def  S_def assms at_center_set_eq_ac_def mem_Collect_eq by blast 
      obtain g where g_def: "g = ((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k)
                                   \<otimes>\<^bsub>SA (m+l)\<^esub> one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1)))"
        by blast 
      have "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> c x \<noteq>  \<zero>"
        by (metis (no_types, lifting) DL_2_4_2 Qp.not_nonzero_memI Qp.zero_closed \<eta>_nonzero aceaE(1) add.right_neutral at_center_set_eq_ac_closed eint_diff_imp_eint subsetD take_closed' zero_eint_def)
      hence P0: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1))) x = inv ([k]\<cdot>((c x)[^](k-1)))"
        using assms by (smt DL_2_4_0 DL_2_4_2 function_ring_car_closed Qp.nonzero_pow_nonzero 
            SA_car_memE(2) SA_nat_pow add_gr_0 at_center_set_eq_ac_closed gr0I not_numeral_le_zero
            one_over_fun_add_pow_eval padic_fields.SA_car_memE(1) padic_fields.SA_nat_pow_closed padic_fields_axioms subsetD)        
      have P1: "(fun_inc (m+l) m \<xi>_1) \<in> carrier (SA (m+l))"
        by (meson \<xi>_1_characterization denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms fun_inc_closed le_iff_add)
      have P2: "c [^]\<^bsub>SA (m+l)\<^esub> k \<in> carrier (SA (m+l))"
        by (meson SA_imp_semialg SA_nat_pow_closed add_gr_0 assms(2) denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms)
      have P3: "one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1))) \<in> carrier (SA (m+l))"
        by (meson DL_2_4_2 SA_add_pow_closed SA_nat_pow_closed add_strict_increasing assms(2) le0 one_over_fun_closed padic_fields.SA_imp_semialg padic_fields_axioms)        
      have P1_eval: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> (fun_inc (m+l) m \<xi>_1) x = \<xi>_1 (take m x)"
          using \<xi>_1_characterization assms fun_inc_eval[of x "m+l" m \<xi>_1] P1 
          by (meson at_center_set_eq_ac_closed fun_inc_eval subsetD)
      have P4:  "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> ((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k) x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k)"
      proof- fix x assume A: "x \<in> at_center_set_eq_ac l N c"
        hence x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
          using at_center_set_eq_ac_closed by blast
        thus "((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> (c [^]\<^bsub>SA (m+l)\<^esub> k)) x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k)"
          using \<xi>_1_characterization assms fun_inc_eval[of x "m+l" m \<xi>_1] P1 P2 P1_eval SA_minus_eval 
                 DL_2_4_2 SA_nat_pow add_gr_0 by presburger
      qed
      have P5: "(fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k \<in> carrier (SA (m+l))"
        using SA_minus_closed fun_inc_closed DL_2_4_2 P1 P2 add_gr_0 by presburger
      have g_eval: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> g x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k) \<otimes> inv ([k]\<cdot>((c x)[^](k-1)))"
        using P0 P3 P4 P5 aceaE
        by (smt SA_mult at_center_set_eq_ac_closed g_def subsetD)
      have  g_closed: "g \<in> carrier (SA (m+l))"
        using P3 P5 SA_imp_semialg add_gr_0 denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms g_def padic_fields.SA_mult_closed padic_fields_axioms by presburger
      have P6: "\<And>x . x \<in> at_center_set_eq_ac l N c \<Longrightarrow> pow_res n (\<eta> (take m x)\<ominus> c x) = pow_res n (g x)"
      proof- fix x assume A: "x \<in> at_center_set_eq_ac l N c"
        have P60: "c x \<in> nonzero Q\<^sub>p"
          using A unfolding at_center_set_eq_ac_def 
          by (metis (no_types, lifting) A function_ring_car_closed SA_car_memE(2) \<open>\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> c x \<noteq> \<zero>\<close> assms(2) mem_Collect_eq not_nonzero_Qp)
        have "pow_res n (\<eta> (take m x)\<ominus> c x) = pow_res n ((\<xi>_1 (take m x) \<ominus> (c x)[^]k) \<otimes> inv ([k]\<cdot>((c x)[^](k-1))))"
          apply(rule fact_vi(2)[of N])
          apply (simp add: \<open>0 < N\<close>) 
          apply (simp add: assms(1))
          using N_def apply blast
          using A at_center_set_eq_ac_def take_closed' DL_2_4_2 apply blast
          using P60 apply blast           
          apply (metis (no_types, lifting) A Qp.not_nonzero_memI Qp.zero_closed aceaE(1) eint.inject padic_fields.val_def padic_fields_axioms val_nonzero')
          using A aceaE(2) by blast
        thus "pow_res n (\<eta> (take m x)\<ominus> c x) = pow_res n (g x)" using A g_eval 
          by presburger
      qed
      have P7: "T = at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (g x) = pow_res n b}"
      proof
        show "T \<subseteq> at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n (g x) = pow_res n b}"
          apply(rule subsetI)
          using T_memE P6 by (smt Int_Collect aceaI)
        show " at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). pow_res n (g x) = pow_res n b} \<subseteq> T"
          apply(rule subsetI)
          using T_memI P6 by (smt Int_Collect aceaE(1) aceaE(2))
      qed
      have "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). pow_res n (g x) = pow_res n b}"
        using g_closed SA_pow_res_is_semialgebraic[of n  b  g "m+l"] DL_2_4_2 assms(1) assms(3) by blast
      thus ?thesis using P7 intersection_is_semialg 
        by (metis (no_types, lifting) T_def \<open>0 < N\<close> assms(2) at_center_set_eq_ac_is_semialgebraic)
    qed
    show "\<And>i. i \<in> {1..int N - 1} \<Longrightarrow> is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
    proof- fix i assume A: "i \<in> {1..int N - 1}"
      have ncsE: "\<And>x. x \<in> near_center_set l i c \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
        unfolding near_center_set_def by blast 
      have ncsI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> x \<in> near_center_set l i c"
        unfolding near_center_set_def by blast 
      obtain T where T_def: "T = S \<inter> near_center_set l i c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
                  "\<And>x. x \<in> T \<Longrightarrow> ord (\<eta> (take m x)) = ord (c x) + i"
        unfolding T_def assms near_center_set_def S_def apply blast apply blast apply blast
        by (smt function_ring_car_closed Int_Collect SA_car_memE(2) \<eta>_nonzero assms(2) eint.inject eint_diff_imp_eint le_add1 local.take_closed plus_eint_simps(1) val_ord)
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> 
                  pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> x \<in> T"
        unfolding  S_def T_def assms near_center_set_def by blast 
      obtain F where F_def: 
        "F = (\<lambda> (j, s, t). {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t))"
      proof
        show "T \<subseteq> (\<Union> (j, s, t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
        proof fix x assume A: "x \<in> T" 
          have 00: "c x \<in> nonzero Q\<^sub>p"
            using eint_diff_imp_eint[of "\<eta> (take m x)" "c x"] A 
            by (meson function_ring_car_closed SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(2) le_add1 local.take_closed)        
          have 0: "\<eta> (take m x) \<noteq> \<zero>"
            using A unfolding T_def near_center_set_def  
            using DL_2_4_2 Qp.nonzero_memE(2) \<eta>_nonzero take_closed' by blast
          hence 1: "c x \<in> nonzero Q\<^sub>p"
            using A unfolding T_def 
            by (metis (no_types, lifting) A DL_2_4_2 function_ring_car_closed SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(2) comm_monoid_add_class.add_0 eint_minus_comm idiff_infinity_right local.val_zero not_nonzero_Qp take_closed' val_nonzero' val_ord zero_eint_def)
          have 2: "ord (c x) mod n \<in> {0..< n}"
            by (meson assms(1) atLeastLessThan_iff of_nat_0_less_iff pos_mod_conj)
          have 3: "ac N (c x) \<in> Units (Zp_res_ring N)"
            using 1 \<open>0 < N\<close> ac_units by blast
          have 4: "ac N (\<eta> (take m x)) \<in> Units (Zp_res_ring N)"
            using 0 A unfolding T_def near_center_set_def 
            using DL_2_4_2 \<eta>_nonzero \<open>0 < N\<close> ac_units take_closed' by blast
          obtain tr where tr_def: "tr = (ord (c x) mod n, ac N (c x),  ac N (\<eta> (take m x)))"
            by blast 
          have 5: "tr \<in> {0..< n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)"
            using 2 3 4 unfolding tr_def by blast 
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using A T_memE(1) by blast
          hence  "x \<in> T \<inter> F tr"
            unfolding F_def tr_def using add.commute[of _  i]  00 A 5 T_memE by blast                    
          thus "x \<in> (\<Union>(j,s,t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
            using 5 by blast 
        qed
        show "(\<Union> (j, s, t) \<in> ({0..< int n }\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t)) \<subseteq> T"
          unfolding F_def by blast 
      qed
      have F_covers: "T = (\<Union> ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F ps)"
        using F_covers by blast 
      have finite: "finite ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
      proof-
        have "finite  (Units (Zp_res_ring N))"
          using \<open>0 < N\<close> p_residues residues.finite_Units by blast
        thus ?thesis by blast
      qed
      have F_semialg: "\<And>j s t . (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
      proof-
        fix j s t assume jst_def: "(j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
        show "is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
        proof(cases "T \<inter> F (j, s, t) = {}")
          case True
          then show ?thesis by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F (j, s, t)" by blast 
          hence x_in_F: "x \<in> F (j,s,t)" by blast 
          obtain a where a_def: "a = pow_res n (\<eta> (take m x) \<ominus> (c x))" by blast 
          have F0: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n (\<eta> (take m x) \<ominus> (c x))"
          proof- fix y assume A0: "y \<in> F (j, s, t)"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def T_def assms  by blast 
            have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using x_def unfolding F_def T_def assms  by blast 
            have 0: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
            have "c x \<in> carrier Q\<^sub>p" 
              using function_ring_car_closed SA_car_memE(2) assms(2) x_closed by blast
            hence 1: "c x \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE x_def 0 eint_diff_imp_eint[of "\<eta> (take m x)" "c x" i] unfolding F_def T_def near_center_set_def
              by blast       
            have 2: "\<eta> (take m y) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' y_closed by blast
            have 3: "c y \<in> carrier Q\<^sub>p"
              using function_ring_car_closed SA_car_memE(2) assms(2) y_closed by blast
            hence 4: "c y \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE  A0 2 eint_diff_imp_eint[of "\<eta> (take m y)" "c y" i]
              unfolding F_def T_def near_center_set_def  by blast
            have 5: "y \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using A0 unfolding F_def by blast 
            have 6: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using x_in_F unfolding F_def by blast 
              show "pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n (\<eta> (take m x) \<ominus> (c x))"
              apply(rule fact_iv[of N _ i])
                          apply (simp add: \<open>0 < N\<close>)
                         apply (simp add: assms(1))
                        using A apply blast
                       using N_def apply blast
                      using A0 take_closed'[of ] DL_2_4_2 y_closed apply blast 
                     using A0 assms(2) unfolding F_def  T_def near_center_set_def 
                     using function_ring_car_closed SA_car_memE(2) apply blast
                    using DL_2_4_2 take_closed' x_closed apply blast
                   using function_ring_car_closed SA_car_memE(2) assms(2) x_closed 1 apply blast           
                  using 5 6 unfolding mem_Collect_eq apply metis   
                 using 5 6 unfolding mem_Collect_eq apply metis   
                using 5 6 unfolding mem_Collect_eq apply metis   
               using 5 unfolding add.commute[of "ord (c y)" i]  mem_Collect_eq apply blast 
              using 6 unfolding add.commute[of "ord (c x)" i]  mem_Collect_eq by blast 
          qed
          have F1: "pow_res n b = a"
            using x_def T_memE[of x] unfolding a_def F_def by blast 
          hence F2: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n b"
            using F0 unfolding a_def by blast  
          have F3: "F (j,s,t) \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding F_def by blast 
          have F4: "F (j, s, t) \<subseteq> T "
          proof fix x assume A: "x \<in> F (j,s,t)" 
            have F5: "val (\<eta> (take m x)) = val (c x) + i"
            proof-
              have 00:  "ord (\<eta> (take m x)) = ord (c x) + i"
                using A unfolding F_def by blast 
              have 01: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
                using A DL_2_4_2 DL_2_4_4  unfolding F_def 
                using \<eta>_nonzero take_closed' by auto                
              have 02: "c x \<in> nonzero Q\<^sub>p"
                using A unfolding F_def by blast 
              then show ?thesis using 00 01  val_ord F3 plus_eint_simps(1) by presburger
            qed
            show "x \<in> T"
              apply(rule T_memI)
              using A F3 apply blast 
              using F5 apply blast
              using A F2 by blast 
          qed
          hence F5: "F (j, s, t) = T \<inter> F (j, s, t)"
            by blast 
          have F6: "is_semialgebraic (m+l) (F (j, s, t))"
          proof-
            obtain F0 where F0_def: "F0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>ord (\<eta> (take m x)) = ord (c x) + i }"
              by blast 
            obtain F1 where F1_def: "F1 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j}"
              by blast 
            obtain F2 where F2_def: "F2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ac N (c x) = s }"
              by blast
            obtain F3 where F3_def: "F3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>).  ac N (\<eta> (take m x)) = t }"
              by blast
            have 00: "is_semialgebraic (m+l) F0" 
              unfolding F0_def  using assms fact_i_take[of c l i] by blast
            have 01: "is_semialgebraic (m+l) F1"
              unfolding F1_def using assms ord_congruence_set_SA_function[of n c m l j] DL_2_4_2 by linarith
            have 02: "is_semialgebraic (m+l) F2"
              unfolding F2_def using assms ac_cong_set_SA[of N s c m l] jst_def \<open>0 < N\<close>
                    denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms by blast
            have 03: "is_semialgebraic (m+l) F3"
              unfolding F3_def using fact_ii'[of N t l] \<open>0 < N\<close> jst_def by blast
            have 04: "F (j,s,t) =  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              unfolding F_def by blast 
            have "F (j, s, t) = F0 \<inter>F1 \<inter> F2 \<inter>F3"
              unfolding 04 F0_def F1_def F2_def F3_def by blast 
            thus ?thesis using 00 01 02 03 intersection_is_semialg  
              by simp
          qed
          then show ?thesis using F5 by auto         
        qed
      qed
      have F_semialg: "\<And>ps . ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
        using F_semialg by blast
      show "is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
        using F_semialg finite F_covers 
              finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps)` ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))" "m+l" ]  
        by (metis T_def finite_imageI image_subsetI is_semialgebraicE)
    qed
    show "\<And>i. i \<in> {- (int N) + 1..-1} \<Longrightarrow> is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
    proof- fix i assume A: "i \<in> {- (int N) + 1..-1} "
      have ncsE: "\<And>x. x \<in> near_center_set l i c \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
        unfolding near_center_set_def by blast 
      have ncsI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> x \<in> near_center_set l i c"
        unfolding near_center_set_def by blast 
      obtain T where T_def: "T = S \<inter> near_center_set l i c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
                  "\<And>x. x \<in> T \<Longrightarrow> ord (\<eta> (take m x)) = ord (c x) + i"
        unfolding  S_def T_def assms near_center_set_def apply blast apply blast apply blast
        by (smt function_ring_car_closed Int_Collect SA_car_memE(2) \<eta>_nonzero assms(2) eint.inject eint_diff_imp_eint le_add1 local.take_closed plus_eint_simps(1) val_ord)
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> 
                  pow_res n (\<eta> (take m x) \<ominus> c x) = pow_res n b \<Longrightarrow> x \<in> T"
        unfolding  S_def T_def assms near_center_set_def by blast 
      obtain F where F_def: 
        "F = (\<lambda> (j, s, t). {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p \<and>  ord (\<eta> (take m x)) mod n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t))"
      proof
        show "T \<subseteq> (\<Union> (j, s, t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
        proof fix x assume A: "x \<in> T" 
          have 00: "c x \<in> nonzero Q\<^sub>p"
            using eint_diff_imp_eint[of "\<eta> (take m x)" "c x"] A 
            by (meson function_ring_car_closed SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(2) le_add1 local.take_closed)        
          have 0: "\<eta> (take m x) \<noteq> \<zero>"
            using A unfolding T_def near_center_set_def  
            using DL_2_4_2 Qp.nonzero_memE(2) \<eta>_nonzero take_closed' by blast
          hence 1: "c x \<in> nonzero Q\<^sub>p"
            using A unfolding T_def 
            by (metis (no_types, lifting) A DL_2_4_2 function_ring_car_closed SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(2) comm_monoid_add_class.add_0 eint_minus_comm idiff_infinity_right local.val_zero not_nonzero_Qp take_closed' val_nonzero' val_ord zero_eint_def)
          have 2: "ord (\<eta> (take m x)) mod n \<in> {0..< n}" 
            by (meson assms(1) atLeastLessThan_iff of_nat_0_less_iff pos_mod_conj)
          have 3: "ac N (c x) \<in> Units (Zp_res_ring N)"
            using 1 \<open>0 < N\<close> ac_units by blast
          have 4: "ac N (\<eta> (take m x)) \<in> Units (Zp_res_ring N)"
            using 0 A unfolding T_def near_center_set_def 
            using DL_2_4_2 \<eta>_nonzero \<open>0 < N\<close> ac_units take_closed' by blast
          obtain tr where tr_def: "tr = (ord (\<eta> (take m x)) mod n, ac N (c x),  ac N (\<eta> (take m x)))"
            by blast 
          have 5: "tr \<in> {0..< n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)"
            using 2 3 4 unfolding tr_def by blast             
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using A T_memE(1) by blast
          hence  "x \<in> T \<inter> F tr"
            unfolding F_def tr_def using add.commute[of _  i] 00 A 5 T_memE by blast                              
          thus "x \<in> (\<Union>(j,s,t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times> Units (Zp_res_ring N). T \<inter> F (j, s, t))"
            using 5 by blast 
        qed
        show "(\<Union> (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t)) \<subseteq> T"
          unfolding F_def by blast 
      qed
      have F_covers: "T = (\<Union> ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F ps)"
        using F_covers by blast 
      have finite: "finite ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
      proof-
        have "finite  (Units (Zp_res_ring N))"
          using \<open>0 < N\<close> p_residues residues.finite_Units by blast
        thus ?thesis by blast
      qed
      have F_semialg: "\<And>j s t . (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
      proof-
        fix j s t assume jst_def: "(j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
        show "is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
        proof(cases "T \<inter> F (j, s, t) = {}")
          case True
          then show ?thesis by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F (j, s, t)" by blast 
          hence x_in_F: "x \<in> F (j,s,t)" by blast 
          obtain a where a_def: "a = pow_res n (\<eta> (take m x) \<ominus> (c x))" by blast 
          have F0: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n (\<eta> (take m x) \<ominus> (c x))"
          proof- fix y assume A0: "y \<in> F (j, s, t)"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def T_def assms  by blast 
            have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using x_def unfolding F_def T_def assms  by blast 
            have 0: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
            have "c x \<in> carrier Q\<^sub>p" 
              using function_ring_car_closed SA_car_memE(2) assms(2) x_closed by blast
            hence 1: "c x \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE x_def 0 eint_diff_imp_eint[of "\<eta> (take m x)" "c x" i] unfolding F_def T_def near_center_set_def
              by blast       
            have 2: "\<eta> (take m y) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' y_closed by blast
            have 3: "c y \<in> carrier Q\<^sub>p"
              using function_ring_car_closed SA_car_memE(2) assms(2) y_closed by blast
            hence 4: "c y \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE  A0 2 eint_diff_imp_eint[of "\<eta> (take m y)" "c y" i]
              unfolding F_def T_def near_center_set_def  by blast
            have 5: "y \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using A0 unfolding F_def by blast 
            have 6: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using x_in_F unfolding F_def by blast 
              show "pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n (\<eta> (take m x) \<ominus> (c x))"
              apply(rule fact_iv'[of N _ i])
                          apply (simp add: \<open>0 < N\<close>)
                         apply (simp add: assms(1))
                        using A apply blast
                       using N_def apply blast
                      using A0 take_closed' DL_2_4_2 
                      unfolding F_def  T_def near_center_set_def apply blast 
                     using A0 assms(2) unfolding F_def  T_def near_center_set_def 
                     using function_ring_car_closed SA_car_memE(2) apply blast
                    using DL_2_4_2 take_closed' x_closed apply blast
                   using 1 apply blast 
                  using 5 6 unfolding mem_Collect_eq apply metis   
                 using 5 6 unfolding mem_Collect_eq apply metis   
                using 5 6 unfolding mem_Collect_eq apply metis   
               using 5 unfolding add.commute[of "ord (c y)" i]  mem_Collect_eq apply blast 
              using 6 unfolding add.commute[of "ord (c x)" i]  mem_Collect_eq by blast 
          qed
          have F1: "pow_res n b = a"
            using x_def T_memE[of x] unfolding a_def F_def by blast 
          hence F2: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> pow_res n (\<eta> (take m y) \<ominus> (c y)) = pow_res n b"
            using F0 unfolding a_def by blast  
          have F3: "F (j,s,t) \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding F_def by blast 
          have F4: "F (j, s, t) \<subseteq> T "
          proof fix x assume A: "x \<in> F (j,s,t)" 
            have F5: "val (\<eta> (take m x)) = val (c x) + i"
            proof-
              have 00:  "ord (\<eta> (take m x)) = ord (c x) + i"
                using A unfolding F_def by blast 
              have 01: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
                using A take_closed' DL_2_4_2 DL_2_4_4  unfolding F_def 
                using \<eta>_nonzero by blast
              have 02: "c x \<in> nonzero Q\<^sub>p"
                using A unfolding F_def by blast 
              then show ?thesis using 00 01  val_ord F3 plus_eint_simps(1) by presburger
            qed
            show "x \<in> T"
              apply(rule T_memI)
              using A F3 apply blast 
              using F5 apply blast
              using A F2 by blast 
          qed
          hence F5: "F (j, s, t) = T \<inter> F (j, s, t)"
            by blast 
          have F6: "is_semialgebraic (m+l) (F (j, s, t))"
          proof-
            obtain F0 where F0_def: "F0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) = ord (c x) + i }"
              by blast 
            obtain F1 where F1_def: "F1 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>).  ord (\<eta> (take m x)) mod n = j}"
              by blast 
            obtain F2 where F2_def: "F2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ac N (c x) = s }"
              by blast
            obtain F3 where F3_def: "F3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>).  ac N (\<eta> (take m x)) = t }"
              by blast
            have 00: "is_semialgebraic (m+l) F0"
              unfolding F0_def   using assms fact_i_take[of c l i] by blast 
            have 01: "is_semialgebraic (m+l) F1"
              unfolding F1_def using assms fact_i_take'[of n l j] by linarith              
            have 02: "is_semialgebraic (m+l) F2"
              unfolding F2_def using assms ac_cong_set_SA[of N s c m l] jst_def \<open>0 < N\<close>
                    denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms by blast
            have 03: "is_semialgebraic (m+l) F3"
              unfolding F3_def using fact_ii'[of N t l] \<open>0 < N\<close> jst_def by blast
            have 04: "F (j,s,t) =  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              unfolding F_def by blast 
            have "F (j, s, t) = F0 \<inter>F1 \<inter> F2 \<inter>F3"
              unfolding 04 F0_def F1_def F2_def F3_def by blast 
            thus ?thesis using 00 01 02 03 intersection_is_semialg  
              by simp
          qed
          then show ?thesis using F5 by auto         
        qed
      qed
      have F_semialg: "\<And>ps . ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
        using F_semialg by blast
      show "is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
        using F_semialg finite F_covers 
              finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps)` ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))" "m+l" ]  
        by (metis T_def finite_imageI image_subsetI is_semialgebraicE)
    qed
  qed
  thus ?thesis using S_eq by auto 
qed

lemma eta_ord_bound_set_semialg:
  assumes "c \<in> carrier (SA (m+l))"
  assumes "a \<in> carrier (SA (m+l))"
  shows "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)}"
proof-
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)}"
    by blast 
  obtain n::nat where n_def: "n > 0"
    by auto 
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using n_def nth_power_fact' by blast
  have "is_semialgebraic (m+l) S"
  proof(rule decomp_around_center_semialg_test[of N c])
    show " 0 < N"
      using N_def by blast 
    show "c \<in> carrier (SA (m + l))"
      using assms by blast 
    show "S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)"
      unfolding S_def by blast 
    show "is_semialgebraic (m + l) (S \<inter> below_center_set l N c)"
    proof-
      have bcsE: "\<And>x . x \<in> below_center_set l N c \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N"
      proof- fix x assume "x \<in> below_center_set l N c"
        show "val (\<eta> (take m x)) \<le> val (c x) - eint (int N)"
        proof-
          show "val (\<eta> (take m x)) \<le> val (c x) - eint (int N)"
            using \<open>x \<in> below_center_set l N c\<close> below_center_set_def by blast
        qed
      qed      
      have bcsI: "\<And>x . x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N \<Longrightarrow> 
                       x \<in> below_center_set l N c"
        unfolding below_center_set_def by blast
      obtain T where T_def: "T = S \<inter> below_center_set l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N"
        unfolding assms using T_def  \<open>S \<subseteq> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>)\<close> apply blast
        using T_def S_def apply blast
        using T_def bcsE by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> val (\<eta> (take m x)) \<le> val (c x) - N
                      \<Longrightarrow> x \<in> T"
        unfolding T_def using bcsI S_def by blast
        
         have 0: "\<And>x. x \<in> below_center_set l N c \<Longrightarrow> val (\<eta> (take m x) \<ominus> (c x)) = val (\<eta> (take m x))"
         proof- fix x assume A: "x \<in> below_center_set l N c" 
           show "val (\<eta> (take m x) \<ominus> (c x)) = val (\<eta> (take m x))"
             apply(rule fact_iii'[of N n]) 
                  apply (simp add: \<open>0 < N\<close>)
                using assms(1) n_def apply blast                
               using N_def assms(1) apply linarith
              using A below_center_set_closed le_add1 local.take_closed apply blast
             using  A function_ring_car_closed SA_car_memE(2) assms below_center_set_closed apply blast             
         by (metis (mono_tags, lifting) A below_center_set_def comm_monoid_add_class.add_0 eint_minus_comm idiff_0 mem_Collect_eq)
         qed
         have 1: "\<And>x. x \<in> below_center_set l N c \<Longrightarrow> val (\<eta> (take m x)) \<le> val (a x) \<Longrightarrow> x \<in> T"
         proof- fix x assume A0: "x \<in> below_center_set l N c" assume A1: "val (\<eta> (take m x)) \<le> val (a x)"
           show "x \<in> T"
             apply(rule T_memI)
               apply (metis (no_types, lifting) A0 add.commute below_center_set_def mem_Collect_eq)
                using 0[of x] A0 A1 apply presburger
                 using A0 bcsE by blast
         qed
         have 2: "T = below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
         proof
           show "T \<subseteq> below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
             by (smt "0" Int_Collect T_memE(1) T_memE(2) T_memE(3) bcsI subsetI)
           show "below_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)} \<subseteq> T"
             using "1" by blast
         qed
         have "is_semialgebraic (m+l)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
           using fact_i' assms  by blast
         thus ?thesis using 2 unfolding T_def 
           using assms(2) below_center_set_is_semialgebraic intersection_is_semialg assms(1) by presburger          
    qed
    show "is_semialgebraic (m + l) (S \<inter> above_center_set l N c)"
    proof-
      have acsE: "\<And>x . x \<in> above_center_set l N c \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N"
      proof- fix x assume "x \<in> above_center_set l N c"
        thus "val (\<eta> (take m x)) \<ge> val (c x) + eint (int N)"
            using  above_center_set_def by blast
      qed      
      have acsI: "\<And>x . x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N \<Longrightarrow> 
                       x \<in> above_center_set l N c"
        unfolding above_center_set_def by blast
      obtain T where T_def: "T = S \<inter> above_center_set l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N"
        unfolding assms S_def using T_def assms S_def apply blast
          using T_def assms S_def apply blast
           using T_def acsE by blast
         have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> val (\<eta> (take m x)) \<ge> val (c x) + N
                      \<Longrightarrow> x \<in> T"
           unfolding T_def using assms S_def  acsI by blast
         have 0: "\<And>x. x \<in> above_center_set l N c \<Longrightarrow> val (\<eta> (take m x) \<ominus> (c x)) = val (c x)"
         proof- fix x assume A: "x \<in> above_center_set l N c" 
           show "val (\<eta> (take m x) \<ominus> (c x)) = val (c x)" 
             apply(rule fact_iii[of N n]) 
                  apply (simp add: \<open>0 < N\<close>)
                using assms(1) n_def apply blast
                using N_def apply blast
                using A take_closed' DL_2_4_2 unfolding above_center_set_def apply blast 
                using A take_closed' DL_2_4_2 function_ring_car_closed SA_car_memE(2) above_center_set_closed assms(1) 
                 apply (meson subsetD)
            by (metis A acsE add.commute)
         qed
         have 1: "\<And>x. x \<in> above_center_set l N c \<Longrightarrow> val (c x) \<le> val (a x) \<Longrightarrow> x \<in> T"
         proof- fix x assume A0: "x \<in> above_center_set l N c" assume A1: "val (c x) \<le> val (a x) "
           show "x \<in> T"
             apply(rule T_memI)
             using A0 unfolding above_center_set_def apply blast 
              using A0 0[of x] A1 apply presburger
               using A0 acsE by blast
         qed
         have 2: "T = above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (c x) \<le> val (a x)}"
         proof
           show "T \<subseteq> above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)}"
             by (smt "0" DL_2_4_2 Int_Collect SA_a_inv_eval T_memE(1) T_memE(2) T_memE(3) acsI add_gr_0 assms(2) subsetI)            
           show "above_center_set l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)} \<subseteq> T"
             using "1" by (smt DL_2_4_2 Int_Collect SA_a_inv_eval add_gr_0 assms(2) subsetI)            
         qed
         have 3: "is_semialgebraic (m+l)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)}"
           using assms DL_2_4_2 semialg_val_ineq_set_is_semialg[of  c "m+l" a] by linarith 
         thus ?thesis using 2 above_center_set_is_semialgebraic assms intersection_is_semialg T_def 
           by (metis (no_types, lifting))
    qed
    show "is_semialgebraic (m + l) (S \<inter> at_center_set_diff_ac l N c)"
    proof-
      have acdaE: "\<And>x. x \<in> at_center_set_diff_ac l N c \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                  "\<And>x. x \<in> at_center_set_diff_ac l N c \<Longrightarrow> ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x)"
        unfolding at_center_set_diff_ac_def apply blast 
        unfolding at_center_set_diff_ac_def by blast 
      have  acdaI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) \<Longrightarrow>
               ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x) \<Longrightarrow> x \<in> at_center_set_diff_ac l N c"
        unfolding at_center_set_diff_ac_def by blast 
      obtain T where T_def: "T = S \<inter> at_center_set_diff_ac l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                   "\<And>x. x \<in> T \<Longrightarrow> ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x)"
        unfolding S_def T_def assms at_center_set_diff_ac_def 
           apply blast apply blast apply blast by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) \<Longrightarrow> 
            ac (e + N) (\<eta> (take m x)) \<noteq> ac (e + N) (c x) \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> x \<in> T"
        unfolding S_def T_def assms at_center_set_diff_ac_def by blast 
      obtain F where F_def: "F = (\<lambda> (s,t). at_center_set_diff_ac l N c \<inter> 
                                           {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> 
                                                                    ac (e+N) (c x) = s \<and> ac (e + N) (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> ps \<in> Units (Zp_res_ring (e+N)) \<times> Units (Zp_res_ring (e+N)). T \<inter> F ps)"
      proof
        show "T \<subseteq> (\<Union>ps\<in>Units (residue_ring (p ^ (e + N))) \<times> Units (residue_ring (p ^ (e + N))). T \<inter> F ps)"
        proof fix x assume A: "x \<in> T "
          then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding S_def T_def assms by blast 
          have etax_closed: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
            using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
          have cx_closed: "c x \<in> nonzero Q\<^sub>p"
            using etax_closed assms A T_memE 
            by (metis (no_types, lifting) function_ring_car_closed Qp.nonzero_closed SA_car_memE(2) not_nonzero_Qp order_le_less val_ineq)
          obtain s where s_def: "s = ac (e+N) (c x)" by blast 
          obtain t where t_def: "t = ac (e+N) (\<eta> (take m x))" by blast 
          have 1: "s \<in> Units (Zp_res_ring (e+N))"
            unfolding s_def using cx_closed 
            by (metis \<open>0 < N\<close> ac_units add_gr_0 mult_2)
          have 2: "t \<in> Units (Zp_res_ring (e+N))"
            unfolding t_def using etax_closed 
            by (metis \<open>0 < N\<close> ac_units add_gr_0 mult_2)
          have 3: "(s,t) \<in>  Units (Zp_res_ring (e+N)) \<times> Units (Zp_res_ring (e+N))"
            using 1 2 
            by blast
          have  4: "x \<in> at_center_set_diff_ac l N c"
            using A T_def by blast
          have "F (s,t) =  at_center_set_diff_ac l N c \<inter>
            {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>).
             c x \<in> nonzero Q\<^sub>p \<and> ac (e + N) (c x) = s \<and> ac (e + N) (\<eta> (take m x)) = t}"
            unfolding F_def by blast 
          hence 5: "x \<in> F (s,t)"
            unfolding s_def t_def using 4 x_closed cx_closed by blast
          show "x \<in> (\<Union>ps\<in>Units (residue_ring (p ^ (e + N))) \<times> Units (residue_ring (p ^ (e + N))). T \<inter> F ps)"
            using 3 s_def t_def A 5 by blast
        qed   
        show "(\<Union>ps\<in>Units (residue_ring (p ^ (e + N))) \<times> Units (residue_ring (p ^ (e + N))). T \<inter> F ps) \<subseteq> T"
          by blast 
      qed
      have F_semialg: "\<And>ps. ps \<in> Units (Zp_res_ring (e+N)) \<times> Units (Zp_res_ring (e+N))
                  \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
      proof- fix ps assume A: "ps \<in> Units (Zp_res_ring (e+N)) \<times> Units (Zp_res_ring (e+N))"
        show "is_semialgebraic (m+l) (T \<inter> F ps)"
        proof(cases "T \<inter> F ps = {}")
          case True
          then show ?thesis 
            by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F ps"
            by blast
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using x_def unfolding S_def T_def assms by blast 
          have x_in_acda: "x \<in> at_center_set_diff_ac l N c"
            using x_def unfolding T_def by blast 
          have F0: "\<And>y. y \<in> F ps \<Longrightarrow> val (\<eta> (take m y) \<ominus> c y) - val (c y) = val (\<eta> (take m x) \<ominus> c x) - val (c x)"
          proof- fix y assume A0: " y \<in> F ps"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def by blast 
            have y_in_acda: "y \<in> at_center_set_diff_ac l N c"
              using A0 unfolding F_def by blast 
            obtain s t where st_def: "ps = (s,t)"
              using A0 A by blast              
            have F_alt_def: "F ps = at_center_set_diff_ac l N c \<inter>
            {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> ac (e+N) (c x) = s \<and> ac (e + N) (\<eta> (take m x)) = t}"
              using st_def A unfolding F_def by blast               
            show "val (\<eta> (take m y) \<ominus> c y) - val (c y) = val (\<eta> (take m x) \<ominus> c x) - val (c x)"
              apply(rule fact_v[of N n])
              using \<open>0 < N\<close> apply auto[1]
              apply (simp add: n_def)
              using N_def apply linarith
              using DL_2_4_2 take_closed' y_closed apply blast                                      
              using A0 F_alt_def apply blast
              using DL_2_4_2 take_closed' x_closed apply blast
              using x_def unfolding F_alt_def apply blast
              using A0 unfolding F_alt_def apply (smt DL_2_4_2 Int_Collect \<eta>_nonzero acdaE(1) eint.inject take_closed' val_ord)
              using x_def unfolding F_alt_def apply (smt DL_2_4_2 IntE Int_Collect \<eta>_nonzero acdaE(1) eint.inject take_closed' val_ord)
              using acdaE(2) y_in_acda apply blast
              using acdaE(2) x_in_acda apply blast
              apply (smt A0 F_alt_def Int_Collect inf_sup_aci(2) x_def)
              by (metis (mono_tags, lifting) A0 F_alt_def Int_Collect inf_sup_aci(2) x_def)
          qed 
          have F1: "val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
            using x_def T_memE by blast 
          have F2: "\<And>y. y \<in> F ps \<Longrightarrow> val (\<eta> (take m y) \<ominus> c y) - val (c y) = val (\<eta> (take m x) \<ominus> c x) - val (c x)"
            using F0 unfolding F1 by blast                                                                            
          obtain i where i_def: "i = ord (\<eta> (take m x) \<ominus> c x) - ord (c x) "
            by blast 
          then have F3: "ord (\<eta> (take m x) \<ominus> c x) =  ord (c x) + i"
            by presburger 
          have F4: "\<And>y. y \<in> F ps \<Longrightarrow> val (\<eta> (take m y) \<ominus> c y) = val (c y) + i"
          proof-
            fix y assume A: "y \<in> F ps"
            hence F40: "val (\<eta> (take m y) \<ominus> c y) - val (c y) = val (\<eta> (take m x) \<ominus> c x) - val (c x)"
              using F2 by blast 
            have F41: "\<eta> (take m x) \<noteq> c x"
              by (metis acdaE(2) x_in_acda)
            have F42: "\<eta> (take m x) \<in> carrier Q\<^sub>p"
              using DL_2_4_2 \<eta>_closed take_closed' x_closed by blast
            have F43: "c x \<in> carrier Q\<^sub>p"
              by (metis (no_types, lifting) PiE SA_car_memE(3) assms(1) x_closed)
            have F44: "\<eta> (take m x) \<ominus> c x \<noteq> \<zero>"
              using F41 F42 F43  Qp.r_right_minus_eq by blast
            hence F45: "\<eta> (take m x) \<ominus> c x \<in> nonzero Q\<^sub>p"
              using F41 F42 F43 Qp.not_eq_diff_nonzero by blast
            have F46: "c x \<in> nonzero Q\<^sub>p"
              using local.F_def x_def by blast
            hence  F47: " val (\<eta> (take m x) \<ominus> c x) - val (c x) =  ord (\<eta> (take m x) \<ominus> c x) - ord (c x)"          
              using F45 idiff_eint_eint val_ord by presburger
            have F48: "\<eta> (take m y) \<ominus> (c y) \<in> nonzero Q\<^sub>p"
              by (metis (no_types, lifting) A DL_2_4_2 IntE Qp.nonzero_closed Qp.not_eq_diff_nonzero \<eta>_closed acdaE(2) local.F_def mem_Collect_eq mem_case_prodE take_closed')
            have F49: "c y \<in> nonzero Q\<^sub>p"
              using A local.F_def by blast
            hence F50: " val (\<eta> (take m y) \<ominus> c y) - val (c y) =  ord (\<eta> (take m y) \<ominus> c y) - ord (c y)"          
              using F48 idiff_eint_eint val_ord by presburger
            hence F51: "ord (\<eta> (take m y) \<ominus> c y) - ord (c y) =  ord (\<eta> (take m x) \<ominus> c x) - ord (c x)"
              by (metis F40 F47 eint.inject)
            show "val (\<eta> (take m y) \<ominus> c y) = val (c y) + eint i "
              using F51 unfolding i_def 
              by (metis F40 F47 F49 Qp.not_nonzero_memI Qp.zero_closed eint_add_cancel_fact
                  eint_diff_imp_eint local.val_zero plus_eq_infty_iff_eint)              
          qed
          obtain U where U_def: "U = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (c x) \<le> val (a x) + eint (-i)}"
            by blast 
          have U_semialg: "is_semialgebraic (m+l) U"
            unfolding U_def 
            using assms semialg_val_ineq_set_plus[of "m+l" c a "-i"] DL_2_4_2 by blast
          have U_alt_def: "U = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (c x) + i \<le> val (a x) }" 
          proof show "U \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) + eint i \<le> val (a x)}"
            proof fix x assume A: "x \<in> U"
              then have "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<and> val (c x) \<le> val (a x) + eint (-i)"
                unfolding U_def by blast 
              hence "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<and> val (c x) + eint i \<le> val (a x) + eint (-i) + eint i"
                using add_mono_thms_linordered_semiring(3) by blast
              hence "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<and> val (c x) + eint i \<le> val (a x)"
                by (metis ab_semigroup_add_class.add_ac(1) add.right_neutral eint.simps(3) eint_add_cancel_fact idiff_0)
              thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) + eint i \<le> val (a x)}"
                by blast 
            qed
            show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) + eint i \<le> val (a x)} \<subseteq> U"
            proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) + eint i \<le> val (a x)}"
              then have "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<and> val (c x) + eint i \<le> val (a x)" by blast 
              hence "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<and> val (c x) + eint i + eint (-i) \<le> val (a x) + eint (-i)"
                using add_mono_thms_linordered_semiring(3) by blast
              hence "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<and> val (c x) \<le> val (a x) + eint (-i)"  
                by (metis ab_semigroup_add_class.add_ac(1) add.right_neutral eint.simps(3) eint_add_cancel_fact idiff_0)
              thus "x \<in> U"
                unfolding U_def by blast 
            qed
          qed
          have F5: "F ps \<inter> U = F ps \<inter> T" 
          proof
            show "F ps \<inter> U \<subseteq> F ps \<inter> T"
            proof fix x assume A: "x \<in> F ps \<inter> U"
              have "x \<in> T"
                apply(rule T_memI)
                using A unfolding U_def apply blast 
                using A unfolding F_def apply (meson IntD1 acdaE(1) mem_case_prodE)
                using A unfolding F_def apply (meson IntD1 acdaE(2) mem_case_prodE)
                using  A F4 unfolding U_def 
                by (metis (no_types, lifting) Int_Collect U_alt_def U_def)
              thus "x \<in> F ps \<inter> T" using A by blast 
            qed
            show "F ps \<inter> T \<subseteq> F ps \<inter> U"
              unfolding U_def using F4 T_memE 
              by (smt IntD1 IntD2 IntI U_alt_def U_def mem_Collect_eq subsetI)
          qed
          have F4: "is_semialgebraic (m+l) (F ps)"
          proof-
            obtain s t where ist_def: "ps = (s,t)"
              by (meson surj_pair)              
            have F40: "F ps = at_center_set_diff_ac l N c \<inter> 
                                           {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and>  
                                                                    ac (e+N) (c x) = s \<and> ac (e + N) (\<eta> (take m x)) = t}"
              unfolding ist_def F_def by blast
            have F42: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> ac (e+N) (c x) = s}"
              using assms ac_cong_set_SA[of "e+N" s c m l] ist_def A 
              by (metis (no_types, lifting) DL_2_4_2 \<open>0 < N\<close> add_is_0 gr0I mem_Sigma_iff mult_is_0 of_nat_0 of_nat_zero_less_power_iff zero_power2)
            have F43: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e + N) (\<eta> (take m x)) = t}"
              using assms fact_ii'[of "e+N" t l] ist_def A 
              by (smt DL_2_4_2 F40 IntE Int_Collect \<eta>_nonzero \<open>0 < N\<close> ac_units add_is_0 gr0I mult_is_0 of_nat_0 of_nat_zero_less_power_iff take_closed' x_def zero_power2)
            have "F ps =   at_center_set_diff_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). (c x) \<in> nonzero Q\<^sub>p \<and> ac (e+N) (c x) = s} \<inter>
                                                            {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ac (e + N) (\<eta> (take m x)) = t}"
              unfolding F40 by blast 
            thus ?thesis using intersection_is_semialg  F40  F42 F43 
              by (metis (no_types, lifting) \<open>0 < N\<close> assms(1) at_center_set_diff_ac_is_semialgebraic)            
          qed 
          then show ?thesis 
           by (metis F5 U_semialg inf_commute intersection_is_semialg)                    
        qed
      qed
      have F_finite: "finite ((\<lambda>ps. T \<inter> F ps) ` (Units (residue_ring (p ^ (e + N))) \<times> Units (residue_ring (p ^ (e + N)))))"
      proof-
        have 0: "finite (Units (residue_ring (p ^ (e + N))))"
          using residues.finite_Units[of "e+N"] 
          by (metis \<open>0 < N\<close> add_eq_0_iff_both_eq_0 mult_is_0 nat_neq_iff padic_fields.prime padic_fields_axioms residues.finite_Units residues_n zero_neq_numeral)
        have 1: "finite {0..<int n}" by blast
        show ?thesis using 0 1 by blast
      qed
      then have "is_semialgebraic (m + l) T"
        using F_covers finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps) `(Units (Zp_res_ring (e+N)) \<times> Units (Zp_res_ring (e+N)))" "m+l"]
              F_semialg  by (metis image_subsetI is_semialgebraicE)
      thus ?thesis unfolding T_def by blast 
    qed
    show "is_semialgebraic (m + l) (S \<inter> at_center_set_eq_ac l N c)"
    proof-
      have aceaE: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                  "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x)"
        unfolding at_center_set_eq_ac_def apply blast 
        unfolding at_center_set_eq_ac_def by blast 
      have  aceaI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) \<Longrightarrow>
               ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x) \<Longrightarrow> x \<in> at_center_set_eq_ac l N c"
        unfolding at_center_set_eq_ac_def by blast 
      obtain T where T_def: "T = S \<inter> at_center_set_eq_ac l N c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x)"
                   "\<And>x. x \<in> T \<Longrightarrow> ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x)"                   
        unfolding S_def T_def assms at_center_set_eq_ac_def 
           apply blast apply blast apply blast by blast
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) \<Longrightarrow> 
            ac (e + N) (\<eta> (take m x)) = ac (e + N) (c x) \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> x \<in> T"
        unfolding S_def T_def assms at_center_set_eq_ac_def mem_Collect_eq by blast 
      obtain g where g_def: "g = ((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k)
                                   \<otimes>\<^bsub>SA (m+l)\<^esub> one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1)))"
        by blast 
      have "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> c x \<noteq>  \<zero>"
        by (metis (no_types, lifting) DL_2_4_2 Qp.not_nonzero_memI Qp.zero_closed \<eta>_nonzero aceaE(1) add.right_neutral at_center_set_eq_ac_closed eint_diff_imp_eint subsetD take_closed' zero_eint_def)
      hence P0: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1))) x = inv ([k]\<cdot>((c x)[^](k-1)))"
        using assms  by (smt DL_2_4_0 DL_2_4_2 function_ring_car_closed Qp.nonzero_pow_nonzero SA_car_memE(2) SA_nat_pow add_gr_0 at_center_set_eq_ac_closed gr0I not_numeral_le_zero one_over_fun_add_pow_eval padic_fields.SA_car_memE(1) padic_fields.SA_nat_pow_closed padic_fields_axioms subsetD)        
      have P1: "(fun_inc (m+l) m \<xi>_1) \<in> carrier (SA (m+l))"
        by (meson \<xi>_1_characterization denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms fun_inc_closed le_iff_add)
      have P2: "c [^]\<^bsub>SA (m+l)\<^esub> k \<in> carrier (SA (m+l))"
        by (meson SA_imp_semialg SA_nat_pow_closed add_gr_0 assms denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms)
      have P3: "one_over_fun (m+l) ([k] \<cdot>\<^bsub>SA (m+l)\<^esub> (c[^]\<^bsub>SA (m+l)\<^esub> (k-1))) \<in> carrier (SA (m+l))"
        by (meson DL_2_4_2 SA_add_pow_closed SA_imp_semialg SA_nat_pow_closed add_gr_0 assms(1) one_over_fun_closed)        
      have P1_eval: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> (fun_inc (m+l) m \<xi>_1) x = \<xi>_1 (take m x)"
          using \<xi>_1_characterization assms fun_inc_eval[of x "m+l" m \<xi>_1] P1 
          by (meson at_center_set_eq_ac_closed fun_inc_eval subsetD)
      have P4:  "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> ((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k) x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k)"
      proof- fix x assume A: "x \<in> at_center_set_eq_ac l N c"
        hence x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
          using at_center_set_eq_ac_closed by blast
        thus "((fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> (c [^]\<^bsub>SA (m+l)\<^esub> k)) x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k)"
          using \<xi>_1_characterization assms fun_inc_eval[of x "m+l" m \<xi>_1] P1 P2 P1_eval SA_minus_eval 
                 DL_2_4_2 SA_nat_pow add_gr_0 by presburger
      qed
      have P5: "(fun_inc (m+l) m \<xi>_1) \<ominus>\<^bsub>SA (m+l)\<^esub> c [^]\<^bsub>SA (m+l)\<^esub> k \<in> carrier (SA (m+l))"
        using SA_minus_closed fun_inc_closed DL_2_4_2 P1 P2 add_gr_0 by presburger
      have g_eval: "\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> g x = (\<xi>_1 (take m x) \<ominus> (c x)[^]k) \<otimes> inv ([k]\<cdot>((c x)[^](k-1)))"
        using P0 P3 P4 P5 aceaE
        by (smt SA_mult at_center_set_eq_ac_closed g_def subsetD)
      have  g_closed: "g \<in> carrier (SA (m+l))"
        using P3 P5 SA_imp_semialg add_gr_0 denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms g_def padic_fields.SA_mult_closed padic_fields_axioms by presburger
      have P6: "\<And>x . x \<in> at_center_set_eq_ac l N c \<Longrightarrow> val (\<eta> (take m x)\<ominus> c x) = val (g x)"
      proof- fix x assume A: "x \<in> at_center_set_eq_ac l N c"
        have P60: "c x \<in> nonzero Q\<^sub>p"
          using A unfolding at_center_set_eq_ac_def 
          by (metis (no_types, lifting) A function_ring_car_closed SA_car_memE(2) 
              \<open>\<And>x. x \<in> at_center_set_eq_ac l N c \<Longrightarrow> c x \<noteq> \<zero>\<close> assms(1) mem_Collect_eq not_nonzero_Qp)
        have "val (\<eta> (take m x)\<ominus> c x) = val ((\<xi>_1 (take m x) \<ominus> (c x)[^]k) \<otimes> inv ([k]\<cdot>((c x)[^](k-1))))"
          apply(rule fact_vi(1)[of N n]) 
          apply (simp add: \<open>0 < N\<close>) 
          apply (simp add: n_def)          
          using N_def apply blast
          using A at_center_set_eq_ac_def take_closed' DL_2_4_2 apply blast
          using A function_ring_car_closed SA_car_memE(2) assms(2) at_center_set_eq_ac_closed 
          using P60 apply blast                  
          apply (metis (no_types, lifting) A Qp.not_nonzero_memI Qp.zero_closed aceaE(1) eint.inject padic_fields.val_def padic_fields_axioms val_nonzero')
          using A aceaE(2) by blast
        thus "val (\<eta> (take m x) \<ominus> c x) = val (g x)" using A g_eval 
          by presburger
      qed
      have P7: "T = at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (g x) \<le> val (a x)}"
      proof
        show "T \<subseteq> at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (a x)}"
          apply(rule subsetI)
          using T_memE P6 by (smt Int_Collect aceaI)
        show " at_center_set_eq_ac l N c \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (g x) \<le> val (a x)} \<subseteq> T"
          apply(rule subsetI)
          using T_memI P6 by (smt Int_Collect aceaE(1) aceaE(2))
      qed
      have "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (g x) \<le> val (a x)}"
        using g_closed semialg_val_ineq_set_is_semialg[of g "m+l"  a] DL_2_4_2 assms  by blast
      thus ?thesis using P7 intersection_is_semialg 
        by (metis (no_types, lifting) T_def \<open>0 < N\<close> assms(1) at_center_set_eq_ac_is_semialgebraic)  
    qed
    show "\<And>i. i \<in> {1..int N - 1} \<Longrightarrow> is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
    proof- fix i assume A: "i \<in> {1..int N - 1}"
      have ncsE: "\<And>x. x \<in> near_center_set l i c \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
        unfolding near_center_set_def by blast 
      have ncsI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> x \<in> near_center_set l i c"
        unfolding near_center_set_def by blast 
      obtain T where T_def: "T = S \<inter> near_center_set l i c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
                  "\<And>x. x \<in> T \<Longrightarrow> ord (\<eta> (take m x)) = ord (c x) + i"
        unfolding S_def T_def assms near_center_set_def apply blast apply blast apply blast
      proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (c x) + eint i}"
        then have "c x \<noteq> \<zero>"
          using val_zero \<eta>_nonzero take_closed' 
          by (metis (mono_tags, lifting) DL_2_4_2 Int_Collect Qp.not_nonzero_memI Qp.zero_closed eint_diff_imp_eint)
        thus "ord (\<eta> (take m x)) = ord (c x) + i"
          using A val_ord[of "\<eta> (take m x)"]  val_ord[of "c x"] 
          by (metis (mono_tags, lifting) DL_2_4_2 function_ring_car_closed Int_Collect SA_car_memE(2) \<eta>_nonzero assms(1) eint.inject not_nonzero_Qp plus_eint_simps(1) take_closed')
      qed
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow>
                  val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> x \<in> T"
        unfolding S_def T_def assms near_center_set_def by blast 
      obtain F where F_def: 
        "F = (\<lambda> (j, s, t). {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t))"
      proof
        show "T \<subseteq> (\<Union> (j, s, t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
        proof fix x assume A: "x \<in> T" 
          have 00: "c x \<in> nonzero Q\<^sub>p"
            using eint_diff_imp_eint[of "\<eta> (take m x)" "c x"] A 
            by (meson DL_2_4_2 Qp.function_ring_car_memE SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(1) take_closed')                         
          have 0: "\<eta> (take m x) \<noteq> \<zero>"
            using A unfolding T_def near_center_set_def  
            using DL_2_4_2 Qp.nonzero_memE(2) \<eta>_nonzero take_closed' by blast
          hence 1: "c x \<in> nonzero Q\<^sub>p"
            using A unfolding T_def using "00" by blast           
          have 2: "ord (c x) mod n \<in> {0..< n}"
            by (meson atLeastLessThan_iff n_def of_nat_0_less_iff pos_mod_conj)            
          have 3: "ac N (c x) \<in> Units (Zp_res_ring N)"
            using 1 \<open>0 < N\<close> ac_units by blast
          have 4: "ac N (\<eta> (take m x)) \<in> Units (Zp_res_ring N)"
            using 0 A unfolding T_def near_center_set_def 
            using DL_2_4_2 \<eta>_nonzero \<open>0 < N\<close> ac_units take_closed' by blast
          obtain tr where tr_def: "tr = (ord (c x) mod n, ac N (c x),  ac N (\<eta> (take m x)))"
            by blast 
          have 5: "tr \<in> {0..< n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)"
            using 2 3 4 unfolding tr_def by blast 
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using A T_memE(1) by blast
          hence  "x \<in> T \<inter> F tr"
            unfolding F_def tr_def using add.commute[of _  i]  00 A 5 T_memE by blast                    
          thus "x \<in> (\<Union>(j,s,t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
            using 5 by blast 
        qed
        show "(\<Union> (j, s, t) \<in> ({0..< int n }\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t)) \<subseteq> T"
          unfolding F_def by blast 
      qed
      have F_covers: "T = (\<Union> ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F ps)"
        using F_covers by blast 
      have finite: "finite ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
      proof-
        have "finite  (Units (Zp_res_ring N))"
          using \<open>0 < N\<close> p_residues residues.finite_Units by blast
        thus ?thesis by blast
      qed
      have F_semialg: "\<And>j s t . (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
      proof-
        fix j s t assume jst_def: "(j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
        show "is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
        proof(cases "T \<inter> F (j, s, t) = {}")
          case True
          then show ?thesis by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F (j, s, t)" by blast 
          hence x_in_F: "x \<in> F (j,s,t)" by blast 
          have F0: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> val (\<eta> (take m y) \<ominus> (c y)) = val (c y)"
          proof- fix y assume A0: "y \<in> F (j, s, t)"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def T_def assms  by blast 
            have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using x_def unfolding F_def T_def assms  by blast 
            have 0: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
            have "c x \<in> carrier Q\<^sub>p" 
              using function_ring_car_closed SA_car_memE(2) assms(2) x_closed  assms(1) by blast              
            hence 1: "c x \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE x_def 0 eint_diff_imp_eint[of "\<eta> (take m x)" "c x" i] unfolding F_def T_def near_center_set_def
              by blast       
            have 2: "\<eta> (take m y) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' y_closed by blast
            have 3: "c y \<in> carrier Q\<^sub>p"
              using function_ring_car_closed SA_car_memE(2) assms(2) y_closed assms(1) by blast
            hence 4: "c y \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE  A0 2 eint_diff_imp_eint[of "\<eta> (take m y)" "c y" i]
              unfolding F_def T_def near_center_set_def  by blast
            have 5: "y \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using A0 unfolding F_def by blast 
            have 6: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using x_in_F unfolding F_def by blast 
            show "val (\<eta> (take m y) \<ominus> c y) = val (c y)"
            apply(rule fact_iv[of N n i])
                          apply (simp add: \<open>0 < N\<close>)
                          apply (simp add: n_def)                         
                        using A  apply blast
                       using N_def apply blast
                      using A0 take_closed' DL_2_4_2 
                      unfolding F_def  T_def near_center_set_def apply blast 
                     using A0 assms(2) unfolding F_def  T_def near_center_set_def 
                     using function_ring_car_closed SA_car_memE(2) apply blast
                    using DL_2_4_2 take_closed' x_closed apply blast
                   using function_ring_car_closed SA_car_memE(2) assms(2) x_closed 1 apply blast                   
                  using 5 6 unfolding mem_Collect_eq apply metis   
                 using 5 6 unfolding mem_Collect_eq apply metis   
                using 5 6 unfolding mem_Collect_eq apply metis   
               using 5 unfolding add.commute[of "ord (c y)" i]  mem_Collect_eq apply blast 
              using 6 unfolding add.commute[of "ord (c x)" i]  mem_Collect_eq by blast 
          qed
          have F3: "F (j,s,t) \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding F_def by blast 
          have F4: "F (j, s, t) \<inter> T = F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (c x) \<le> val (a x)}"
          proof 
            show "F (j, s, t) \<inter> T \<subseteq> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le>  val (a x)}"
            proof
              fix x assume P: "x \<in> F (j,s,t) \<inter> T"
              then have "val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                using T_memE by blast
              then have "val (c x) \<le> val (a x)"
                using P F0 by (metis IntD1)
              thus "x \<in> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)}"
                using P unfolding S_def T_def assms  by blast 
            qed
            show "F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)} \<subseteq> F (j, s, t) \<inter> T"
            proof fix x assume P : "x \<in> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)}"
              then have P0: "val (\<eta> (take m x) \<ominus> (c x)) \<le> val (a x)"
                using F0 by (metis (no_types, lifting) Int_Collect)
              have P1: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<and> ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p"
                using P unfolding F_def by blast 
              have P2: "val (\<eta> (take m x)) = ord (\<eta> (take m x))"
                using P \<eta>_nonzero  take_closed' DL_2_4_2 val_ord by blast
              have P3: "val (c x) = ord (c x)"
                using P1 val_ord by blast
              have "x \<in> T"
                apply(rule T_memI) 
                using P apply blast 
                using P unfolding F_def using P2 P3  val_ord \<eta>_nonzero P1 plus_eint_simps(1) apply presburger
                using P F0 P0 by linarith
              thus "x \<in> F (j, s, t) \<inter> T"
                using P by blast 
            qed
          qed 
          have F5: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (c x) \<le> val (a x)}"
            using assms semialg_val_ineq_set_is_semialg[of c "m+l"  a]  DL_2_4_2 by blast
          have F6: "is_semialgebraic (m+l) (F (j, s, t))"
          proof-
            obtain F0 where F0_def: "F0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) = ord (c x) + i }"
              by blast 
            obtain F1 where F1_def: "F1 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j}"
              by blast 
            obtain F2 where F2_def: "F2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ac N (c x) = s }"
              by blast
            obtain F3 where F3_def: "F3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>).  ac N (\<eta> (take m x)) = t }"
              by blast
            have 00: "is_semialgebraic (m+l) F0"
              unfolding F0_def   using assms fact_i_take[of c l i] by blast               
            have 01: "is_semialgebraic (m+l) F1"
              unfolding F1_def using assms ord_congruence_set_SA_function[of n c m l j] DL_2_4_2 n_def 
              by linarith              
            have 02: "is_semialgebraic (m+l) F2"
              unfolding F2_def using assms ac_cong_set_SA[of N  s c m l] jst_def \<open>0 < N\<close>
                    denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms by blast
            have 03: "is_semialgebraic (m+l) F3"
              unfolding F3_def using fact_ii'[of N t l] \<open>0 < N\<close> jst_def by blast
            have 04: "F (j,s,t) =  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              unfolding F_def by blast 
            have "F (j, s, t) = F0 \<inter>F1 \<inter> F2 \<inter>F3"
              unfolding 04 F0_def F1_def F2_def F3_def by blast 
            thus ?thesis using 00 01 02 03 intersection_is_semialg  
              by simp
          qed
          then show ?thesis using F4 F5 
            by (metis (no_types, lifting) inf_commute intersection_is_semialg)
        qed
      qed
      have F_semialg: "\<And>ps . ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
        using F_semialg by blast
      show "is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
        using F_semialg finite F_covers 
              finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps)` ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))" "m+l" ]  
        by (metis T_def finite_imageI image_subsetI is_semialgebraicE)
    qed
    show "\<And>i. i \<in> {- (int N) + 1..-1} \<Longrightarrow> is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
    proof- fix i assume A: "i \<in> {- (int N) + 1..-1}"
      have ncsE: "\<And>x. x \<in> near_center_set l i c \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
        unfolding near_center_set_def by blast 
      have ncsI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow> x \<in> near_center_set l i c"
        unfolding near_center_set_def by blast 
      obtain T where T_def: "T = S \<inter> near_center_set l i c"
        by blast 
      have T_memE: "\<And>x. x \<in> T \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                   "\<And>x. x \<in> T \<Longrightarrow> val (\<eta> (take m x)) = val (c x) + i"
                  "\<And>x. x \<in> T \<Longrightarrow> ord (\<eta> (take m x)) = ord (c x) + i"
        unfolding S_def T_def assms near_center_set_def apply blast apply blast apply blast
      proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) = val (c x) + eint i}"
        then have "c x \<noteq> \<zero>"
          using val_zero \<eta>_nonzero take_closed' 
          by (metis (mono_tags, lifting) DL_2_4_2 Int_Collect Qp.not_nonzero_memI Qp.zero_closed eint_diff_imp_eint)
        thus "ord (\<eta> (take m x)) = ord (c x) + i"
          using A val_ord[of "\<eta> (take m x)"]  val_ord[of "c x"] 
          by (metis (mono_tags, lifting) DL_2_4_2 function_ring_car_closed Int_Collect SA_car_memE(2) \<eta>_nonzero assms(1) eint.inject not_nonzero_Qp plus_eint_simps(1) take_closed')
      qed
      have T_memI: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>) \<Longrightarrow>  val (\<eta> (take m x)) = val (c x) + i \<Longrightarrow>
                  val (\<eta> (take m x) \<ominus> c x) \<le> val (a x) \<Longrightarrow> x \<in> T"
        unfolding S_def T_def assms near_center_set_def by blast 
      obtain F where F_def: 
        "F = (\<lambda> (j, s, t). {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t})"
        by blast 
      have F_covers: "T = (\<Union> (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t))"
      proof
        show "T \<subseteq> (\<Union> (j, s, t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
        proof fix x assume A: "x \<in> T" 
          have 00: "c x \<in> nonzero Q\<^sub>p"
            using eint_diff_imp_eint[of "\<eta> (take m x)" "c x"] A 
            by (meson DL_2_4_2 Qp.function_ring_car_memE SA_car_memE(2) T_memE(1) T_memE(3) \<eta>_nonzero assms(1) take_closed')                         
          have 0: "\<eta> (take m x) \<noteq> \<zero>"
            using A unfolding T_def near_center_set_def  
            using DL_2_4_2 Qp.nonzero_memE(2) \<eta>_nonzero take_closed' by blast
          hence 1: "c x \<in> nonzero Q\<^sub>p"
            using A unfolding T_def using "00" by blast           
          have 2: "ord (c x) mod n \<in> {0..< n}"
            by (meson atLeastLessThan_iff n_def of_nat_0_less_iff pos_mod_conj)            
          have 3: "ac N (c x) \<in> Units (Zp_res_ring N)"
            using 1 \<open>0 < N\<close> ac_units by blast
          have 4: "ac N (\<eta> (take m x)) \<in> Units (Zp_res_ring N)"
            using 0 A unfolding T_def near_center_set_def 
            using DL_2_4_2 \<eta>_nonzero \<open>0 < N\<close> ac_units take_closed' by blast
          obtain tr where tr_def: "tr = (ord (c x) mod n, ac N (c x),  ac N (\<eta> (take m x)))"
            by blast 
          have 5: "tr \<in> {0..< n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)"
            using 2 3 4 unfolding tr_def by blast 
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            using A T_memE(1) by blast
          hence  "x \<in> T \<inter> F tr"
            unfolding F_def tr_def using add.commute[of _  i]  00 A 5 T_memE by blast                    
          thus "x \<in> (\<Union>(j,s,t) \<in> {0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N). T \<inter> F (j, s, t))"
            using 5 by blast 
        qed
        show "(\<Union> (j, s, t) \<in> ({0..< int n }\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F (j, s, t)) \<subseteq> T"
          unfolding F_def by blast 
      qed
      have F_covers: "T = (\<Union> ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N)). T \<inter> F ps)"
        using F_covers by blast 
      have finite: "finite ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
      proof-
        have "finite  (Units (Zp_res_ring N))"
          using \<open>0 < N\<close> p_residues residues.finite_Units by blast
        thus ?thesis by blast
      qed
      have F_semialg: "\<And>j s t . (j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
      proof-
        fix j s t assume jst_def: "(j, s, t) \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))"
        show "is_semialgebraic (m+l) (T \<inter> F (j, s, t))"
        proof(cases "T \<inter> F (j, s, t) = {}")
          case True
          then show ?thesis by (simp add: empty_is_semialgebraic)
        next
          case False
          then obtain x where x_def: "x \<in> T \<inter> F (j, s, t)" by blast 
          hence x_in_F: "x \<in> F (j,s,t)" by blast 
          have F0: "\<And>y. y \<in> F (j, s, t) \<Longrightarrow> val (\<eta> (take m y) \<ominus> (c y)) = val (\<eta> (take m y))"
          proof- fix y assume A0: "y \<in> F (j, s, t)"
            have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using A0 unfolding F_def T_def assms  by blast 
            have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
              using x_def unfolding F_def T_def assms  by blast 
            have 0: "\<eta> (take m x) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' x_closed by blast
            have "c x \<in> carrier Q\<^sub>p" 
              using function_ring_car_closed SA_car_memE(2) assms(2) x_closed  assms(1) by blast              
            hence 1: "c x \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE x_def 0 eint_diff_imp_eint[of "\<eta> (take m x)" "c x" i] unfolding F_def T_def near_center_set_def
              by blast       
            have 2: "\<eta> (take m y) \<in> nonzero Q\<^sub>p"
              using DL_2_4_2 \<eta>_nonzero take_closed' y_closed by blast
            have 3: "c y \<in> carrier Q\<^sub>p"
              using function_ring_car_closed SA_car_memE(2) assms(2) y_closed assms(1) by blast
            hence 4: "c y \<in> nonzero Q\<^sub>p"
              using Pair_inject mem_Collect_eq mem_case_prodE  A0 2 eint_diff_imp_eint[of "\<eta> (take m y)" "c y" i]
              unfolding F_def T_def near_center_set_def  by blast
            have 5: "y \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using A0 unfolding F_def by blast 
            have 6: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              using x_in_F unfolding F_def by blast 
            show "val (\<eta> (take m y) \<ominus> c y) = val (\<eta> (take m y))" 
            apply(rule fact_iv'[of N n i])
                          apply (simp add: \<open>0 < N\<close>)
                          apply (simp add: n_def)                         
                        using A apply blast
                       using N_def apply blast
                      using A0 take_closed' DL_2_4_2 
                      unfolding F_def  T_def near_center_set_def apply blast 
                     using A0 assms(2) unfolding F_def  T_def near_center_set_def 
                     using function_ring_car_closed SA_car_memE(2) apply blast
                    using DL_2_4_2 take_closed' x_closed apply blast
                   using function_ring_car_closed SA_car_memE(2) assms(2) x_closed 1 apply blast                   
                  using 5 6 unfolding mem_Collect_eq apply (metis mod_add_eq)                  
                 using 5 6 unfolding mem_Collect_eq apply metis   
                using 5 6 unfolding mem_Collect_eq apply metis   
               using 5 unfolding add.commute[of "ord (c y)" i]  mem_Collect_eq apply blast 
              using 6 unfolding add.commute[of "ord (c x)" i]  mem_Collect_eq by blast 
          qed
          have F3: "F (j,s,t) \<subseteq> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>)"
            unfolding F_def by blast 
          have F4: "F (j, s, t) \<inter> T = F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
          proof 
            show "F (j, s, t) \<inter> T \<subseteq> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le>  val (a x)}"
            proof
              fix x assume P: "x \<in> F (j,s,t) \<inter> T"
              then have "val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)"
                using T_memE by blast
              then have "val (\<eta> (take m x)) \<le> val (a x)"
                using P F0[of x] by (metis IntE)               
              thus "x \<in> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
                using P unfolding S_def T_def assms  by blast 
            qed
            show "F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)} \<subseteq> F (j, s, t) \<inter> T"
            proof fix x assume P : "x \<in> F (j, s, t) \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
              then have P0: "val (\<eta> (take m x) \<ominus> (c x)) \<le> val (a x)"
                using F0 by (metis (no_types, lifting) Int_Collect)
              have P1: "x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>) \<and> ord (\<eta> (take m x)) = ord (c x) + i \<and>  c x \<in> nonzero Q\<^sub>p"
                using P unfolding F_def by blast 
              have P2: "val (\<eta> (take m x)) = ord (\<eta> (take m x))"
                using P \<eta>_nonzero  take_closed' DL_2_4_2 val_ord by blast
              have P3: "val (c x) = ord (c x)"
                using P1 val_ord by blast
              have "x \<in> T"
                apply(rule T_memI) 
                using P apply blast 
                using P unfolding F_def using P2 P3  val_ord \<eta>_nonzero P1 plus_eint_simps(1) apply presburger
                using P F0 P0 by linarith
              thus "x \<in> F (j, s, t) \<inter> T"
                using P by blast 
            qed
          qed 
          have F5: "is_semialgebraic (m+l) {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). val (\<eta> (take m x)) \<le> val (a x)}"
            using assms fact_i' by blast
          have F6: "is_semialgebraic (m+l) (F (j, s, t))"
          proof-
            obtain F0 where F0_def: "F0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and> ord (\<eta> (take m x)) = ord (c x) + i }"
              by blast 
            obtain F1 where F1_def: "F1 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ord (c x) mod n = j}"
              by blast 
            obtain F2 where F2_def: "F2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>). c x \<in> nonzero Q\<^sub>p \<and>  ac N (c x) = s }"
              by blast
            obtain F3 where F3_def: "F3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+l\<^esup>).  ac N (\<eta> (take m x)) = t }"
              by blast
            have 00: "is_semialgebraic (m+l) F0"
              unfolding F0_def   using assms fact_i_take[of c l i] by blast               
            have 01: "is_semialgebraic (m+l) F1"
              unfolding F1_def using assms ord_congruence_set_SA_function[of n c m l j] DL_2_4_2 n_def 
              by linarith              
            have 02: "is_semialgebraic (m+l) F2"
              unfolding F2_def using assms ac_cong_set_SA[of N s c m  l] jst_def \<open>0 < N\<close>
                    denef_lemma_2_4.DL_2_4_2 denef_lemma_2_4_axioms by blast
            have 03: "is_semialgebraic (m+l) F3"
              unfolding F3_def using fact_ii'[of N t l] \<open>0 < N\<close> jst_def by blast
            have 04: "F (j,s,t) =  {x \<in> carrier (Q\<^sub>p\<^bsup>m + l\<^esup>). ord (\<eta> (take m x)) = ord (c x) + i \<and> c x \<in> nonzero Q\<^sub>p \<and> ord (c x) mod int n = j \<and> ac N (c x) = s \<and> ac N (\<eta> (take m x)) = t}"
              unfolding F_def by blast 
            have "F (j, s, t) = F0 \<inter>F1 \<inter> F2 \<inter>F3"
              unfolding 04 F0_def F1_def F2_def F3_def by blast 
            thus ?thesis using 00 01 02 03 intersection_is_semialg  
              by simp
          qed
          then show ?thesis using F4 F5 
            by (metis (no_types, lifting) inf_commute intersection_is_semialg)
        qed
      qed
      have F_semialg: "\<And>ps . ps \<in> ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))
                    \<Longrightarrow> is_semialgebraic (m+l) (T \<inter> F ps)"
        using F_semialg by blast
      show "is_semialgebraic (m + l) (S \<inter> near_center_set l i c)"
        using F_semialg finite F_covers 
              finite_union_is_semialgebraic[of "(\<lambda> ps. T \<inter> F ps)` ({0..< int n}\<times>Units (Zp_res_ring N) \<times>Units (Zp_res_ring N))" "m+l" ]  
        by (metis T_def finite_imageI image_subsetI is_semialgebraicE)
    qed
  qed
  thus ?thesis unfolding S_def by auto 
qed

lemma SA_poly_to_SA_fun_minus:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "g \<in> carrier (UP (SA m))"
  shows "SA_poly_to_SA_fun m (f \<ominus>\<^bsub>UP (SA m)\<^esub> g) = 
              SA_poly_to_SA_fun m f \<ominus>\<^bsub>SA (Suc m)\<^esub> SA_poly_to_SA_fun m g"
  apply(rule ring_hom_minus)
  apply (simp add: SA_is_ring)
  using SA_poly_to_SA_fun_ring_hom apply blast
  by(rule assms, rule assms)

text\<open>This polynomial is necessary to apply the proof template laid out in \texttt{SA\_fun\_test}. 
$\eta$ will clearly be a root of the polynomial by the construction of $\eta$.\<close>
definition kth_pow_poly where 
"kth_pow_poly = up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k \<ominus>\<^bsub>UP (SA m)\<^esub> up_ring.monom (UP (SA m))  \<xi>_1 0"

lemma kth_pow_poly_closed:
"kth_pow_poly \<in> carrier (UP (SA m))"
    unfolding kth_pow_poly_def 
        by (meson R.one_closed UPSA.P.cring_simprules(4) UPSA.is_UP_monomE(1) UPSA.is_UP_monomI \<xi>_1_closed)

lemma kth_pow_poly_deg:
"deg (SA m) kth_pow_poly = k"
proof-
  have lt: "up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k \<in> carrier (UP (SA m))"
    using UPSA.is_UP_monomE(1) UPSA.monom_is_UP_monom(2) by blast
  have lt_deg: "deg (SA m) (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) = k"
    using SA_one_not_zero UPSA.deg_monom by blast
  have kth_pow_poly_deg: "deg (SA m) (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) = deg (SA m)  kth_pow_poly"
    apply(rule UPSA.deg_diff_by_const'[of _ _ \<xi>_1 ]) unfolding kth_pow_poly_def 
  using lt apply blast
  using \<xi>_1_closed apply blast
  by blast
  thus deg_kth_pow_poly: "deg (SA m) kth_pow_poly = k"
  unfolding lt_deg kth_pow_poly_def by auto  
qed

lemma kth_pow_poly_deg_bound:
"deg (SA m) kth_pow_poly \<le> Suc d"
  unfolding kth_pow_poly_deg 
  by (simp add: DL_2_4_1) 

lemma kth_pow_poly_eval:
"\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_SA_fun m kth_pow_poly (\<eta> x # x) = \<zero>"
proof fix x assume A': "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    have \<eta>_x_closed: "\<eta> x \<in> carrier Q\<^sub>p"
      by (simp add: A' \<eta>_characterization) 
    have 00: "\<eta> x [^]k = \<xi>_1 x"
      using A' \<eta>_characterization[of x] 
      by linarith
    have 01: "(\<eta> x # x) \<in> carrier (Q\<^sub>p\<^bsup>m+1\<^esup>)"
      using A' \<eta>_x_closed by (meson cartesian_power_cons) 
    have 02: "SA_poly_to_SA_fun m kth_pow_poly  = SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k)  \<ominus>\<^bsub>SA (Suc m)\<^esub> 
                                            SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<xi>_1 0)"
      unfolding kth_pow_poly_def apply(rule SA_poly_to_SA_fun_minus)
      using \<xi>_1_closed by auto 
    hence 03: "SA_poly_to_SA_fun m kth_pow_poly (\<eta> x # x) = SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) (\<eta> x # x)
                                                  \<ominus> SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<xi>_1 0) (\<eta> x # x)"
      using 02 01 
      by (simp add: SA_minus_eval SA_poly_to_SA_fun_monom_closed \<xi>_1_closed) 
    have 04: "SA_poly_to_SA_fun m kth_pow_poly (\<eta> x # x) =  \<eta> x [^] k   \<ominus> \<xi>_1 x"
    proof-
      have "SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) (\<eta> x # x) = (\<one>\<^bsub>SA m\<^esub> x) \<otimes> \<eta> x [^] k"
        using A' SA_poly_to_SA_fun_monom' by (simp add: \<eta>_x_closed) 
      hence 040: "SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) (\<eta> x # x) = \<eta> x [^] k"
        using A' "00" Qp.l_one Qp.nonzero_memE(1) SA_oneE \<xi>_1_nonzero by presburger
      have 0410: "SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<xi>_1 0) (\<eta> x # x) = \<xi>_1 x \<otimes> \<eta> x [^] (0::nat)"
        apply(rule SA_poly_to_SA_fun_monom') 
        using \<xi>_1_closed apply blast
        using A' apply blast
        using A' 
        by (simp add: \<eta>_x_closed)        
      hence 041: "SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<xi>_1 0) (\<eta> x # x) = \<xi>_1 x"
        using A'  
        by (metis "00" "040" Group.nat_pow_0 Qp.nat_pow_comm SA_oneE \<eta>_x_closed \<open>SA_poly_to_SA_fun m (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) (\<eta> x # x) = \<one>\<^bsub>SA m\<^esub> x \<otimes> \<eta> x [^] k\<close>) 
      show ?thesis unfolding 03 040 041 by blast
    qed
    thus 05: "SA_poly_to_SA_fun m kth_pow_poly (\<eta> x # x) =  \<zero>"
      unfolding 00 
      by (metis "00" Qp.nat_pow_closed Qp.r_right_minus_eq \<eta>_x_closed)       
qed

lemma kth_pow_poly_lcf:
"kth_pow_poly (deg (SA m) kth_pow_poly) \<in> Units (SA m)"
proof- 
  have 0620: "kth_pow_poly k = (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) k \<ominus>\<^bsub>SA m\<^esub> up_ring.monom (UP (SA m)) \<xi>_1 0  k"
    unfolding kth_pow_poly_def 
    by (meson R.one_closed UPSA.cfs_minus UPSA.is_UP_monomE(1) UPSA.is_UP_monomI \<xi>_1_characterization) 
  have 0621: "up_ring.monom (UP (SA m)) \<xi>_1 0 k = \<zero>\<^bsub>SA m\<^esub>"
    using UPSA.cfs_monom[of "\<xi>_1" m 0 k] \<xi>_1_closed DL_2_4_0 by auto   
  hence "kth_pow_poly k = (up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> k) k"
    unfolding 0620 0621 a_minus_def 
    using UPSA.cfs_monom by force 
  hence "kth_pow_poly k = \<one>\<^bsub>SA m\<^esub>"
    using R.one_closed UPSA.cfs_monom by presburger
  thus ?thesis 
    using R.Units_one_closed unfolding kth_pow_poly_deg by presburger
qed

lemma \<eta>_in_function_ring:
"\<eta> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
  apply(rule Qp.function_ring_car_memI)
  using \<eta>_closed \<eta>_def kth_rt_def by auto 
  
lemma denef_lemma_2_4:
"\<eta> \<in> carrier (SA m)"
proof(rule SA_fun_test[of _ kth_pow_poly])
  show  "deg (SA m) kth_pow_poly \<le> Suc d"
        "0 < deg (SA m) kth_pow_poly"
        "kth_pow_poly \<in> carrier (UP (SA m))"
        "\<eta> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
        "kth_pow_poly (deg (SA m) kth_pow_poly) \<in> Units (SA m)"
        "\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_SA_fun m kth_pow_poly (\<eta> x # x) = \<zero>"
    using DL_2_4_1 DL_2_4_0 kth_pow_poly_closed kth_pow_poly_lcf 
          kth_pow_poly_deg \<eta>_in_function_ring kth_pow_poly_eval by auto
  show "\<And>k c a.
       c \<in> carrier (SA (m + k)) \<Longrightarrow>
       a \<in> carrier (SA (m + k)) \<Longrightarrow>
       is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<eta> (take m x) \<ominus> c x) \<le> val (a x)}"
    by(intro eta_ord_bound_set_semialg, auto)
  show "\<And>k c \<alpha> n.
       c \<in> carrier (SA (m + k)) \<Longrightarrow>
       \<alpha> \<in> carrier Q\<^sub>p \<Longrightarrow>
       0 < n \<Longrightarrow> 
       is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<eta> (take m x) \<ominus> c x \<in> pow_res n \<alpha>}"  
    by(intro eta_minus_c_pow_res_set_semialg, auto)
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Removing Lemma 2.4 from its Proof Locale\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>In this section we prove Lemma 2.4 in the context the \texttt{padic\_field} locale. We also 
derive two related versions of the lemma which will be useful for the proof of Macintyre's Theorem. 
In the original version, we show that if a semialgebraic function $\xi$ always has a valuation which 
is a multiple of $k$, then we can find a function whose valuation is always $val(\xi)/k$. In general 
we can always find a function whose valuation is given by the floor or ceiling function applied to 
$val(\xi)/k$, even in the case where this quantity is not itself an integer. \<close>
context padic_fields
begin


lemma denef_lemma_2_4: 
  assumes "denef_II p d"
  assumes DL_2_4_0: "(k::nat) \<ge> 1" 
  assumes DL_2_4_1: "k \<le> Suc d"
  assumes DL_2_4_3: "\<xi> \<in> carrier (SA m)"
  assumes DL_2_4_4: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<xi> x \<noteq> \<zero>"
  assumes DL_2_4_5: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<xi> x) mod k = 0"
  shows "\<exists> \<eta> \<in> Units (SA m). (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). k* ord(\<eta> x) = ord (\<xi> x))"
proof(cases "m = 0")
  case True
  then obtain c where c_def: "c \<in> carrier Q\<^sub>p \<and> \<xi> = Qp_const 0 c"
    using car_SA_0_mem_imp_const assms(4) by blast
  have 0: "c \<noteq> \<zero>"
    using DL_2_4_4 c_def unfolding True  
    by (metis function_ring_defs(5) function_zero_eval function_zero_is_constant Qp_2I True assms(5) local.take_closed zero_le)
  have 1: "c = \<xi> []"
    using c_def 
    by (metis constant_functionE cartesian_power_car_memI' less_nat_zero_code list.size(3))
  have 2: "ord c mod k = 0"
    using c_def[of ] 0 assms(5)[of "[]"] assms(6)[of "[]"] 
    unfolding True constant_function_def Qp_zero_carrier    
    using "1" by fastforce
  obtain l where l_def: "ord c = l*int k"
    using 2 mod_zeroE[of "ord c" k] by metis   
  obtain \<eta> where \<eta>_def: "\<eta> = Qp_const 0 (\<pp>[^]l)"
    by blast 
  have \<eta>_closed: "\<eta> \<in> carrier (SA m)"
    unfolding True using \<eta>_def  
    by (metis constant_function_closed SA_zero_is_function_ring p_intpow_closed(1))
  have 3: "\<pp>[^]l \<noteq> \<zero>"
    using Qp.not_nonzero_memI p_intpow_closed(2) by blast
  have \<eta>_unit: "\<eta> \<in> Units (SA m)"
    apply(rule SA_Units_memI)
    using \<eta>_closed apply blast 
    unfolding \<eta>_def constant_function_def restrict_def True
    using "3" by presburger   
  have 4: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<eta> x) = l"
    unfolding \<eta>_def  True 
    using Qp_constE ord_p_pow_int p_intpow_closed(1) by presburger
  have  "\<eta>\<in>Units (SA m) \<and>( \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) = ord (\<xi> x))"
    using 4 \<eta>_unit l_def \<eta>_def unfolding True  1 Qp_zero_carrier 
    by (metis empty_iff insert_iff mult_of_nat_commute)
  then show ?thesis 
    by blast  
next
  case F0:  False
  then have m_pos: "m > 0"
    by blast 
  show ?thesis 
  proof(cases "k = 1")
    case True
    have \<xi>_unit: "\<xi> \<in> Units (SA m)"
      apply(rule SA_Units_memI)
       apply (simp add: assms(4))
      using assms(5) by blast
    hence "\<xi> \<in> Units (SA m) \<and> (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). k* ord(\<xi> x) = ord (\<xi> x))"
      unfolding True
    by (metis Num.of_nat_simps(2) more_arith_simps(5)) 
      then show ?thesis by blast 
  next
    case False
    then have k_bound: "k \<ge> 2"
      using assms by linarith
    obtain \<eta> where \<eta>_def: "\<eta>  = denef_lemma_2_4.\<eta> p \<xi> k m"
      by blast 
    have 0: "denef_lemma_2_4 p d \<xi> k m"
      apply(rule denef_lemma_2_4.intro)
      using assms  apply blast 
      unfolding denef_lemma_2_4_axioms_def using k_bound m_pos assms 
      unfolding Zp_def Q\<^sub>p_def 
      by blast
    have \<eta>_closed: "\<eta> \<in> carrier (SA m)"
      using \<eta>_def 0 denef_lemma_2_4.denef_lemma_2_4 by blast
    have \<eta>_ord: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> k* ord (\<eta> x) = ord (\<xi> x)"
      using \<eta>_def 0 denef_lemma_2_4.\<eta>_ord[of p d \<xi> k m] unfolding Q\<^sub>p_def Zp_def 
      by blast
    have \<eta>_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<eta> x \<noteq>  \<zero>"
      using \<eta>_def 0  denef_lemma_2_4.\<eta>_nonzero[of p d \<xi> k m] unfolding Q\<^sub>p_def Zp_def 
      using Q\<^sub>p_def Qp.nonzero_memE(2) Zp_def by blast
    have \<eta>_Units: "\<eta> \<in> Units (SA m)"
      apply(rule SA_Units_memI)
      using \<eta>_closed apply blast 
      using \<eta>_nonzero by blast 
    show "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) = ord (\<xi> x)"
      using \<eta>_Units \<eta>_ord by blast 
  qed
qed

text\<open>In this lemma, the function $\eta$ satisfies $ord (\eta x) = floor(ord (\phi x)/k)$ for all x\<close>
lemma denef_lemma_2_4_floor: 
  assumes "denef_II p d"
  assumes "k \<ge> 1"
  assumes "k \<le> Suc d"
  assumes "\<phi> \<in> Units (SA m)"
  shows "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x)"
proof- 
  have \<phi>_closed: "\<phi> \<in> carrier (SA m)"
    using assms by blast
  obtain F where F_def: "F = (\<lambda>i. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<phi> x) mod k = int i })"
    by blast 
  have F_semialg: "\<And>i. is_semialgebraic m (F i)"
  proof- fix i::nat
    have 0: "is_semialgebraic (m + 0) {x \<in> carrier (Q\<^sub>p\<^bsup>m + 0\<^esup>). \<phi> x \<in> nonzero Q\<^sub>p \<and> ord (\<phi> x) mod int k = i}"
      apply(rule ord_congruence_set_SA_function[of k \<phi> m 0 i])
      using assms apply(presburger )
      using assms Nat.add_0_right SA_Units_closed by presburger
    have 1: "F i = {x \<in> carrier (Q\<^sub>p\<^bsup>m + 0\<^esup>). \<phi> x \<in> nonzero Q\<^sub>p \<and> ord (\<phi> x) mod int k = int i}"
      apply(rule equalityI')
      unfolding F_def mem_Collect_eq using assms 
      apply (metis SA_Units_nonzero arith_extra_simps(6))
      by (metis arith_extra_simps(6))     
    thus "is_semialgebraic m (F i)"
      unfolding F_def using assms 
      by (metis (no_types, lifting) "0" arith_simps(50))
  qed
  have P0: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<pp>[^]k)) \<in> carrier (SA m)"
    by(rule constant_fun_closed, rule p_natpow_closed(1))
  have P1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<pp>[^]k)) x = \<pp>[^]k"
    using constant_functionE p_natpow_closed(1) by blast
  have P2: "\<And> i. F i \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    unfolding F_def by blast 
  obtain G0 where G0_def: "G0 = (\<lambda>i. fun_glue m (F i) (\<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi>) (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<pp>[^]k)))"
    by blast 
  have \<phi>_sm_closed: "\<And>i. \<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi> \<in> carrier (SA m)"
    by(rule SA_smult_closed, rule \<phi>_closed, rule p_intpow_closed)
  have \<phi>_sm_eval: "\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (\<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi>)  x =  \<pp>[^](- int i) \<otimes> \<phi> x"
    using SA_smult_formula \<phi>_closed p_intpow_closed(1) by blast
  have \<phi>_sm_nonzero: "\<And> i x.  x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> (\<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi>)  x \<in> nonzero Q\<^sub>p"
    apply(rule nonzero_memI)
    using assms \<phi>_sm_eval apply (meson SA_car_closed \<phi>_sm_closed)
    using assms \<phi>_sm_eval 
    by (metis Qp.integral Qp.l_null Qp.one_not_zero SA_Units_memE' SA_car_closed \<phi>_closed p_intpow_closed(1) p_intpow_inv)
  have \<phi>_sm_ord: "\<And> i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord ((\<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi>)  x) = ord (\<phi> x) - i"
    using \<phi>_sm_eval assms ord_mult Qp_int_pow_nonzero SA_Units_nonzero ord_p_pow_int p_nonzero by presburger
  have G0_closed: "\<And>i. G0 i \<in> carrier (SA m)"
    unfolding G0_def 
    by(rule fun_glue_closed, rule \<phi>_sm_closed, rule P0, rule F_semialg) 
  have G0_eval_1: "\<And> (i::nat) x. x \<in> F i \<Longrightarrow> G0 i x = \<pp>[^](- int i) \<otimes> \<phi> x"
  proof- fix i::nat fix x assume A: "x \<in>  F i"
    have 0: "G0 i x = (\<pp>[^](- int i)\<odot>\<^bsub>SA m\<^esub>\<phi>) x"
      unfolding G0_def by(rule fun_glueE, rule \<phi>_sm_closed, rule P0, rule P2, rule A)
    show "G0 i x = \<pp>[^](- int i) \<otimes> \<phi> x"
      unfolding 0 apply(rule \<phi>_sm_eval)
      using A unfolding F_def by blast
  qed
  have G0_eval_2: "\<And> (i::nat) x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> F i \<Longrightarrow> G0 i x = \<pp>[^]k"
  proof- fix i::nat fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "x \<notin> F i"
    have Q0: "G0 i x = constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<pp> [^] k) x"
      unfolding G0_def apply(rule fun_glueE', rule \<phi>_sm_closed, rule P0, rule P2)
      using A by blast 
    show "G0 i x = \<pp>[^]k"
      unfolding G0_def 
      using fun_glueE'[of \<phi> m "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<pp>[^]k)" "F i" x] 
          P0 P1[of x] P2 \<phi>_closed A(1) G0_def Q0 by blast
  qed
  have P3: "(\<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> G0 i x \<noteq> \<zero>)"
  proof- fix i x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    show "G0 i x \<noteq> \<zero>"
      apply(cases "x \<in> F i")
      using G0_eval_1[of x i] \<phi>_sm_nonzero[of x i] 
      apply (metis A Qp.nonzero_memE(2) \<phi>_sm_eval)
      using G0_eval_2[of x i] A Qp.nonzero_memE(2) Qp_nat_pow_nonzero p_nonzero by presburger
  qed
  have P4: " \<And>i x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (G0 i x) mod int k = 0"
  proof- fix i x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    show "ord (G0 i x) mod int k = 0"
    proof(cases "x \<in> F i")
      case True
      have T0: "ord (G0 i x) = ord (\<phi> x) - i"
        using True G0_eval_1 \<phi>_sm_ord  A \<phi>_sm_eval by metis 
      show ?thesis 
        using True unfolding T0 F_def mem_Collect_eq 
        by (metis cancel_comm_monoid_add_class.diff_cancel mod_0 mod_diff_right_eq)
    next
      case False
      have F0: "G0 i x = \<pp>[^]k"
        by(rule G0_eval_2, rule A, rule False)
      show ?thesis unfolding F0 
        using ord_p_pow_nat by presburger  
    qed
  qed 
  have P5: "\<And>i. \<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) = ord (G0 i x)"
    by(rule denef_lemma_2_4[of d k _  m], rule assms, rule assms, rule assms, rule G0_closed, rule P3, blast, rule P4)
  obtain G where G_def: "G = (\<lambda>i. (SOME \<eta>. \<eta> \<in> Units (SA m) \<and>  (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) = ord (G0 i x))))"
    by blast 
  have GE: "\<And>i. G i \<in> Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (G i x) = ord (G0 i x))"
  proof- fix i
    obtain \<eta> where \<eta>_def: "\<eta> \<in> Units (SA m) \<and>  (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) = ord (G0 i x))"
      using P5 by blast 
    show "G i \<in> Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (G i x) = ord (G0 i x))"
      apply(rule SomeE[of "G i" _ \<eta>]) using G_def apply blast by(rule \<eta>_def)
  qed
  obtain Fs where Fs_def: "Fs = {S \<in> (F ` {..<k}). S \<noteq> {}}"
    by blast 
  have Fs_covers: "\<Union> Fs = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    apply(rule equalityI') unfolding Fs_def F_def apply blast
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    obtain i where i_def: "i = ord (\<phi> x) mod int k"
      by blast 
    have i_nonneg: "i \<ge> 0"
    proof- 
      have 0: "\<And>i k::int. k \<ge> 1 \<Longrightarrow> i mod k \<ge> 0"
      proof- fix i::int fix  k::int assume A: "k \<ge> 1"
        show "i mod k \<ge> 0"
          using A Euclidean_Division.pos_mod_sign int_one_le_iff_zero_less by blast
      qed
      show ?thesis unfolding i_def apply(rule 0) 
        using assms 
        by linarith
    qed      
    have x_in: "x \<in> F(nat i)"
      unfolding F_def using i_def i_nonneg 
      by (metis (mono_tags, lifting) A mem_Collect_eq nat_0_le)
    have 0: "nat i < k"
      unfolding i_def 
      by (metis assms(2) gr0I i_def nat_eq_iff nat_less_iff of_nat_0_less_iff pos_mod_conj rel_simps(45))
    have Fi_in_Fs: "F (nat i) \<in> Fs"
      unfolding Fs_def using A x_in unfolding mem_Collect_eq  
      using "0" by blast
    thus "x \<in> \<Union> {S \<in> (\<lambda>i. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). ord (\<phi> x) mod int k = int i}) ` {..<k}. S \<noteq> {}}"
      using x_in unfolding F_def Fs_def 
      by blast
  qed
  have Fs_inj: "\<And> i j. i \<noteq> j \<Longrightarrow> F i \<in> Fs \<Longrightarrow> F i \<noteq> F j"
  proof fix i j assume A: "i \<noteq> j" "F i \<in> Fs" "F i = F j"
    obtain x where x_def: "x \<in> F i"
      using A(2) unfolding Fs_def by blast 
    have 0: "x \<in> F j"
      using x_def unfolding A(3) by blast 
    show False using x_def A(1) 0 unfolding F_def mem_Collect_eq 
      by linarith
  qed
  obtain F_inv where F_inv_def: "F_inv = (\<lambda>s. (THE i. s = F i))"
    by blast 
  have F_invE: "\<And>s. s \<in> Fs \<Longrightarrow> F( F_inv s) = s"
    using Fs_inj unfolding F_inv_def 
    by (smt Fs_def The_unsafe_def image_iff mem_Collect_eq the1I2)
  have F_inv_in: "\<And>s. s \<in> Fs \<Longrightarrow> F_inv s \<in> {..<k}"
    using F_invE Fs_inj unfolding Fs_def 
    by (metis (no_types, lifting) imageE mem_Collect_eq)
  have Fs_disjoint: "\<And>x A B. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)  \<Longrightarrow> A \<in> Fs \<Longrightarrow> B \<in> Fs \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}"
  proof- fix x A B assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "A \<in> Fs" "B \<in> Fs" "A \<noteq> B"
    obtain i where i_def: "i = F_inv A"
      by blast 
    obtain j where j_def: "j = F_inv B"
      by blast 
    have i0: "F i = A"
      unfolding i_def by(rule F_invE, rule A)
    have j0: "F j = B"
      unfolding j_def by(rule F_invE, rule A)
    have i_neq_j: "i \<noteq> j"
      using A i0 j0 by blast 
    hence 0: "int i \<noteq> int j"
      using nat_int_comparison(1) by blast
    have i1: "F i \<noteq> {}"
      unfolding i0 using A unfolding Fs_def by blast 
    have 1: "F i \<inter> F j = {}" 
      apply(rule equalityI')
      unfolding F_def using 0 
       apply (metis (mono_tags) mem_Collect_eq mem_Collect_inter)
      by blast 
    show "A \<inter> B = {}"
      using 1 unfolding i0 j0 by blast 
  qed
  obtain G1 where G1_def: "G1 = G \<circ> F_inv"
    by blast
  obtain \<eta> where \<eta>_def: "\<eta> = parametric_fun_glue m Fs G1"
    by blast 
  have \<eta>_eval: "\<And>x s. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> s \<in> Fs \<Longrightarrow> x \<in> s \<Longrightarrow> \<eta> x = G1 s x"
    unfolding \<eta>_def 
    apply(rule parametric_fun_glue_formula, rule is_partitionI, rule disjointI)
    using Fs_disjoint apply blast
    using Fs_covers by(blast, blast, blast)
  have \<eta>_closed: "\<eta> \<in> carrier (SA m)"
    unfolding \<eta>_def apply(rule parametric_fun_glue_is_SA)
    using Fs_def 
    apply (metis (mono_tags) Collect_mem_eq finite_Collect_conjI finite_imageI finite_lessThan)
    apply(rule is_partitionI, rule disjointI)
    using Fs_disjoint 
    using Fs_covers apply blast
    using Fs_covers apply blast
    unfolding G1_def comp_apply using GE apply blast
    unfolding Fs_def using F_semialg by blast 
  have \<eta>_eval': "\<And>i x. x \<in> F i \<Longrightarrow> \<eta> x = G i x"
  proof- fix i x assume A: "x \<in> F i"
    have 1: "ord (\<phi> x) mod k = i"
      using A unfolding F_def mem_Collect_eq by blast 
    have i_nonneg: "i \<ge> 0"
    proof- 
      have 0: "\<And>i k::int. k \<ge> 1 \<Longrightarrow> i mod k \<ge> 0"
      proof- fix i::int fix  k::int assume A: "k \<ge> 1"
        show "i mod k \<ge> 0"
          using A Euclidean_Division.pos_mod_sign int_one_le_iff_zero_less by blast
      qed
      show ?thesis using 1 
        using assms 
        by linarith
    qed      
    have 0: "i < k"
      using 1
     by (smt Euclidean_Division.pos_mod_bound assms(2) of_nat_0_less_iff of_nat_less_imp_less of_nat_mono zero_less_one)
    have 1: "F i \<in> Fs"
      unfolding Fs_def using 0 A by blast 
    have 2: "F_inv (F i) = i"
      using F_invE[of "F i"] 1 Fs_inj by metis
    have 3: "\<eta> x = G1 (F i) x"
      apply(rule \<eta>_eval)
      using A F_def apply blast
      by(rule 1, rule A)
    show "\<eta> x = G i x"
      unfolding 3 G1_def comp_apply 2 by blast 
  qed
  have P6: " \<And>i x. x \<in> F i \<Longrightarrow> ord (G0 i x) = ord (\<phi> x) - i"
  proof- fix i x assume A: "x \<in> F i"
  show "ord (G0 i x) = ord (\<phi> x) - i"
        using A G0_eval_1 \<phi>_sm_ord  A \<phi>_sm_eval F_def 
        by (metis (no_types, lifting) mem_Collect_eq)
  qed
  have P7: "\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + ord (\<phi> x) mod int k = ord (\<phi> x)"
  proof fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    obtain j where j_def: "j = ord (\<phi> x) mod k"
      by blast 
    have j_pos: "j \<ge> 0"
      unfolding j_def apply(rule Euclidean_Division.pos_mod_sign) using assms 
      by linarith
    obtain i where i_def: "i = nat j"
      by blast
    have ij: "int i = j"
      unfolding i_def using j_pos 
      by simp
    have 0: "x \<in> F i"
      unfolding F_def mem_Collect_eq using A j_def unfolding ij by blast 
    have 1: "\<eta> x = G i x"
      by(rule \<eta>_eval', rule 0)
    have 2: "k*ord(\<eta> x) = ord (G0 i x)"
      unfolding 1 using GE[of i] A by blast 
    have 3: "k*ord(\<eta> x) = ord (\<phi> x) - i"
      unfolding 2 by(rule P6, rule 0)
    show "int k * ord (\<eta> x) + ord (\<phi> x) mod int k = ord (\<phi> x)"
      unfolding 3 ij j_def 
      using diff_add_cancel by blast
  qed
  have \<eta>_Units: "\<eta> \<in> Units (SA m)"
  proof(rule SA_Units_memI, rule \<eta>_closed)
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
   obtain j where j_def: "j = ord (\<phi> x) mod k"
      by blast 
    have j_pos: "j \<ge> 0"
      unfolding j_def apply(rule Euclidean_Division.pos_mod_sign) using assms 
      by linarith
    obtain i where i_def: "i = nat j"
      by blast
    have ij: "int i = j"
      unfolding i_def using j_pos 
      by simp
    have 0: "x \<in> F i"
      unfolding F_def mem_Collect_eq using A j_def unfolding ij by blast 
    have 1: "\<eta> x = G i x"
      by(rule \<eta>_eval', rule 0)
    show "\<eta> x \<noteq> \<zero>"
      unfolding 1
      using A GE[of i]SA_Units_nonzero unfolding nonzero_def by blast 
  qed
  show ?thesis using P7 \<eta>_Units by blast 
qed

text\<open>In this lemma, the function $\eta$ satisfies $ord(\eta x) = ceiling(ord (\phi x)/k)$ for all x\<close>
lemma denef_lemma_2_4_ceiling: 
  assumes "denef_II p d"
  assumes "k \<ge> 1"
  assumes "k \<le> Suc d"
  assumes "\<phi> \<in> Units (SA m)"
  shows "\<exists>\<eta>\<in>Units (SA m). \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x) + k"
proof-
  obtain \<psi> where \<psi>_def: "\<psi> = (\<pp>[^]k)\<odot>\<^bsub>SA m\<^esub> \<phi>"
    by blast 
  have \<psi>_unit: "\<psi> \<in> Units (SA m)"
    apply(rule SA_Units_memI ) 
    unfolding \<psi>_def apply(rule SA_smult_closed)
    using assms  apply blast
     apply blast
    using assms SA_Units_nonzero[of \<phi> m] unfolding nonzero_def mem_Collect_eq 
    using Qp.int_inc_closed Qp.integral_iff Qp.nonzero_memE(2) Qp.nonzero_pow_nonzero SA_Units_closed SA_smult_formula p_natpow_closed(1) p_nonzero by presburger
  obtain \<eta> where \<eta>_def: "\<eta>\<in>Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<psi> x)mod k) = ord (\<psi> x))"
    using denef_lemma_2_4_floor[of d k \<psi> m]
          assms \<psi>_unit by blast 
  have \<psi>_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<psi> x = \<pp>[^]k \<otimes> \<phi> x"
    unfolding \<psi>_def using assms SA_smult_formula p_natpow_closed(1) by blast
  have 0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<psi> x) = ord (\<phi> x) + k"
    using \<psi>_eval assms ord_mult SA_Units_nonzero[of \<phi> m] Qp_nat_pow_nonzero ord_p_pow_nat p_nonzero by presburger
  have 1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (\<psi> x) mod k = ord (\<phi> x) mod k"
    using 0  by (metis mod_add_self2)
  have 2: "\<eta>\<in>Units (SA m) \<and> (\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<phi> x)mod k) = ord (\<phi> x) + k)"
    apply(rule conjI, rule conjE[of "\<eta>\<in>Units (SA m)" "(\<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). int k * ord (\<eta> x) + (ord (\<psi> x)mod k) = ord (\<psi> x))"], rule \<eta>_def, metis)
    using \<psi>_eval 0 1  by (metis \<eta>_def)
  thus ?thesis by blast 
qed

end
end



