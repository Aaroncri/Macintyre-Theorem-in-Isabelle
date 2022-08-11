theory Denef_Cell_Decomp_Theorem_I
  imports Denef_Lemma_2_4 Denef_Lemma_2_3 Cell_Normalization
          Cell_Decomp_Theorem_Helpers
begin

section\<open>The Proof of Cell Decomposition Theorem \texttt{I\_{d+1}} Assuming Theorems \texttt{I\_{d}}
         and \texttt{II\_{d}} \<close>

text\<open>Towards the inductive proofs of the cell decomposition theorems, this section shows that
     theorem \texttt{I\_{d+1}} follows from theorems \texttt{I\_{d}} and \texttt{II\_{d}}. The 
     overall proof proceeds by many successive refinements of cell decompositions until the desired 
     result holds on each cell. This means that we will have to frequently shift contexts to smaller
     and smaller cells with more precise properties holding on each. We have organized this data 
     into several different locales. Before getting into the main body of the proof, we prove some 
     miscellaneous facts that will be needed later.\<close>

context padic_fields
begin

lemma denef_cell_decomp_I_base:
"denef_I p 0"
proof fix m P assume A: "P \<in> carrier (UP (SA m))" "deg (SA m) P \<le> 0"
  then obtain a where a_def: "a \<in> carrier (SA m) \<and> P = up_ring.monom (UP (SA m)) a 0"
    using SA_is_cring[of m] UP_ring.deg_zero_impl_monom[of "SA m" P ] unfolding UP_ring_def   
    using SA_is_ring UP.coeff_closed by blast
  obtain \<C> where \<C>_def: "is_cell_condition \<C> \<and> arity \<C> = m\<and>  \<C> = Cond m (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_ray \<and>condition_to_set \<C> = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)" 
    using carrier_is_cell by blast
  obtain S where S_def: "S = {\<C>}"
    by blast 
  have 0: "is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    apply(rule is_cell_decompI)
        apply (simp add: S_def)
     apply(rule is_partitionI) unfolding S_def using \<C>_def 
        apply (metis (full_types) empty_iff image_empty image_insert insert_iff disjointI)
      using \<C>_def apply blast
      using \<C>_def apply blast 
       apply blast 
      by blast 
  have 1: " (\<forall>A\<in>S. SA_poly_ubounded p  m P (center A) (condition_to_set A) 0)"
    proof fix A assume A0: "A \<in> S"
      then have 10: "A = \<C>"
        unfolding S_def by blast 
      show "SA_poly_ubounded p m P (center A) (condition_to_set A) 0"
      proof(rule SA_poly_uboundedI[of _ _ _ _ ])
        show "P \<in> carrier (UP (SA m))"
          using A by blast 
        show "center A \<in> carrier (SA m)"
          unfolding 10 using \<C>_def 
          by (metis condition_decomp' is_cell_conditionE(2))
        show "condition_to_set A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using "0" A0 is_cell_decomp_subset by blast         
        show "\<And>x t i. t # x \<in> condition_to_set A \<Longrightarrow>
       val (SA_poly_to_Qp_poly m x P \<bullet> t) \<le> val (UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i \<bullet> t) + eint 0"
        proof- fix x t i
          assume A1: " t # x \<in> condition_to_set A"
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
            using A1 unfolding 10 using \<C>_def condition_to_set_memE'(1) by blast
          have t_closed: "t \<in> carrier Q\<^sub>p"
          proof-
            have "t = lead_coeff (t # x)"
              by simp
            thus ?thesis 
              using A1 unfolding 10 using cartesian_power_head[of "t#x" Q\<^sub>p m] \<C>_def 
              by metis
          qed
          have 11: "SA_poly_to_Qp_poly m x P = up_ring.monom (UP Q\<^sub>p) (a x) 0"
            using x_closed A a_def SA_poly_to_Qp_poly_monom[of x m a 0] 
            by blast
          have 12: "SA_poly_to_Qp_poly m x P \<bullet> t = a x"
            using t_closed a_def x_closed unfolding 11  
            using Qp.function_ring_car_memE SA_car_memE(2) UPQ.to_fun_const by blast
          show "val (SA_poly_to_Qp_poly m x P \<bullet> t) \<le> val (UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i \<bullet> t) + eint 0"
          proof(cases "i = 0")
            case True
            have l: "(X_poly_plus (SA m) \<zero>\<^bsub>SA m\<^esub>) = (X_poly (SA m))"
              unfolding X_poly_plus_def using SA_is_cring UP_cring_def 
              by (metis (no_types, lifting) SA_is_cring UP_cring.UP_cring UP_cring.X_closed UP_cring.add_nat_pow_monom cring.axioms(1) cring.cring_simprules(16) cring.cring_simprules(6) ring.nat_mult_zero to_polynomial_def)
            have T0: "taylor_expansion (SA m) \<zero>\<^bsub>SA m\<^esub> P 0 = a"
              using a_def SA_is_cring UP_cring.UP_cring[of "SA m"]
              unfolding l A taylor_expansion_def 
              by (metis A(1) A(2) SA_is_cring UP_cring.lcf_monom(1) UP_cring.X_sub UP_cring.intro le_zero_eq)
            have T000:"up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> 0 = \<one>\<^bsub>UP (SA m)\<^esub>"
              using SA_is_ring UP_ring.monom_one UP_ring_def by blast
            have T00: "X_poly_minus (SA m) \<zero>\<^bsub>SA m\<^esub> [^]\<^bsub>UP (SA m)\<^esub> (0::nat) = up_ring.monom (UP (SA m)) \<one>\<^bsub>SA m\<^esub> 0"
              using UP_cring.X_minus_closed[of "SA m" "\<zero>\<^bsub>SA m\<^esub>"] SA_is_cring[of m] UP_cring.UP_cring[of "SA m"]
              unfolding T000  UP_cring_def X_poly_minus_def  
              by (meson Group.nat_pow_0)
            have T1: "P =  a \<odot>\<^bsub>UP (SA m)\<^esub> X_poly_minus (SA m) \<zero>\<^bsub>SA m\<^esub> [^]\<^bsub>UP (SA m)\<^esub> (0::nat)"
              using a_def A SA_is_cring[of m] UP_cring.UP_cring[of "SA m"] UP_ring.monom_mult_smult[of "SA m"]
              unfolding T00 UP_cring_def UP_ring_def 
              by (metis SA_is_ring T000 UP_ring.monom_mult_is_smult UP_ring_def cring.cring_simprules(12) cring.cring_simprules(14) cring.cring_simprules(6))
            have T2: "UP_cring.taylor_term (SA m) \<zero>\<^bsub>SA m\<^esub> P i = P"
              using a_def A  UP_cring.taylor_term_def[of "SA m" "\<zero>\<^bsub>SA m\<^esub>" P i] 
              unfolding UP_cring_def T0 T1 True  
              by (metis SA_is_cring T0 a_def)              
            have T3: "UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i = up_ring.monom (UP Q\<^sub>p) (a x) 0"
              using  SA_poly_to_Qp_poly_comm_taylor_term[of P m "\<zero>\<^bsub>SA m\<^esub>" x i] \<C>_def unfolding T2 10 
              by (metis "11" A(1) center.simps is_cell_conditionE(2) x_closed)
            have "val (SA_poly_to_Qp_poly m x P \<bullet> t) = val (UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i \<bullet> t)"
              unfolding T3 12 using a_def x_closed t_closed UP_cring.to_fun_monom[of "Q\<^sub>p" "a x" t 0] 
              using "11" "12" by presburger
            thus "val (SA_poly_to_Qp_poly m x P \<bullet> t) \<le> val (UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i \<bullet> t) + eint 0"
            proof -
              have "(0::int) \<le> 0"
                by auto
              then show ?thesis
                by (metis \<open>val (SA_poly_to_Qp_poly m x P \<bullet> t) = val (UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i \<bullet> t)\<close> add.comm_neutral add.commute add_right_mono eint_ord_simps(1) zero_eint_def)
            qed
          next
            case False
            have F0: "UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
            proof-
              have "UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i
                    = UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x (up_ring.monom (UP (SA m)) a 0)) i"
                using a_def \<C>_def unfolding 10 using center.simps by presburger
              hence F0: "UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i
                    = UPQ.taylor_term \<zero> (up_ring.monom (UP Q\<^sub>p) (a x) 0) i"
                using SA_poly_to_Qp_poly_monom[of x m a 0] x_closed a_def SA_zeroE by metis 
              have "taylor_expansion Q\<^sub>p \<zero> (up_ring.monom (UP Q\<^sub>p) (a x) 0) = (up_ring.monom (UP Q\<^sub>p) (a x) 0)"
                unfolding taylor_expansion_def 
                using UPQ.sub_const[of _ "up_ring.monom (UP Q\<^sub>p) (a x) 0"] x_closed a_def 
                by (metis "11" "12" A(1) Qp.cring_simprules(2) SA_poly_to_Qp_poly_closed
                    UPQ.X_plus_closed UPQ.deg_const UPQ.sub_const UPQ.to_fun_closed t_closed)
              hence F1: "taylor_expansion Q\<^sub>p \<zero> (up_ring.monom (UP Q\<^sub>p) (a x) 0) i = \<zero>"
                using False UPQ.cfs_monom[of "a x" 0 i] a_def x_closed 
                by (metis "12" A(1) SA_poly_to_Qp_poly_closed UPQ.to_fun_closed t_closed)
              thus "UPQ.taylor_term (center A x) (SA_poly_to_Qp_poly m x P) i
                    = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
                using False F0 unfolding F1 UPQ.taylor_term_def 
                using Qp.zero_closed UPQ.X_poly_minus_nat_pow_closed UPQ.smult_l_null 
                      F1 UPQ.taylor_term_def by presburger                
            qed
            show ?thesis unfolding F0 using t_closed val_zero 
              by (metis UPQ.to_fun_zero add.right_neutral eint_ord_code(3) zero_eint_def)
          qed
        qed
      qed
  qed
  show "\<exists>S. is_cell_decomp m S (carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)) \<and>
               (\<forall>A\<in>S. \<exists>N. SA_poly_ubounded p m P (center A) (condition_to_set A) N)"
    using 0 1 Q\<^sub>p_def Zp_def by blast
qed

lemma cong_set_is_cell:
  assumes "is_semialgebraic m B"
  assumes "val ([k]\<cdot>\<one>) = 0"
  assumes "k < p^i"
  assumes "0 < k"
  shows "{x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> B \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = k}
          = condition_to_set (Cond m B (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^i)]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)"
proof
  show "{x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> B \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) i = k}
    \<subseteq> condition_to_set
        (Cond m B (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>)) (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p^i)] \<cdot> \<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    apply(rule subsetI)
    unfolding mem_Collect_eq condition_to_set.simps cell_def 
    apply(rule conjI) apply blast
    apply(rule conjI) apply blast
    apply(rule closed_interval_memI)
  proof-
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> tl x \<in> B \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = k"
    have hd_x_closed: "hd x \<in> carrier Q\<^sub>p"
      using A cartesian_power_head by blast
    have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A cartesian_power_tail by blast 
    have hd_x_inc: "\<iota> (to_Zp (hd x)) = hd x"
      using hd_x_closed A  by (metis Qp_val_ringI assms(2) to_Zp_inc val_of_int_inc)
    have 0: "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([i] \<cdot> \<one>) (tl x) = [i] \<cdot> \<one>"
      using tl_x_closed unfolding constant_function_def restrict_def by metis 
    have 1: "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x) = [k] \<cdot> \<one>"
      using tl_x_closed unfolding constant_function_def restrict_def by metis 
    have 2: "to_Zp (hd x) \<in> carrier Z\<^sub>p"
      using A hd_x_closed to_Zp_closed by blast
    have 3: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = k mod p^i"
      using assms Zp_int_inc_res by blast
    have 4: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = k"
      unfolding 3 using assms 
      by (smt mod_pos_pos_trivial)
    have 5: "(to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = 0"
      using 4 2 A Zp.int_inc_closed res_diff_zero_fact'' by presburger
    hence 6: "val_Zp (to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) \<ge> i"
      using "2" Zp.int_inc_closed res_diff_zero_fact(1) val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
    have 7: "val (\<iota>(to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)) \<ge> i"
      using 6 
      by (metis "2" Zp.minus_closed Zp_int_inc_closed val_of_inc)
    hence 8: "val (hd x \<ominus> [k]\<cdot>\<one>) \<ge> i"
      by (metis "2" Zp_int_inc_closed hd_x_inc inc_of_diff inc_of_int)
    have 9: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = [(p ^ i)] \<cdot> \<one>"
      using tl_x_closed Qp.int_inc_closed Qp_constE by blast
    hence 10: "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = val ([(p ^ i)] \<cdot> \<one>)"
      by  metis 
    have 11: "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = i"
      unfolding 10 
      by (metis Qp.int_nat_pow_rep int_pow_int val_p_int_pow)
    show "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x))
         \<le> val (lead_coeff x \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x))"
      unfolding 11 1 by(rule 8)
  next
    fix x assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> tl x \<in> B \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) i = k"
    then have "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      by (simp add: Qp_pow_ConsE(1))       
    hence "(\<zero>\<^bsub>SA m\<^esub> (tl x)) = \<zero>"
      using SA_zeroE by blast
    thus " val (lead_coeff x \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x)) \<le> val (\<zero>\<^bsub>SA m\<^esub> (tl x))"
      by (metis A constant_functionE Qp.cring_simprules(4) Qp.int_inc_closed Qp.int_inc_zero'
        Qp.int_mult_closed Qp.r_right_minus_eq Qp_isosceles Qp_pow_ConsE(2) \<open>tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)\<close>
        dist_nonempty' val_dist_sym val_of_int_inc val_ringI val_val_ring_prod')
  qed
  show "condition_to_set
     (Cond m B (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>)) (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>)) \<zero>\<^bsub>SA m\<^esub>
       closed_interval)
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> B \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) i = k}"
    unfolding condition_to_set.simps cell_def 
    apply(rule subsetI)
    unfolding mem_Collect_eq  apply(rule conjI, blast, rule conjI, blast)
  proof- 
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and>
         tl x \<in> B \<and>
         val (lead_coeff x \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x))
         \<in> I[val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) val (\<zero>\<^bsub>SA m\<^esub> (tl x))]"
    have 0: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = ([(p ^ i)] \<cdot> \<one>)"
      using assms A Qp.int_inc_closed Qp_constE Qp_pow_ConsE(1) by blast
    have 1: "val ([(p ^ i)] \<cdot> \<one>) = i"
      by (metis Qp.int_nat_pow_rep int_pow_int val_p_int_pow)
    have 2: "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = i"
      unfolding 0 1 by blast 
    have 3: "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x) = [k] \<cdot> \<one>"
      using assms A constant_functionE Qp.int_inc_closed Qp_pow_ConsE(1) by blast
    have 4: "val (hd x \<ominus> [k] \<cdot> \<one>) \<ge> i"
      using A unfolding closed_interval_def mem_Collect_eq 2 3 by blast 
    have 5: "i > 0"
    proof(rule ccontr)
      assume "\<not> i > 0"
      then have 0:"i = 0"
        by blast
      show False using assms unfolding 0 
        by (smt power.simps(1))
    qed
    hence 5: "eint i > 0"
      using eint_pow_int_is_pos of_nat_0_less_iff by blast
    have 6: "val (hd x \<ominus> [k] \<cdot> \<one>) > 0"
      by(rule less_le_trans[of _ "eint i"], rule 5, rule 4)
    have 7: "val (hd x \<ominus> [k] \<cdot> \<one>) > val ([k]\<cdot>\<one>)"
      unfolding assms by(rule 6)
    have hd_x_closed: "hd x \<in> carrier Q\<^sub>p"
      using A Qp_pow_ConsE(2) by blast
    hence "val (hd x) = val ([k]\<cdot>\<one>)"
      using 7 assms by (metis Qp.int_inc_closed ultrametric_equal_eq)
    hence  8: "val (hd x) = 0 "
      unfolding assms by blast 
    have 9: "to_Zp (hd x) \<in> carrier Z\<^sub>p"
      using A hd_x_closed to_Zp_closed by blast
    have 10: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = k mod p^i"
      using assms Zp_int_inc_res by blast
    have 11: "([k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = k"
      unfolding 10 using assms 
      by (smt mod_pos_pos_trivial)
    have 12: "(to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = to_Zp ((hd x) \<ominus> [k]\<cdot>\<one>)"
      using 4 8 hd_x_closed assms(2) to_Zp_minus[of "hd x" "[k] \<cdot> \<one>"] 
      by (metis Qp.int_inc_closed Zp.int_inc_closed inc_of_int inc_to_Zp val_of_int_inc val_ring_memI)
    have 13: "val_Zp (to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) \<ge> i"
    proof-
      have 130: "(hd x) \<ominus> [k]\<cdot>\<one> \<in> \<O>\<^sub>p"
        using hd_x_closed 8 
        by (metis Qp.int_inc_closed assms(2) val_of_int_inc val_ring_memI val_ring_minus_closed)
      thus ?thesis 
      using 4 assms 8 hd_x_closed unfolding 12  
      using to_Zp_val by presburger
    qed
    hence 14: "(to_Zp (hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> [k]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) i = 0"
      using "9" Zp.int_inc_closed Zp.minus_closed zero_below_val_Zp by blast
    hence 15: "to_Zp (hd x) i = k"
      using 11 by (metis "9" Zp.int_inc_closed res_diff_zero_fact(1))
    show "val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) i = k"
      using 15 8 by blast 
  qed
qed

lemma cong_set_cell_decomp:
  assumes "is_semialgebraic m C"
  assumes "\<B> = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0}"
  assumes "(i::nat) > 0"
  assumes "(S::int set) = {0<..< p^i} \<inter> {k. val ([k]\<cdot>\<one>) = 0}"
  assumes "f = (\<lambda>k::int. Cond m C (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^i)]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)"
  shows "is_cell_decomp m (f ` S) \<B>"
proof(rule is_cell_decompI)
  have "finite S"
    unfolding assms by blast
  then show "finite (f` S)"
    by blast 
  show "condition_to_set ` f ` S partitions \<B>"
  proof(rule is_partitionI)
    show "disjoint (condition_to_set ` f ` S)"
    proof(rule disjointI)
      fix A B assume A: "A \<in> condition_to_set ` f ` S" "B \<in> condition_to_set  ` f ` S" "A \<noteq> B"
      obtain a where a_def: "a \<in> S \<and> A = condition_to_set (f a)"
        using A(1) by blast 
      obtain b where b_def: "b \<in> S \<and> B = condition_to_set (f b)"
        using A(2) by blast 
      have dis: "a \<noteq> b"
        using A a_def b_def by blast 
      have a_eq: "A = condition_to_set (f a)"
        using a_def by blast 
      have b_eq: "B = condition_to_set (f b)"
        using b_def by blast 
      have 00: "A = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = a}"
      proof- 
        have 0: "val ([a]\<cdot>\<one>) = 0"
          using a_def unfolding assms by blast 
        have 1: "a \<in> {0<..<p^i}"
          using a_def unfolding assms by blast 
        have 2: "a > 0"
          using 1 greaterThanLessThan_iff by blast
        have 3: "a < p^i"
          using 1 greaterThanLessThan_iff by blast
        show ?thesis 
          using assms(1) 0 2 3  cong_set_is_cell[of m C a i] 
          unfolding a_eq assms by blast 
      qed
      have 01: "B = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = b}"
      proof- 
        have 0: "val ([b]\<cdot>\<one>) = 0"
          using b_def unfolding assms by blast 
        have 1: "b \<in> {0<..<p^i}"
          using b_def unfolding assms by blast 
        have 2: "b > 0"
          using 1 greaterThanLessThan_iff by blast
        have 3: "b < p^i"
          using 1 greaterThanLessThan_iff by blast
        show ?thesis 
          using assms(1) 0 2 3  cong_set_is_cell[of m C b i] 
          unfolding b_eq assms by blast 
      qed         
      show "A \<inter> B = {}"
        unfolding 00 01 using dis by blast 
    qed
    show "\<Union> (condition_to_set ` f ` S) = \<B>"
    proof
      show "\<Union> (condition_to_set ` f ` S) \<subseteq> \<B>"
      proof fix x assume A: "x \<in> \<Union> (condition_to_set ` f ` S)"
        then obtain a where a_def: "a \<in> S \<and> x \<in> condition_to_set (f a)"
          by blast 
        have 0: "val ([a]\<cdot>\<one>) = 0"
          using a_def unfolding assms by blast 
        have 1: "a \<in> {0<..<p^i}"
          using a_def unfolding assms by blast 
        have 2: "a > 0"
          using 1 greaterThanLessThan_iff by blast
        have 3: "a < p^i"
          using 1 greaterThanLessThan_iff by blast
        have 4: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = a}"
          using 0 2 3 cong_set_is_cell[of m C a i] a_def unfolding assms 
          using assms(1) by blast
        have 5: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> tl x \<in> C \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) i = a"
          using 4 unfolding mem_Collect_eq           by blast 
        show "x \<in> \<B>"
          unfolding assms mem_Collect_eq using  5 by blast 
      qed
      show "\<B> \<subseteq> \<Union> (condition_to_set ` f ` S)"
      proof fix x assume A: "x \<in> \<B>"
        have 0: "val (hd x) = 0"
          using A unfolding assms by blast 
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using A unfolding assms mem_Collect_eq by blast 
        have tl_x_closed: "tl x \<in> C"
          using A unfolding assms mem_Collect_eq by blast 
        have x_in_val_ring: "hd  x \<in> \<O>\<^sub>p"
          apply(rule val_ring_memI, rule cartesian_power_head[of _ _ m]) 
          using x_closed apply blast using 0 by (metis order_refl)          
        obtain a where a_def: "to_Zp (hd x) i = a"
          by blast 
        have  1: "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([a] \<cdot> \<one>) (tl x) = [a]\<cdot>\<one>"
          using assms tl_x_closed Qp.int_inc_closed Qp_constE Qp_pow_ConsE(1) x_closed by blast
        have 2: "[a]\<cdot>\<one> \<in> \<O>\<^sub>p"
          using Qp.int_inc_closed val_of_int_inc val_ring_memI by blast
        have 3: "to_Zp (hd x) \<in> carrier Z\<^sub>p"
          using x_in_val_ring  val_ring_memE to_Zp_closed by blast
        have 4: "to_Zp( [a]\<cdot>\<one>) \<in> carrier Z\<^sub>p"
          using 2 Qp.int_inc_closed to_Zp_closed by blast
        have 5: "to_Zp( [a]\<cdot>\<one>) = [a]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"
          using to_Zp_int_inc  by blast 
        have 6: "val_Zp (to_Zp (hd x)) = 0"
          using x_in_val_ring 0 to_Zp_val by presburger
        have 7: "to_Zp( [a]\<cdot>\<one>) i  = a mod p^i "
          unfolding 5  using Zp_int_inc_res by blast
        have 8: "a \<in> carrier (Zp_res_ring i)"
          unfolding a_def  using 3 a_def residues_closed by blast          
        then have 9: "a = a mod p^i"
          unfolding residue_ring_def Ring.ring_record_simps(1) 
          by (metis atLeastAtMost_iff mod_pos_pos_trivial zle_diff1_eq)
        have 10: "to_Zp( [a]\<cdot>\<one>) i  = a"
          using 7 9 by metis 
        have 11: "to_Zp(hd x \<ominus> [a]\<cdot>\<one>) = to_Zp(hd x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp( [a]\<cdot>\<one>)"
          apply(rule to_Zp_minus) using x_in_val_ring apply blast using 2 by blast 
        have  12: "to_Zp(hd x \<ominus> [a]\<cdot>\<one>) i = 0"
          unfolding 11 using 10 a_def 
          using "3" "4" res_diff_zero_fact'' by presburger
        have 13: "to_Zp(hd x \<ominus> [a]\<cdot>\<one>) \<in> carrier Z\<^sub>p"
          apply(rule to_Zp_closed)
          apply(rule Qp.ring_simprules)
           apply(rule cartesian_power_head[of _ _ m], rule x_closed)
          by blast 
        have  14: "val_Zp (to_Zp(hd x \<ominus> [a]\<cdot>\<one>)) \<ge> i"
          using 13 12 unfolding 11 
          using "10" "3" "4" a_def val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
        have 15: "(hd x \<ominus> [a]\<cdot>\<one>) \<in> \<O>\<^sub>p "
          using 2 x_in_val_ring val_ring_minus_closed by blast
        have 16: "val (hd x \<ominus> [a]\<cdot>\<one>) \<ge> i"
          using 14 15 by (metis to_Zp_val)
        have 17: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ i)] \<cdot> \<one>) (tl x)) = [(p ^ i)] \<cdot> \<one>"
          using tl_x_closed assms is_semialgebraic_closed  constant_functionE Qp.int_inc_closed by blast
        have 18: "\<zero>\<^bsub>SA m\<^esub> (tl x) = \<zero>"
          using tl_x_closed SA_zeroE assms is_semialgebraic_closed by blast 
        have 19: "val ([(p ^ i)] \<cdot> \<one>) = i"
          by (metis Qp.int_nat_pow_rep int_pow_val p_nonzero val_of_power val_p_int_pow)
        have 20: "x \<in> condition_to_set (f a)"
          unfolding assms condition_to_set.simps 
          apply(rule cell_memI)
          using x_closed apply blast
          using tl_x_closed apply blast
          apply(rule closed_interval_memI)
          unfolding 1 17 18 19 apply(rule 16)
          unfolding val_zero using eint_ord_code(3) by blast
        have 21: "a \<noteq> 0"
        proof-
          have 210: "val_Zp (to_Zp (lead_coeff x)) = 0"
            using 0 x_in_val_ring  to_Zp_val by metis   
          have 211: "to_Zp (lead_coeff x) i \<noteq> 0"
          proof(rule ccontr) assume A: "\<not> to_Zp (lead_coeff x) i \<noteq> 0"
            hence "to_Zp (lead_coeff x) i = 0"
              by blast 
            hence "val_Zp (to_Zp (lead_coeff x)) \<ge> i"
              apply(cases "to_Zp (lead_coeff x) = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
              unfolding val_Zp_def using eint_ord_code(3) apply presburger             
              using 3 zero_below_val_Zp[of "to_Zp (hd x)" i] ord_Zp_geq[of "to_Zp (hd x)" i]
              unfolding ord_Zp_def val_Zp_def 
              using eint_ord_simps(1) ord_Zp_geq by presburger            
            thus False using 210 
              by (metis assms(3) eint_ord_simps(1) neq0_conv of_nat_le_0_iff zero_eint_def)
          qed
          thus ?thesis 
            unfolding a_def by blast 
        qed
        have 22: "a \<le> p^i - 1"
          using 8 unfolding Ring.ring_record_simps(1) residue_ring_def 
          using atLeastAtMost_iff by blast
        have 23: "val ([a]\<cdot>\<one>) = 0"
        proof- 
          have 231: "val_Zp (to_Zp (lead_coeff x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([a] \<cdot> \<one>)) > val_Zp (to_Zp (hd x))"
            unfolding 6 apply(rule less_le_trans[of _  "eint (int i)"  ] )
            using assms eint_pow_int_is_pos of_nat_0_less_iff apply blast
            using 14 unfolding 11 by blast 
          have "val_Zp ([a]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = 0"
            using 231 6 3 4 unfolding 11   
            by (metis equal_val_Zp to_Zp_int_inc val_Zp_dist_def val_Zp_dist_sym)
          thus ?thesis 
            using 5 
            by (metis Q\<^sub>p_def Zp.int_inc_closed Zp_def padic_fields.inc_of_int padic_fields.val_of_inc padic_fields_axioms)
        qed
        have 24: "a \<in> S"
          unfolding assms 
          apply(rule IntI)
          using 22 21 8 p_residue_ring_car_memE(2) apply fastforce
          unfolding mem_Collect_eq 23 by blast 
        show "x \<in> \<Union> (condition_to_set ` f ` S)"
          using  24 20 by blast  
      qed
    qed
  qed
  show "\<And>s. s \<in> f ` S \<Longrightarrow> is_cell_condition s \<and> arity s = m"
  proof- 
    fix s assume  A: "s \<in> f ` S"
    then obtain a where a_def: "a \<in> S \<and>  s  = f a"
      by blast 
    have a_eq: "s = f a"
      using a_def by blast 
    have "is_cell_condition s"
      unfolding a_eq assms apply(rule is_cell_conditionI')
      using assms apply blast 
      using Qp.int_inc_closed SA_car constant_function_in_semialg_functions apply blast
       using Qp.int_inc_closed SA_car constant_function_in_semialg_functions apply blast
        apply blast
       unfolding is_convex_condition_def by blast 
     thus "is_cell_condition s \<and> arity s = m"
       unfolding a_eq assms arity.simps
       by blast 
  qed
  show "\<B> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding assms by blast 
  show "\<And>s s'. s \<in> f ` S \<Longrightarrow> s' \<in> f ` S \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  proof-  fix s s'
    assume A: "s \<in> f ` S" "s' \<in> f ` S" "s \<noteq> s'"
    obtain a where a_def: "a \<in> S \<and>s = f a"
      using A by blast 
    obtain a' where a'_def: "a' \<in> S \<and>s' = f a'"
      using A by blast 
    have a_eq: "s = f a"
      using a_def by blast 
    have a'_eq: "s' = f a'"
      using a'_def by blast 
    have 0: "a \<noteq> a'"
      using A unfolding a_eq a'_eq by blast 
    have 00: "condition_to_set (f a) = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = a}"
      proof- 
        have 0: "val ([a]\<cdot>\<one>) = 0"
          using a_def unfolding assms by blast 
        have 1: "a \<in> {0<..<p^i}"
          using a_def unfolding assms by blast 
        have 2: "a > 0"
          using 1 greaterThanLessThan_iff by blast
        have 3: "a < p^i"
          using 1 greaterThanLessThan_iff by blast
        show ?thesis 
          using assms(1) 0 2 3  cong_set_is_cell[of m C a i] 
          unfolding a_eq assms by blast 
      qed
    have 01: "condition_to_set (f a') = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> C \<and> val (hd x) = 0 \<and> to_Zp (hd x) i = a'}"
      proof- 
        have 0: "val ([a']\<cdot>\<one>) = 0"
          using a'_def unfolding assms by blast 
        have 1: "a' \<in> {0<..<p^i}"
          using a'_def unfolding assms by blast 
        have 2: "a' > 0"
          using 1 greaterThanLessThan_iff by blast
        have 3: "a' < p^i"
          using 1 greaterThanLessThan_iff by blast
        show ?thesis 
          using assms(1) 0 2 3  cong_set_is_cell[of m C a' i] 
          unfolding a'_eq assms by blast 
      qed       
    show "condition_to_set s \<inter> condition_to_set s' = {}"
        unfolding a_eq a'_eq 00 01
        using 0 by blast 
  qed
qed

lemma pre_poly_cf_zero_set_is_semialg:
  assumes "G \<in> carrier (SA (Suc m))"
  assumes "c \<in> \<O>\<^sub>p"
  assumes "is_semialgebraic m b"
  assumes "\<And>x. x \<in> b \<Longrightarrow> G(c#x) \<in> \<O>\<^sub>p"
  shows "is_semialgebraic m (b \<inter>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G(c#x)) i = 0})"
proof-
  have 00: "b \<inter>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G(c#x)) i = 0} = b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (G(c#x)) \<ge> i}"
  proof(rule equalityI')
    fix x assume A: "x \<in> b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G (c # x)) i = 0}"
    have 00: "G(c#x) \<in> \<O>\<^sub>p"
      using A assms  by blast 
    have 01: " to_Zp (G (c # x)) i = 0"
      using A by blast 
    have 02: "to_Zp (G(c#x)) \<in> carrier Z\<^sub>p"
      using 00 val_ring_memE to_Zp_closed by blast 
    have 03: "val_Zp (to_Zp (G (c # x))) \<ge> i"
      apply(cases "to_Zp (G (c # x)) = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
      using val_Zp_def 02 eint_ord_code(3) apply presburger
      using padic_integers.above_ord_nonzero[of p "to_Zp (G (c # x))" i] unfolding val_Zp_def padic_integers_def  
      using "01" "02" eint_ord_code(1) ord_Zp_geq val_Zp_def val_ord_Zp by presburger
    have 04: "val (G(c#x)) = val_Zp (to_Zp (G (c # x)))"
      using to_Zp_val[of "G(c#x)"] 00 by smt 
    show "x \<in> b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G (c # x)) i = 0} \<Longrightarrow> x \<in> b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). eint (int i) \<le> val (G (c # x))}"
      apply(rule IntI)
      using A apply blast 
      unfolding mem_Collect_eq using A 03 unfolding 04 by blast 
  next
    fix x  assume A: "x \<in> b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). eint (int i) \<le> val (G (c # x))}"
    have 00: "G(c#x) \<in> \<O>\<^sub>p"
      using A assms  by blast 
    have 01: "i \<le> val (G (c # x))"
      using A by blast 
    have 02: "to_Zp (G (c # x)) \<in> carrier Z\<^sub>p"
      using 00 val_ring_memE to_Zp_closed by blast
    have 03: "val (G (c # x)) = val_Zp (to_Zp (G (c#x)))"
      using to_Zp_val[of "G(c#x)"] 00 by smt 
    have 04: "i \<le> val_Zp (to_Zp (G (c#x)))"
      using 01 unfolding 03 by blast 
    have 05: "to_Zp (G (c#x)) i = 0"
      using 04 02 zero_below_val_Zp by blast
    show "x \<in> b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G (c # x)) i = 0}"
      using A 05 by blast 
  qed
  obtain F where F_def: "F = (\<lambda> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). c#x)"
    by blast 
  have 0: "F = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) c x # x)"
  proof fix x show "F x = (\<lambda>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) c x # x) x"
      apply(cases "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)")
      unfolding F_def restrict_def constant_function_def apply smt  
      by smt 
  qed
  have 1: "is_semialg_map m (Suc m) F"
    unfolding 0
    apply(rule semialg_map_cons[of m m "\<lambda>x. x" "constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) c"])
    using id_is_semialg_map apply blast
    using assms val_ring_memE(2)[of c] Q\<^sub>p_def SA_car Zp_def 
      constant_function_in_semialg_functions padic_fields_axioms by blast
  obtain H where H_def: "H= restrict  (G \<circ> F) (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
    by blast 
  have  H_semialg: "is_semialg_function m H"
    using semialg_function_comp_closed[of "Suc m" G m F] assms 1 unfolding H_def 
    using SA_car_memE(1) restrict_is_semialg by blast
  have H_closed: "H \<in> carrier (SA m)"
    unfolding SA_car semialg_functions_def mem_Collect_eq 
    apply(rule  conjI)
    using H_semialg is_semialg_function_closed apply blast
    apply(rule  conjI)
    using H_semialg apply blast
    unfolding H_def restrict_def by meson
  have H_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H x = G(c#x)"
    unfolding H_def restrict_def F_def 
    by (smt comp_apply)    
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (G(c#x)) \<ge> i} = H  \<inverse>\<^bsub>m\<^esub> {t \<in> carrier Q\<^sub>p. val t \<ge> i}"
    apply(rule equalityI')
    unfolding evimage_def apply(rule IntI, rule vimageI2) unfolding mem_Collect_eq 
    using H_eval H_closed apply (metis SA_car_closed)
     apply blast using H_eval 
    by (metis (no_types, lifting) Int_iff mem_Collect_eq vimage_eq)
  show "is_semialgebraic m (b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (G (c # x)) i = 0})"
    unfolding 00 apply(rule intersection_is_semialg)
    using assms apply blast
    unfolding 2 apply(rule evimage_is_semialg, rule H_closed)
    using ball_is_univ_semialgebraic[of \<zero> i] unfolding c_ball_def 
    by (smt Collect_cong Qp.cring_simprules(2) Qp.r_right_minus_eq notin_closed val_ineq val_ultrametric_noteq'')
qed
    
lemma poly_cf_zero_set_is_semialg:
  assumes "G \<in> carrier (UP (SA m))"
  assumes "c \<in> \<O>\<^sub>p"
  assumes "is_semialgebraic m b"
  assumes "\<And>x. x \<in> b \<Longrightarrow> SA_poly_to_Qp_poly m x G \<bullet> c \<in> \<O>\<^sub>p"
  shows "is_semialgebraic m (b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (SA_poly_to_Qp_poly m x G \<bullet> c) i = 0})"
proof-
  have 1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m x G \<bullet> c = SA_poly_to_SA_fun m G (c#x)"
    using SA_poly_to_SA_fun_formula[of G m _ c] val_ring_memE assms by smt 
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (SA_poly_to_Qp_poly m x G \<bullet> c) i = 0} = 
{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (SA_poly_to_SA_fun m G (c#x)) i = 0}"
    apply(rule equalityI') unfolding mem_Collect_eq  using 1 apply smt 
    using 1 by smt 
  show ?thesis unfolding 2 
    apply(rule pre_poly_cf_zero_set_is_semialg, rule SA_poly_to_SA_fun_is_SA, rule assms(1), rule assms(2), rule assms(3))
    using 1 assms  
    by (metis (no_types, opaque_lifting) Set.basic_monos(7) is_semialgebraic_closed)
qed

definition denef_I_property where
"denef_I_property m f A = (\<exists> S. (is_cell_decomp m S A \<and>
                      (\<forall>\<C> \<in> S. \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N)))"

lemma denef_I_property_refine:
  assumes "is_cell_decomp m S A \<and> (\<forall> \<C> \<in> S. denef_I_property m f (condition_to_set \<C>))"
  shows "denef_I_property m f A"
  apply(unfold denef_I_property_def, rule  refine_each_cell[of _ S])
    using assms denef_I_property_def by auto 

lemma denef_I_property_replace:
  assumes "f \<in> carrier (UP (SA m))"
  assumes "denef_I_property m g A"
  assumes "\<And> x t. t#x \<in> A \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
  shows "denef_I_property m f A"
proof- 
  obtain S where S_def: "is_cell_decomp m S A \<and>
                      (\<forall>\<C> \<in> S. \<exists>N. SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N)"
    using assms denef_I_property_def by blast 
  have "(\<forall>\<C> \<in> S. \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N)"
  proof
    fix \<C> assume A: "\<C> \<in> S"
    obtain N where N_def: "SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N"
      using S_def A by blast
    have rule: " \<And>x t.
       t # x \<in> condition_to_set \<C> \<Longrightarrow>  SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
    proof- 
      fix x t assume a: "t#x \<in> condition_to_set \<C>"
      show "SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
        apply(rule assms(3)[of t x])
        using A is_cell_decomp_subset a  S_def by blast
    qed
    have "SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N"
      apply(intro SA_poly_uboundedI assms)
      using A S_def is_cell_decompE[of m S A] is_cell_conditionE'[of ]
        apply (meson SA_poly_ubounded_facts'(2))
      using A S_def is_cell_decompE[of m S A] is_cell_conditionE'[of ]
       apply (metis SA_poly_ubounded_facts'(3))
      using rule N_def SA_poly_uboundedE 
      by (metis SA_poly_uboundedE')
    thus "\<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N "
      by blast 
  qed
  thus ?thesis 
    using S_def unfolding denef_I_property_def by auto 
qed

lemma denef_I_proof_by_property:
  assumes "\<And>m f.\<lbrakk>f \<in> carrier (UP (SA m)); deg (SA m) f \<le> d \<rbrakk> \<Longrightarrow> 
                  denef_I_property m f (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  shows "denef_I p d"
  using assms padic_fields_axioms
      unfolding denef_I_def denef_I_axioms_def 
      using denef_I_property_def is_compatible_decompI padic_fields.is_compatible_decomp_def 
      by fastforce

end 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Building Contexts for the Proof\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open> The first locale needed for the proof is just the amalgam of \texttt{denef\_I} and 
      \texttt{denef\_II}.\<close>


text\<open>At this point, we have a large number of parameters which will be fixed for the rest of the 
     proof. We can therefore create a new locale to track these parameters and the basic assumptions 
     that we will need to make about them. Once we have proved the premise of the previous lemma in 
     this locale, we will be done the proof of $\texttt{I}_\texttt{d+1}$.\<close>

locale denef_cell_decomp_I_induct_reduction = common_refinement_locale + 
  assumes deriv_bounded: "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Decomposing the Complement of the Set $A_0$\<close>
(**************************************************************************************************)
(**************************************************************************************************)
text\<open>This section finishes the final important piece of the proof, in showing that the complement of 
     $A_0$ can also be decomposed as desired. The proof is involved enough to warrant its own 
     context locale. \<close>

locale A\<^sub>0_comp_refinement = common_refinement_locale + 
  fixes B b \<phi> i H
  assumes \<phi>_Unit: "\<phi> \<in> Units (SA m)"
  assumes B_cell: "is_cell_condition B"
  assumes B_eq: "B = Cond m b c \<phi> \<phi> closed_interval"
  assumes b_subset: "condition_to_set B \<subseteq> condition_to_set \<C> - A\<^sub>0"
  assumes i_inds: "i \<in> inds"
  assumes H_def: "H = (\<lambda>i. a i \<otimes>\<^bsub>SA m\<^esub>\<phi>[^]\<^bsub>SA m\<^esub> i)"
  assumes H_ineq: "\<And>j x. j \<in> inds \<Longrightarrow> x \<in> b \<Longrightarrow> val (H i x) \<le> val (H j x)"
  assumes b_nonempty: "b \<noteq> {}"
  assumes static: "static_order_type (H ` inds) b"

context A\<^sub>0_comp_refinement
begin

lemma \<phi>_closed: "\<phi> \<in> carrier (SA m)"
  using  \<phi>_Unit SA_Units_closed by blast 

lemma \<phi>_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<noteq> \<zero>"
  using \<phi>_Unit SA_Units_memE' by blast
            
lemma \<phi>_nonzero': "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<in> nonzero Q\<^sub>p"
  using \<phi>_closed \<phi>_nonzero SA_car_memE(3) unfolding nonzero_def by blast 
  
lemma b_semialg: "is_semialgebraic m b"
  using B_eq B_cell is_cell_conditionE by blast

lemma H_closed: "\<And> i. i \<in> inds \<Longrightarrow>  H i \<in> carrier (SA m)"
  unfolding H_def using inds_memE \<phi>_closed SA_Units_closed[of _ m]
  by blast

lemma H_unit: "\<And>i. i \<in> inds \<Longrightarrow> H i \<in> Units (SA m)"
  unfolding H_def using inds_memE  R.Units_pow_closed \<phi>_Unit by blast

lemma H_eval: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x = a i x \<otimes> (\<phi> x [^] i)"
  unfolding H_def using \<phi>_closed inds_memE a_closed SA_mult SA_nat_pow by presburger

lemma H_eval_closed: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<in> carrier Q\<^sub>p"
  using H_closed SA_car_closed by blast

lemma H_eval_closed': "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> a i x \<otimes> (\<phi> x [^] i) \<in> carrier Q\<^sub>p"
  using H_eval_closed H_eval by auto 

lemma H_nonzero: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<noteq> \<zero>"
  using H_unit SA_Units_memE' by blast            

lemma H_nonzero': "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<in> nonzero Q\<^sub>p"
  unfolding nonzero_def mem_Collect_eq using SA_car_memE(3) H_closed H_nonzero by blast 

lemma H_ord: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (H i x) = ord (a i x) + i*ord(\<phi> x)"
  using H_eval \<phi>_nonzero inds_memE ord_mult nonzero_nat_pow_ord 
  by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero')

lemma H_val: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (H i x) = val (a i x) + val (\<phi> x [^] i)"
  using  \<phi>_nonzero inds_memE  H_eval val_mult 
  by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero' val_mult0)

lemma H_val': "\<And>t x i. i \<in> inds \<Longrightarrow> t#x \<in> condition_to_set B
                 \<Longrightarrow> val (H i x) = val ((a i x) \<otimes>(t \<ominus> c x)[^] i)"
proof- fix t x i assume A: "i \<in> inds" "t#x \<in> condition_to_set B"
  have x_in: "x \<in> b"
    using A B_eq B_cell condition_to_set_memE'(1) by blast
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    by (meson b_semialg basic_trans_rules(31) is_semialgebraic_closed x_in)
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using A B_eq \<C>_memE(2) b_subset in_mono by fastforce    
  have 0: "val ((a i x) \<otimes>(t \<ominus> c x)[^] i) = val (a i x) + val ((t \<ominus> c x)[^] i)"
    by(intro val_mult a_eval Qp.nat_pow_closed Qp.ring_simprules
            t_closed SA_car_closed[of c m] c_closed x_closed)
  have 1: "val ((t \<ominus> c x)[^] i) = val (\<phi> x [^] i)"
    using A by (smt (verit, best) B_eq Qp.minus_closed SA_car_closed \<phi>_nonzero' 
        c_closed equal_val_imp_equal_ord(2) list.sel(1) list.sel(3) mem_Collect_eq
        one_point_closed_interval t_closed val_of_power x_closed)
  have 2: "val ((\<phi> x)[^] i) = val ((t \<ominus> c x)[^] i)"
    using A 1 unfolding B_eq cell_def condition_to_set.simps
    by presburger
  show "val (H i x) = val ((a i x) \<otimes>(t \<ominus> c x)[^] i)"
    using H_val 0 1 unfolding 2 
    using "1" A(1) x_closed by presburger
qed

lemma b_closed:
"b \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  using b_semialg is_semialgebraic_closed by presburger

lemma common_g_prems:
"f \<in> carrier (UP (SA m))"
"c \<in> carrier (SA m)"
"\<phi> \<in> Units (SA m)"
"a i \<in> Units (SA m)"
  using f_closed c_closed \<phi>_Unit apply auto 
  by (meson i_inds inds_memE)

lemma a_i_Unit:
"a i \<in> Units (SA m)"
  by(intro inds_memE i_inds)

lemma inv_a_i_Unit:
"inv\<^bsub>SA m\<^esub> a i \<in> Units (SA m)"
  using a_i_Unit by simp

lemma \<phi>_pow_Unit:
"\<phi> [^]\<^bsub>SA m\<^esub> (j::int) \<in> Units (SA m)"
  using \<phi>_Unit 
  by (simp add: R.Units_int_pow_closed)
end

locale A\<^sub>0_comp_refinement_i_pos = A\<^sub>0_comp_refinement +
  assumes deriv_bounded: "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
  assumes i_nonzero: "i \<noteq> 0"

locale A\<^sub>0_comp_refinement_i_zero = A\<^sub>0_comp_refinement +
  assumes deriv_bounded: "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
  assumes i_zero: "i = 0"
  assumes i_unique_min: "\<And>j x. j \<in> inds \<Longrightarrow> j > 0 \<Longrightarrow> x \<in> b \<Longrightarrow> val (H 0 x) < val (H j x)"

context A\<^sub>0_comp_refinement_i_pos
begin

definition N where N_def: 
"N = (SOME N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N)"

lemma N_prop:
"SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
  using N_def deriv_bounded 
  by (metis someI)

lemma B_subset:
"condition_to_set B \<subseteq> condition_to_set \<C> - A\<^sub>0"
  using A\<^sub>0_comp_refinement_axioms
  unfolding A\<^sub>0_comp_refinement_axioms_def A\<^sub>0_comp_refinement_def
  by blast 

lemma SA_poly_ubounded_on_B:
"SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set B) N"
  apply(rule SA_poly_ubounded_mono[of _ _ _ "condition_to_set \<C>"], rule N_prop )
  using B_subset by blast

interpretation cell_normalization _ _ _ _ B a b c \<phi> _ _ inds i
proof-
  have 0: "\<And>j t x.
        t # x \<in> condition_to_set B \<Longrightarrow>
        val (a i x \<otimes> (t \<ominus> c x) [^] i)
        \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
  proof- 
    fix j t x assume a: " t # x \<in> condition_to_set B"
    have x_in: "x \<in> b"
      using a unfolding B_eq condition_to_set.simps cell_def by auto  
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using b_closed x_in by blast
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using a B_subset \<C>_memE(2) subsetD by fastforce
    have tminus: "t \<ominus> c x \<in> carrier Q\<^sub>p"
      by(intro Qp.ring_simprules t_closed SA_car_closed[of _ m] c_closed x_closed)
    show "val (a i x \<otimes> (t \<ominus> c x) [^] i)
        \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
    proof(cases "j \<in> inds")
      case True
      have H_vals: "H i x = a i x \<otimes> \<phi> x [^] i"
                 "H j x = a j x \<otimes> \<phi> x [^] j"
         apply(intro H_eval i_inds x_closed)
          by(intro H_eval True x_closed) 
      have b: "val (a i x \<otimes> (\<phi> x) [^] i)
          \<le> val (a j x \<otimes> (\<phi> x) [^] j)"
        using a True H_ineq H_vals by (metis x_in)
      have c: "val (a i x \<otimes> (\<phi> x) [^] i) = val (a i x \<otimes> (t \<ominus> c x) [^] i)"
        using a H_val'[of i t x] unfolding H_def  
        using H_def H_vals(1) i_inds by fastforce
      have d: "val (a j x \<otimes> (\<phi> x) [^] j) = val (a j x \<otimes> (t \<ominus> c x) [^] j)"
        by (metis H_val' H_vals(2) True a)
      show ?thesis
        using b unfolding c d by auto 
    next
      case False
      have a: "a j x \<otimes> (t \<ominus> c x) [^] j = \<zero>"
        using Qp.nat_pow_closed False inds_non_memE[of j x] x_closed tminus  
        by auto 
      then show ?thesis unfolding a val_zero by auto 
    qed
  qed
  have 1: "\<And>j. j \<in> inds \<Longrightarrow> a j \<in> Units (SA m)"
          "\<And>j. j \<notin> inds \<Longrightarrow> a j = \<zero>\<^bsub>SA m\<^esub>"
     apply (simp add: inds_memE)
    using a_def f_taylor_cfs inds_def by auto
  show "cell_normalization p B a b c \<phi> m f inds i"
       "Z\<^sub>p \<equiv> padic_int p" "Q\<^sub>p \<equiv> Frac Z\<^sub>p" "\<iota> \<equiv> Frac_inc Z\<^sub>p"
     apply(intro cell_normalization.intro refined_one_val_point_cell.intro one_val_point_cell.intro
                  refined_one_val_point_cell_axioms.intro one_val_point_cell_axioms.intro
                 cell_normalization_axioms.intro)
               apply (simp add: padic_fields_axioms)
  using f_closed  \<phi>_Unit B_cell B_eq a_def b_nonempty Q\<^sub>p_def Z\<^sub>p_def \<iota>_def
        i_inds 0 1
  unfolding a_def by auto 
qed

lemma M_exists: 
"\<exists>M::nat. M > ord([s]\<cdot>\<one>) \<and> eint M > val ([i]\<cdot>\<one>) + eint N"
proof- 
  obtain M' where M'_def: "eint M' = max (val ([i]\<cdot>\<one>) + eint N) (eint 1)"
    using  Qp.nat_inc_closed Qp_char_0 plus_eint_simps(1) val_ord' max_eint_simps(1) 
    by (simp add: i_nonzero)
  obtain M where M_def: "M = Suc (max (nat M') (nat (ord([s]\<cdot>\<one>))))"
    by blast 
  have M_int: "int M > M'"
    unfolding M_def using M'_def 
    by linarith  
  have M_eint: "eint M > eint M'"
    using M_int  by simp
  have " M > ord([s]\<cdot>\<one>) \<and> eint M > val ([i]\<cdot>\<one>) + eint N"
    apply(rule conjI)
    using M_def  apply simp
    using M_eint M'_def by simp 
  thus ?thesis by blast 
qed

definition s where s_def: "s = deg (SA m) f"

lemma s_pos: "s > 0"
proof- 
  have "deg (SA m) f \<ge> i"
    using i_inds inds_def inds_bounded by blast
  thus ?thesis unfolding s_def using i_nonzero by auto 
qed

definition M where M_def: 
"M = (SOME M::nat. M > ord([s]\<cdot>\<one>) \<and> eint M > val ([i]\<cdot>\<one>) + eint N)"

lemma M_props:
"M > ord([s]\<cdot>\<one>)"
"eint M > val ([i]\<cdot>\<one>) + eint N"
  using M_def M_exists apply(smt (z3) someI)
  using M_def M_exists  by(smt (z3) someI)

definition S where S_def: 
  "(S::int set) = {0<..< p^(M+1)} \<inter> {k. val ([k]\<cdot>\<one>) = 0}"

lemma M_pos: 
"M > 0"
proof- 
  have "ord ([s] \<cdot> \<one>) \<ge> 0"
    apply(rule ord_nonneg)
     apply (meson val_ring_nat_inc_closed)
    using s_pos 
    by (simp add: Qp_char_0'')
  thus ?thesis 
using M_props by auto 
qed  

text\<open>We need to decompose the normal cell fibred at b\<close>

definition normal_cell_decomp where
"normal_cell_decomp =  
        (\<lambda>k::int. Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval) ` S"

lemma normal_cell_underlying_set:
"condition_to_set (normal_cell m b) = {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> b \<and> val (hd x) = 0}"
     apply(rule equalityI')
  unfolding mem_Collect_eq 
   apply (metis b_closures(2) cell_condition_set_memE(1) list.sel(1) normal_cell_cell_cond 
                normal_cell_memE(2) obtain_cell_mem_coords padic_fields.arity.simps 
                padic_fields.condition_to_set_memE(1) padic_fields.normal_cell_def 
                padic_fields_axioms)
  by (metis b_closures(2) carrier_is_cell cartesian_power_head list.discI list.exhaust_sel 
      normal_cell_memI obtain_cell_mem_coords)

lemma normal_cell_decomp_is_decomp:
"is_cell_decomp m normal_cell_decomp (condition_to_set (normal_cell m b)) "
  unfolding normal_cell_decomp_def
  apply(rule cong_set_cell_decomp[of _ b _ "M+1"])
  using b_semialg apply blast
  unfolding normal_cell_underlying_set apply blast
  using M_pos  unfolding S_def by auto 

definition b_part where 
"b_part k = b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<exists> \<alpha> \<in> \<O>\<^sub>p. to_Zp \<alpha> (M+1) = k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2*M + 1) = 0}"

lemma g_ith_cf: "\<And>x y. y#x \<in> condition_to_set (normal_cell m b) \<Longrightarrow> g i x = \<one>"
proof- fix x y assume Aa: "y#x \<in> condition_to_set (normal_cell m b)" 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using Aa unfolding normal_cell_underlying_set mem_Collect_eq using cartesian_power_tail[of "y#x" Q\<^sub>p m]
    unfolding list_tl 
    by blast 
  have x_in_b: "x \<in> b"
    using Aa unfolding normal_cell_underlying_set mem_Collect_eq using cartesian_power_tail[of "y#x" Q\<^sub>p m]
    unfolding list_tl 
    by blast 
  have 01: "g i x = (\<phi> x[^](int i - int i)) \<otimes>(a i x \<otimes> inv (a i x) )"
    using x_in_b g_cfs_eval by auto  
  have 02: "g i x = (\<phi> x[^](0::int)) \<otimes>\<one>"
  proof-
    have 020: "(a i x \<otimes> inv (a i x) ) = \<one>" 
      using inds_memE x_closed SA_Units_nonzero 
      by (meson SA_Units_memE' a_eval common_g_prems(4) field_inv(2))      
    show ?thesis 
      unfolding 01 020 by (metis group_add_class.right_minus_eq)
  qed
  show "(g i x) = \<one>" unfolding 02 using \<phi>_closed x_closed SA_car_memE 
    by (metis Qp.cring_simprules(6) Qp.r_one int_pow_0)
qed

lemma b_part_alt0:
"\<And>k. b_part k = b \<inter> (\<Union> \<beta> \<in> carrier (Zp_res_ring (2*M + 1)) \<inter> {x. x mod p^(M+1) = k}. 
                {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>]\<cdot>\<one>) (M+1) = k \<and>
                                      to_Zp (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>]\<cdot>\<one>)) (2*M + 1) = 0} )"
proof- fix k
  show "b_part k = b \<inter>(\<Union>\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p^ (M + 1) = k}.
                  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
                  to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0})"
    apply(rule equalityI')
  proof- 
    fix x assume A00: "x \<in> b_part k"                      
    hence A0: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (\<exists>\<alpha>\<in>\<O>\<^sub>p. to_Zp \<alpha> (M + 1) = k \<and> 
                    to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2 * M + 1) = 0)"
      unfolding b_part_def
      by blast
    obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> \<O>\<^sub>p \<and>to_Zp \<alpha> (M + 1) = k \<and>
                       to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2 * M + 1) = 0"
      using A0 by blast 
    obtain \<beta> where \<beta>_def: "\<beta> = to_Zp \<alpha> (2*M+1)"
      by blast 
    have 00: "to_Zp \<alpha> \<in> carrier Z\<^sub>p"
      using \<alpha>_def to_Zp_closed val_ring_memE(2) by blast
    have 01: "to_Zp \<alpha>  (M+1) = to_Zp \<alpha> (2*M+1) mod  p^(M+1)"
      using 00 p_residue_padic_int[of "to_Zp \<alpha>" "M+1" "2*M + 1"] unfolding p_residue_def residue_def    
      by linarith
    have 02: "\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p^ (M + 1) = k}"
      apply(rule IntI) unfolding \<beta>_def using \<alpha>_def 
       apply (metis Q\<^sub>p_def val_ring_memE Zp_def padic_fields.to_Zp_closed padic_fields_axioms residues_closed)
      unfolding mem_Collect_eq using \<alpha>_def 01 by linarith
    have 03: "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
                to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0}"
      unfolding mem_Collect_eq apply(rule conjI) using A0 apply blast apply(rule conjI)
    proof-
      have 030: "to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = \<beta> mod p^(M+1)"
        unfolding to_Zp_int_inc using Zp_int_inc_res by blast
      show "to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k" 
        unfolding 030 using \<beta>_def 01 \<alpha>_def by metis  
    next
      obtain G where G_def: "G = SA_poly_to_Qp_poly m x g"
        by blast 
      have G_closed: "G \<in> carrier (UP Q\<^sub>p)"
        unfolding G_def apply(rule  SA_poly_to_Qp_poly_closed )
        using A0 apply blast using g_closed by blast
      have G_cfs: "\<And>i. G i \<in> \<O>\<^sub>p"
        unfolding G_def  using g_integral A00 integral_on_memE b_part_def 
        by force
      have 000: "to_Zp (G \<bullet> \<alpha>) (2*M+1) = to_Zp (G \<bullet> ([\<beta>]\<cdot>\<one>)) (2*M+1)"
        apply(rule poly_eval_cong, rule G_closed, rule G_cfs)
        using \<alpha>_def apply blast 
        using Qp.int_inc_closed val_of_int_inc val_ring_memI apply blast
      proof- 
        have 000: "to_Zp ([\<beta>] \<cdot> \<one>) = [\<beta>]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
          using to_Zp_int_inc by blast
        have 001: "([\<beta>]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (2*M+1) = \<beta> mod p^(2*M+1)"
          using Zp_int_inc_res by blast
        have 002: "\<beta> mod p^(2*M+1) = \<beta>"
        proof-
          have 0: "\<beta> \<in> {0..p ^ (2 * M + 1) - 1}"
            using 02 unfolding Ring.ring_record_simps residue_ring_def by blast 
          have 1: "\<beta> \<le>  p^(2*M+1) - 1"
            using 0 atLeastAtMost_iff by blast
          have 2: "\<beta> \<ge> 0"
            using 0 atLeastAtMost_iff by blast
          have 3: "\<beta> < p^(2*M+1)"
            using 1 by presburger 
          show  ?thesis 
            using 2 3 mod_pos_pos_trivial by blast
        qed
        show " to_Zp \<alpha> (2 * M + 1) = to_Zp ([\<beta>] \<cdot> \<one>) (2 * M + 1)"
          unfolding 000 001 002 using \<beta>_def by blast
      qed
      thus " to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0"
        using \<alpha>_def unfolding G_def 000 by smt 
    qed
    show " x \<in> b \<inter> (\<Union>\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p ^ (M + 1) = k}.
    {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
          to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0})"
      apply(rule IntI)
      using A00 unfolding b_part_def
       apply blast
      using 03 02 by blast 
  next
    fix x assume A0: "x \<in> b \<inter>
(\<Union>\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p ^ (M + 1) = k}.
{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0})"
    then obtain \<beta> where \<beta>_def: "\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<inter> 
                                                    {x. x mod p ^ (M + 1) = k} \<and>
                    x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
                       to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0}"
      by blast 
    have A00: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
              to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0"
      using \<beta>_def unfolding mem_Collect_eq by blast 
    show " x \<in> b_part k"
      unfolding b_part_def 
      apply(rule IntI) using A0 apply blast
    proof
      obtain \<alpha> where \<alpha>_def: "\<alpha> = [\<beta>]\<cdot>\<one> "
        by blast 
      have \<alpha>_in_val: "\<alpha> \<in> \<O>\<^sub>p"
        unfolding \<alpha>_def using Qp.int_inc_closed val_of_int_inc val_ring_memI by blast
      have 000: "to_Zp \<alpha>  = [\<beta>]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"
        unfolding \<alpha>_def using to_Zp_int_inc by blast
      have 001: "to_Zp \<alpha> (M+1) = \<beta> mod p^(M+1)"
        unfolding 000 using Zp_int_inc_res by blast
      have 002: "to_Zp \<alpha> (M+1) = k"
        unfolding 001 using \<beta>_def by blast 
      have 003: "to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2 * M + 1) =0"
        unfolding \<alpha>_def using \<beta>_def by blast 
      show "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (\<exists>\<alpha>\<in>\<O>\<^sub>p. to_Zp \<alpha> (M + 1) = k \<and> 
            to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2 * M + 1) = 0)"
        using A0 \<alpha>_in_val 002 003 by blast 
    qed
  qed
qed

lemma b_part_alt:
"\<And>k. b_part k = (\<Union> \<beta> \<in> carrier (Zp_res_ring (2*M + 1)) \<inter> {x. x mod p^(M+1) = k}. b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>]\<cdot>\<one>) (M+1) = k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>]\<cdot>\<one>)) (2*M + 1) = 0} )"
  unfolding b_part_alt0 by blast 

lemma pre_b_part_semialg:
"\<And> (\<beta>::int) (k::nat).  is_semialgebraic m (b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>]\<cdot>\<one>) (M+1) = k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>]\<cdot>\<one>)) (2*M + 1) = 0})"
proof- fix \<beta>::int fix k::nat
  show "is_semialgebraic m (b \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>]\<cdot>\<one>) (M+1) = k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>]\<cdot>\<one>)) (2*M + 1) = 0})"       
  proof(cases "to_Zp ([\<beta>]\<cdot>\<one>) (M+1) = k")
    case True
    obtain G where G_def: "G = SA_poly_to_SA_fun m g"
      by blast 
    have G_closed: "G \<in> carrier (SA (Suc m))"
      unfolding G_def by(rule SA_poly_to_SA_fun_is_SA, rule g_closed)
    have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = int k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0} = 
                              {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0}"
      apply(rule equalityI') unfolding mem_Collect_eq apply blast using True by blast 
    show ?thesis unfolding 0 
      apply(rule poly_cf_zero_set_is_semialg, rule g_closed ) 
      using Qp.int_inc_closed val_of_int_inc val_ring_memI apply blast
      using b_semialg apply blast
      apply(rule val_ring_poly_eval, rule SA_poly_to_Qp_poly_closed)
      using b_closed apply blast
      using g_closed apply blast 
      using g_integral integral_on_memE(2) apply presburger      
      using Qp.int_inc_closed val_of_int_inc val_ring_memI by blast                       
  next
    case False
    have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = int k \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0} = {}"
      apply(rule equalityI') unfolding mem_Collect_eq using False apply blast  by blast
    show ?thesis unfolding 0 using empty_is_semialgebraic 
      by simp
  qed
qed

lemma b_part_semialg:
"is_semialgebraic m (b_part (j::nat))"
  unfolding b_part_alt 
proof(rule finite_union_is_semialgebraic'')
  have 0: "finite (carrier (residue_ring (p ^ (2 * M + 1))))"
    using residue_ring_card[of "(2 * M + 1)"] by auto 
  thus "finite (carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p ^ (M + 1) = j})"
    by blast 
  show  "\<And>\<beta>. \<beta> \<in> carrier (residue_ring (p ^ (2 * M + 1))) \<inter> {x. x mod p ^ (M + 1) = j} \<Longrightarrow>
         is_semialgebraic m
          (b \<inter>
           {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>).
            to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = j \<and> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0})"
    by(rule  pre_b_part_semialg )
qed

lemma g'_SA_poly_ubounded:
"SA_poly_ubounded p m g' \<zero>\<^bsub>SA m\<^esub> (condition_to_set (normal_cell m b)) N"
  using transfer_SA_poly_ubounded3[of N] B_eq SA_poly_ubounded_on_B padic_fields.normal_cell_def
        padic_fields_axioms by force

lemma g'_val_bound:
 "\<And>x t. t # x \<in> condition_to_set (normal_cell m b) \<Longrightarrow>  val (SA_poly_to_Qp_poly m x g' \<bullet> t) \<le> eint M"
proof- 
  have g'_bound: "\<And>x t. t # x \<in> condition_to_set (normal_cell m b) \<Longrightarrow> val (SA_poly_to_Qp_poly m x g' \<bullet> t) \<le> val(UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') (i-1) \<bullet> t)  + eint N"
    using g'_SA_poly_ubounded SA_poly_uboundedE'[of m g' "\<zero>\<^bsub>SA m\<^esub>" "(condition_to_set (normal_cell m b))" N]
    by blast
  have 0: "\<And>x t. t#x \<in> condition_to_set (normal_cell m b)\<Longrightarrow> val(UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') (i-1) \<bullet> t) = val ([i]\<cdot>\<one>)"
  proof- 
    fix x t assume A0: "t#x \<in> condition_to_set (normal_cell m b)"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A0 unfolding normal_cell_underlying_set mem_Collect_eq list_tl using b_closed by blast 
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using A0 b_closed cartesian_power_head[of "t#x" Q\<^sub>p m]
      unfolding normal_cell_underlying_set mem_Collect_eq list_hd by blast  
    have 0: "UPQ.X_minus (\<zero>\<^bsub>SA m\<^esub> x)  = up_ring.monom (UP Q\<^sub>p) \<one> 1"
    proof-
      have 00: "to_polynomial Q\<^sub>p (\<zero>\<^bsub>SA m\<^esub> x) = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
        using SA_zeroE[of x m] x_closed unfolding to_polynomial_def
        using UPQ.monom_zero by presburger
      show ?thesis unfolding 00 X_poly_minus_def X_poly_def                       
      by (metis Qp.one_closed UPQ.P.r_right_minus_eq UPQ.is_UP_monomE(1) UPQ.monom_is_UP_monom(1) UPQ.trms_of_deg_leq_def UPQ.trms_of_deg_leq_degree_f UPQ.trms_of_deg_leq_id)
    qed
    have 1: "UPQ.X_minus (\<zero>\<^bsub>SA m\<^esub> x) [^]\<^bsub>UP Q\<^sub>p\<^esub> (i-1) = up_ring.monom (UP Q\<^sub>p) \<one> (i-1)"
      unfolding 0
      using Qp.nat_pow_one Qp.one_closed UPQ.monom_pow nat_mult_1 by presburger
    have 2: "taylor_expansion Q\<^sub>p (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g')= (SA_poly_to_Qp_poly m x g')"
    proof-
      have 20: "\<zero>\<^bsub>SA m\<^esub> x = \<zero>"
        using x_closed SA_zeroE by blast 
      have 21: "UPQ.X_plus (\<zero>\<^bsub>SA m\<^esub> x) = up_ring.monom (UP Q\<^sub>p) \<one> 1"
        unfolding X_poly_plus_def 20 X_poly_def to_polynomial_def 
        by (metis Qp.cring_simprules(2) Qp.cring_simprules(6) Qp.one_not_zero Suc_less_eq UPQ.P.a_ac(2) UPQ.cfs_monom UPQ.deg_monom UPQ.is_UP_monomE(1) UPQ.lin_part_def UPQ.lin_part_id UPQ.monom_is_UP_monom(1) UPQ.trms_of_deg_leq_degree_f less_Suc0 less_one nat.simps(2))
      show ?thesis unfolding taylor_expansion_def 21 unfolding 20 
        using UPQ.X_sub[of "SA_poly_to_Qp_poly m x g'"] SA_poly_to_Qp_poly_closed 
        unfolding X_poly_def using x_closed 
        by (simp add: g'_def g'_closed)       
    qed
    have 3: "UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') (i-1) = (SA_poly_to_Qp_poly m x g') (i-1) \<odot>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) \<one> (i-1) "
      unfolding UPQ.taylor_term_def 1 2 by blast
    have 4: "(SA_poly_to_Qp_poly m x g') (i-1) =[i]\<cdot>(g i x)"    
    proof-
      have 40: "Suc (i-1) = i"
        using i_nonzero  by presburger 
      have 41: "SA_poly_to_Qp_poly m x g' (i - 1) = g' (i - 1) x"
        using x_closed  g'_closed SA_poly_to_Qp_poly_coeff[of x m g' "(i-1)"] by blast 
      have 42: "[i] \<cdot> g i x = [Suc (i-1)] \<cdot> g (Suc (i-1)) x"
        using 40 by auto 
      have 43: "g' (i - 1) = [Suc (i - 1)] \<cdot>\<^bsub>SA m\<^esub> g (Suc (i - 1))"
        unfolding g'_def 
        by (meson g_closed 
            A\<^sub>0_comp_refinement_i_pos_axioms UPSA.pderiv_cfs)        
      show ?thesis
        using A0 b_closed g_closed SA_poly_to_Qp_poly_coeff[of x m g' "(i-1)"] 40
        unfolding  41 normal_cell_underlying_set mem_Collect_eq list_tl 42
        unfolding 43 
        using x_closed g_cfs_inds  A\<^sub>0_comp_refinement.axioms 
              SA_Units_closed SA_add_pow_apply i_inds UP_SA_cfs_closed by presburger              
    qed      
    have 5: "val ([i]\<cdot>(g i x)) = val ([i] \<cdot> \<one>) "
    proof-
      have 50: "[i]\<cdot>(g i x) = [i]\<cdot>\<one> \<otimes>(g i x)"
        using x_closed  SA_Units_closed_fun[of "g i" m x] Qp.add_pow_ldistr Qp.cring_simprules(12)
          Qp.cring_simprules(6) g_cfs_inds i_inds by presburger
      have 51: "g i x = \<one> "
        using A0  by (meson g_ith_cf)        
      show ?thesis unfolding 50 51 by blast 
    qed
    have 6: "[i] \<cdot> g i x \<odot>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) \<one> (i - 1) \<bullet> t = [i] \<cdot> g i x \<otimes> t[^](i-1)"
      using t_closed g_cfs_inds SA_Units_closed_fun x_closed 
      by (metis Qp.nat_mult_closed UPQ.monic_monom_smult UPQ.to_fun_monom i_inds)
    have 7: "val t = 0"
      using A0 unfolding normal_cell_underlying_set mem_Collect_eq list_hd by blast 
    have 8: "val (t[^](i-1)) = 0"
      using  7 
      by (metis (no_types, lifting) Qp.cring_simprules(6) Qp.nat_pow_closed Qp.nat_pow_one Qp.nonzero_pow_nonzero equal_val_imp_equal_ord(1) nonzero_nat_pow_ord t_closed val_nonzero' val_one val_ord')
    have 9: "g i x = \<one>"
      using x_closed g_ith_cf A0 by blast
    show "val (UPQ.taylor_term (\<zero>\<^bsub>SA m\<^esub> x) (SA_poly_to_Qp_poly m x g') (i-1) \<bullet> t) = val ([i] \<cdot> \<one>)"
      unfolding 3 4 6 unfolding 9 using 8 val_mult[of "[i]\<cdot>\<one>" "t[^](i-1)"] t_closed 
      by (metis Qp.add_pow_closed Qp.cring_simprules(6) Qp.nat_pow_closed add.comm_neutral)
  qed
  have "\<And>x t. t # x \<in> condition_to_set (normal_cell m b) \<Longrightarrow>  val (SA_poly_to_Qp_poly m x g' \<bullet> t) \<le> val ([i]\<cdot>\<one>) + eint N"
    using  Groups.add_ac(2) g'_bound
    unfolding normal_cell_underlying_set
    using 0 normal_cell_underlying_set by auto
  thus  "\<And>x t. t # x \<in> condition_to_set (normal_cell m b) \<Longrightarrow>  val (SA_poly_to_Qp_poly m x g' \<bullet> t) \<le> eint M"
    using M_props(2) by fastforce
qed

lemma g'_val_bound':
  assumes "t \<in> \<O>\<^sub>p"
  assumes "val t = 0"
  assumes "x \<in> b"
  shows " val (SA_poly_to_Qp_poly m x g' \<bullet> t) \<le> eint M"
  by(intro g'_val_bound normal_cell_memI b_semialg assms val_ring_memE)

lemma S_mem_mod:
  assumes "k \<in> S"
  shows "to_Zp ([k]\<cdot>\<one>) (M + 1) = k"
proof-
  have 0: "k mod p ^ (M + 1) = k"
    using assms(1) 
    unfolding   S_def Int_iff by simp
  show 1: "to_Zp ([k]\<cdot>\<one>) (M+1) = k"
    using Qp_res_int_inc[of k "M + 1"] unfolding Qp_res_def 0 by auto 
qed
 
lemma S_mem_mod':
  assumes "k \<in> S"
  assumes "l \<ge> M+1"
  shows "to_Zp ([k]\<cdot>\<one>) l = k"
proof-
  have "p^(M+1) \<le> p^l"
    using assms 
    by (metis less_one not_less p_residues power_less_imp_less_exp power_one_right residues_def)
  hence "k < p^l"
    using assms(1) 
    unfolding   S_def Int_iff assms by simp 
  hence 0: "k mod p ^ l = k"
    using assms(1) 
    unfolding   S_def Int_iff assms by simp 
  show 1: "to_Zp ([k]\<cdot>\<one>) l = k"
    using Qp_res_int_inc[of k l] unfolding Qp_res_def 0 by auto 
qed

lemma zero_res_imp_val_bound:
  assumes "x \<in> \<O>\<^sub>p"
  assumes "(to_Zp x n) = 0"
  shows "val x \<ge> n"
proof- 
  have "val (x \<ominus> \<zero>) \<ge>n"
    apply(intro Qp_res_eqE assms zero_in_val_ring)
    unfolding Qp_res_def assms 
    using Qp_res_def Qp_res_zero by presburger
  thus ?thesis using assms 
    by (simp add: Qp.minus_zero val_ring_memE(2))
qed

lemma g_eval_val_ring:
  assumes "x \<in> b"
  assumes "y \<in> \<O>\<^sub>p"
  shows "(SA_poly_to_Qp_poly m x g \<bullet> y) \<in> \<O>\<^sub>p"
proof(intro val_ring_poly_eval SA_poly_to_Qp_poly_closed g_closed assms)
  show x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms b_closed by blast 
  show "\<And>i. SA_poly_to_Qp_poly m x g i \<in> \<O>\<^sub>p"
    by(intro integral_on_memE[of _ _ b] g_integral assms)
qed

lemma g_hensel_application:
  assumes "k \<in> S"
  assumes "x \<in> b_part k"
  shows "(\<exists>\<xi> \<in> \<O>\<^sub>p. SA_poly_to_Qp_poly m x g \<bullet> \<xi> = \<zero> \<and> to_Zp \<xi> (M+1) = k)"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms b_part_def by auto 
  have x_in_b: "x \<in> b"
    using assms b_part_def by auto 
  have k_val: "val ([k]\<cdot>\<one>) = 0"
    using assms unfolding S_def by auto 
  obtain \<beta> where \<beta>_def: "\<beta>\<in>carrier (residue_ring (p ^ (2 * M + 1))) \<and> 
                          to_Zp ([\<beta>] \<cdot> \<one>) (M + 1) = k \<and> 
                          to_Zp (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) (2 * M + 1) = 0"
    using assms unfolding b_part_alt by auto 
  have 0: "to_Zp ([k]\<cdot>\<one>) (M + 1) = k"
    using S_mem_mod assms by auto 
  have "val ([\<beta>] \<cdot> \<one> \<ominus> [k]\<cdot>\<one>) \<ge> M+1"
    apply(intro Qp_res_eqE val_ring_int_inc_closed )
    unfolding Qp_res_def 0
    using \<beta>_def by auto 
  hence 1: "val([\<beta>] \<cdot> \<one>) = val([k]\<cdot>\<one>)"
    using assms unfolding S_def 
    by (smt (verit, del_insts) Qp.int_inc_closed add_is_0 eint_defs(1) eint_ord_code(1) 
        eint_ord_trans eq_numeral_extra(2) k_val notin_closed of_nat_le_0_iff ultrametric_equal_eq)
  have beta_val: "val([\<beta>] \<cdot> \<one>) = 0"
    unfolding 1 k_val by auto 
  have 2: "\<exists>!\<alpha>. \<alpha> \<in> \<O>\<^sub>p \<and>
        SA_poly_to_Qp_poly m x g \<bullet> \<alpha> = \<zero> \<and>
        val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>) < val ([\<beta>] \<cdot> \<one> \<ominus> \<alpha>) \<and>
        val ([\<beta>] \<cdot> \<one> \<ominus> \<alpha>) = val (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>] \<cdot> \<one>)) - 
                              val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>)"
  proof(rule hensels_lemma(2)[of "SA_poly_to_Qp_poly m x g" "[\<beta>]\<cdot>\<one>"])
    show g_eval_closed: "SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)"
      using x_closed g_closed SA_poly_to_Qp_poly_closed by auto 
    show in_val_ring: "[\<beta>] \<cdot> \<one> \<in> \<O>\<^sub>p"
      using val_ring_int_inc_closed by presburger
    show gauss_norm: "0 \<le> gauss_norm (SA_poly_to_Qp_poly m x g)"
    proof- 
      have "\<And> j. val ((SA_poly_to_Qp_poly m x g) j) \<ge>0"
        using g_integral x_in_b val_ring_memE unfolding integral_on_def mem_Collect_eq
        by auto 
      thus " 0 \<le> gauss_norm (SA_poly_to_Qp_poly m x g)"
        unfolding gauss_norm_def by auto 
    qed
    show "eint 2 * val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>) < 
                  val (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>)"
    proof- 
    have closure:  "(SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) \<in> carrier Q\<^sub>p"
      by (simp add: UPQ.to_fun_closed \<open>SA_poly_to_Qp_poly m x g \<in> carrier (UP Q\<^sub>p)\<close>)
    have val_ring:  "(SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) \<in> \<O>\<^sub>p"
      using gauss_norm positive_gauss_norm_eval in_val_ring g_eval_closed by auto 
    have val_bound: "val (SA_poly_to_Qp_poly m x g \<bullet> [\<beta>] \<cdot> \<one>) \<ge> (2 * M + 1)"
      apply(intro zero_res_imp_val_bound val_ring)
      using \<beta>_def by auto 
    have g'_val_bound: "val (SA_poly_to_Qp_poly m x g' \<bullet> ([\<beta>] \<cdot> \<one>)) \<le> eint M"
    proof(rule g'_val_bound, unfold normal_cell_def condition_to_set.simps cell_def
            mem_Collect_eq list_tl list_hd, intro conjI)
      show "[\<beta>] \<cdot> \<one> # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        using x_closed by (simp add: Qp_pow_ConsI)
      show "x \<in> b"
        using x_in_b by auto 
      show "val ([\<beta>] \<cdot> \<one> \<ominus> \<zero>\<^bsub>SA m\<^esub> x) \<in> I[val (\<one>\<^bsub>SA m\<^esub> x) val (\<one>\<^bsub>SA m\<^esub> x)]"
      proof- 
        have 0: "[\<beta>] \<cdot> \<one> \<ominus> \<zero>\<^bsub>SA m\<^esub> x = [\<beta>] \<cdot> \<one>"
          using x_closed by (simp add: Qp.minus_zero SA_zeroE)
        have 1: "val (\<one>\<^bsub>SA m\<^esub> x) = 0"
          using x_closed val_one SA_oneE by auto
        show ?thesis 
          unfolding 0 1 beta_val 
          by(rule closed_interval_memI, auto)
      qed
    qed
    have eq: "UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one> 
                = (SA_poly_to_Qp_poly m x g' \<bullet> ([\<beta>] \<cdot> \<one>))"
      unfolding g'_def using x_closed g_closed SA_poly_to_Qp_poly_comm_pderiv 
      by presburger
    have "eint 2 * val (SA_poly_to_Qp_poly m x g' \<bullet> [\<beta>] \<cdot> \<one>) \<le> eint (2*M)"
      using g'_val_bound 
      by (metis Num.of_nat_simps(5) eint_nat_mult_mono of_nat_numeral times_eint_simps(1))
    thus ?thesis 
      using val_bound g'_val_bound unfolding eq 
      by (smt (verit, ccfv_threshold) Extended_Int.Suc_ile_eq Num.of_nat_simps(4) 
          eint_ord_trans notin_closed of_nat_1_eq_iff)
  qed
  qed
  then obtain \<xi> where \<xi>_def: 
    "\<xi> \<in> \<O>\<^sub>p \<and>
        SA_poly_to_Qp_poly m x g \<bullet> \<xi> = \<zero> \<and>
        val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>) < val ([\<beta>] \<cdot> \<one> \<ominus> \<xi>) \<and>
        val ([\<beta>] \<cdot> \<one> \<ominus> \<xi>) = val (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>] \<cdot> \<one>)) - 
                              val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>)"
    by blast 
  have "to_Zp \<xi> (M+1) = k"
  proof- 
    have "val (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>] \<cdot> \<one>)) - 
                              val (UPQ.pderiv (SA_poly_to_Qp_poly m x g) \<bullet> [\<beta>] \<cdot> \<one>) 
           \<ge> M+1"
    proof- 
      have 0: "val (SA_poly_to_Qp_poly m x g \<bullet> ([\<beta>] \<cdot> \<one>)) \<ge> 2 * M + 1"
        apply(intro zero_res_imp_val_bound g_eval_val_ring x_in_b
              val_ring_int_inc_closed)
        using \<beta>_def by auto 
      have 1: "val ((SA_poly_to_Qp_poly m x g') \<bullet> [\<beta>] \<cdot> \<one>)  \<le> M"
        by(intro g'_val_bound' val_ring_int_inc_closed beta_val x_in_b)
      have R: "\<And> (x::eint) y::eint. x \<ge> 2*M +1 \<Longrightarrow> y \<le> M \<Longrightarrow> x - y \<ge> M+1"
      proof-
        fix x y ::eint
        have "x \<ge> 2*M +1 \<longrightarrow> y \<le> M \<longrightarrow> x - y \<ge> M+1"
          by(induction x, induction y, auto)
        thus "x \<ge> 2*M +1 \<Longrightarrow> y \<le> M \<Longrightarrow> x - y \<ge> M+1"
          by auto 
      qed
      show ?thesis apply(rule R)
        using 0 apply blast
        by (metis 1 g'_def g_closed 
            A\<^sub>0_comp_refinement_i_pos_axioms SA_poly_to_Qp_poly_pderiv x_closed)
    qed
    hence "val ([\<beta>] \<cdot> \<one> \<ominus> \<xi>) \<ge> M+1"
      using \<xi>_def by presburger
    hence "to_Zp ([\<beta>] \<cdot> \<one>) (M+1) = to_Zp \<xi> (M+1)"
      by (metis Qp_res_def Qp_res_eqI' \<xi>_def val_ring_int_inc_closed)
    thus ?thesis 
      using \<beta>_def by presburger
  qed
  thus "\<exists>\<xi>\<in>\<O>\<^sub>p. SA_poly_to_Qp_poly m x g \<bullet> \<xi> = \<zero> \<and> to_Zp \<xi> (M + 1) = k"
    using \<xi>_def by auto 
qed

lemma deg_f_inds: 
"deg (SA m) f \<in> inds"
proof(rule ccontr)
  assume A: "deg (SA m) f \<notin> inds"
  then have "taylor_expansion (SA m) c f (deg (SA m) f) = \<zero>\<^bsub>SA m\<^esub>"
    using a_def f_taylor_cfs inds_def by auto
  then have "taylor_expansion (SA m) c f = \<zero>\<^bsub>UP (SA m)\<^esub>"
    by (metis UPSA.deg_ltrm UPSA.deg_nzero_nzero UPSA.monom_zero UPSA.trms_of_deg_leq_0 
        UPSA.trms_of_deg_leq_degree_f a_def a_deg local.a_closed)
  hence "f = \<zero>\<^bsub>UP (SA m)\<^esub>"
    using SA_units_not_zero a_def common_g_prems(4) by auto
  thus False 
    by (metis i_nonzero A\<^sub>0_comp_refinement_i_pos_axioms 
        UPSA.deg_zero bot_nat_0.extremum_unique i_inds inds_bounded)
qed

lemma g_semialg_root:
  assumes "k \<in> S" 
  shows "\<exists> \<xi> \<in> carrier (SA m). (\<forall> x \<in>  b_part k. \<xi> x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> x) (M+1) = k \<and> 
                                    SA_poly_to_Qp_poly m x g \<bullet> (\<xi> x) = \<zero>)"
proof-
  obtain \<xi> where \<xi>_def: 
      "\<xi>  = (\<lambda>x. (SOME \<xi> .  \<xi> \<in> \<O>\<^sub>p \<and> 
                           SA_poly_to_Qp_poly m x g \<bullet> \<xi> = \<zero> \<and> 
                           to_Zp \<xi> (M+1) = k))"
    by blast 
  have \<xi>_prop: "\<And>x. x \<in> b_part k \<Longrightarrow>  \<xi> x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> x) (M+1) = k \<and> 
                                    SA_poly_to_Qp_poly m x g \<bullet> (\<xi> x) = \<zero>"
    using assms g_hensel_application \<xi>_def 
    by (smt (verit, del_insts) someI_ex)
  have b_part_sub: "b_part k \<subseteq> b"
    unfolding b_part_def by auto 
  have k_pos: "k > 0"
    using assms S_def by auto 
  have semialg: "is_semialgebraic m (b_part k)"
    using b_part_semialg[of "nat k"]  k_pos by simp
  have \<xi>_val: "\<And> x. x \<in> b_part k \<Longrightarrow> val (\<xi> x) = 0"
  proof- 
    fix x assume A: "x \<in> b_part k"
    have 0: "to_Zp (\<xi> x) (M+1) = to_Zp ([k]\<cdot>\<one>) (M+1)"
      using \<xi>_prop A S_mem_mod assms by presburger
    have 1: "val (\<xi> x) = val ([k]\<cdot>\<one>)"
    proof- 
      have "M+1 \<le> val (\<xi> x \<ominus> [k] \<cdot> \<one>)"
        using Qp_res_eqE[of "\<xi> x" "[k]\<cdot>\<one>" "M+1"] 0 A 
        using Qp_res_def \<xi>_prop val_ring_int_inc_closed by presburger
      hence "val (\<xi> x \<ominus> [k] \<cdot> \<one>) > val ([k]\<cdot>\<one>)"
        by (smt (verit, best) IntE S_def add_is_0 assms eint_defs(1) eint_ord_code(1) 
            eint_ord_trans eq_numeral_extra(2) mem_Collect_eq not_less of_nat_le_0_iff)
      thus ?thesis 
        by (metis A Qp.int_inc_closed \<xi>_prop ultrametric_equal_eq val_ring_memE(2))
    qed
    show "val (\<xi> x) = 0"
      unfolding 1 
      using S_def assms by force
  qed
  have g_val_bound_xi: "\<And> x. x \<in> b_part k \<Longrightarrow> val (SA_poly_to_Qp_poly m x g' \<bullet> (\<xi> x)) \<le> eint (int M)"
    apply(intro g'_val_bound'  \<xi>_val)
    using  \<xi>_prop b_part_sub by auto 
  have "\<exists> \<eta> \<in> carrier (SA m). \<forall>x \<in> b_part k. \<eta> x = \<xi> x"
    apply(rule denef_lemma_2_3_on_subset[of _ g _ _ "M" k ], unfold g_deg)
    apply (simp add: f_deg)
           apply (simp add: g_closed)
          apply(simp add: semialg)
    using b_part_sub g_cfs_integral(1) apply auto[1]
    using \<xi>_prop apply auto[1]
       using deg_f_inds g_cfs_inds apply blast     
    using \<xi>_prop SA_poly_to_SA_fun_formula 
    apply (simp add: b_part_def g_closed val_ring_memE(2))
    using \<xi>_prop  apply simp
    using \<xi>_prop UPSA.pderiv_closed[of g m] g_closed g_val_bound_xi
          SA_poly_to_SA_fun_formula [of "UPSA.pderiv m g" m] 
    using Set.basic_monos(7) b_closed b_part_sub g'_def val_ring_memE(2) by auto
  then obtain \<eta> where \<eta>_def: "\<eta> \<in> carrier (SA m) \<and> (\<forall>x \<in> b_part k. \<eta> x = \<xi> x)"
    by blast
  have " \<forall>x\<in>b_part k. \<eta> x \<in> \<O>\<^sub>p \<and> to_Zp (\<eta> x) (M + 1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> \<eta> x = \<zero>"
    using \<xi>_prop \<eta>_def by auto 
  thus ?thesis using \<eta>_def 
    by blast
qed 

definition \<xi> where \<xi>_def: 
"\<xi> k = (SOME \<xi>. \<xi> \<in> carrier (SA m) \<and> (\<forall> x \<in>  b_part k. \<xi> x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> x) (M+1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> (\<xi> x) = \<zero>) )"

lemma \<xi>_prop:
  assumes "k \<in> S"
  shows "\<xi>  k\<in> carrier (SA m)"
        "x \<in> b_part k \<Longrightarrow> \<xi> k x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> k x) (M+1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> (\<xi> k x) = \<zero>"
proof- 
  obtain \<eta> where \<eta>_def: "\<eta> \<in> carrier (SA m) \<and> (\<forall> x \<in>  b_part k. \<eta> x \<in> \<O>\<^sub>p \<and> to_Zp (\<eta> x) (M+1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> (\<eta> x) = \<zero>)"
    using assms g_semialg_root by blast 
  have 0: "\<xi>  k\<in> carrier (SA m) \<and> (\<forall> x \<in>  b_part k. \<xi> k x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> k x) (M+1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> (\<xi> k x) = \<zero>) "
    apply(rule SomeE[of "\<xi> k" _ \<eta>])
    using \<xi>_def apply blast 
    by(rule \<eta>_def)
  show "\<xi>  k\<in> carrier (SA m)" using 0 by blast 
  show "x \<in> b_part k \<Longrightarrow> \<xi> k x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> k x) (M+1) = k \<and> SA_poly_to_Qp_poly m x g \<bullet> (\<xi> k x) = \<zero>"
    using 0 by blast 
qed

definition C where C_def: 
"C k = Cond m (b - (b_part k)) (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval"

lemma C_subset:
  assumes "k \<in> S"
  shows "condition_to_set (C k) \<subseteq> condition_to_set (normal_cell m b)"
proof- 
  have 0: "condition_to_set (C k) \<subseteq> condition_to_set (Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    unfolding C_def condition_to_set.simps cell_def by blast 
  have  "(Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval) \<in> normal_cell_decomp"
    unfolding normal_cell_decomp_def using assms by blast
  hence 1: " condition_to_set (Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval) \<subseteq> condition_to_set (normal_cell m b)"
    using assms normal_cell_decomp_is_decomp  
    by (meson is_cell_decomp_subset)
  show ?thesis using 0 1 by auto 
qed

lemma C_ubounded:
  assumes "k \<in> S"
  shows "SA_poly_ubounded p m g (center (C k)) (condition_to_set (C k)) (2*M)"
  apply(rule SA_poly_uboundedI[of _ _ _ _ "2*M"], rule g_closed) unfolding C_def center.simps
    apply(rule constant_fun_closed, blast) unfolding condition_to_set.simps cell_def apply blast
proof- 
  fix  x t i assume A0: " t # x   \<in> {as \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).       tl as \<in> b - b_part k \<and>
                val (lead_coeff as \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl as))
          \<in> I[val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl as)) val (\<zero>\<^bsub>SA m\<^esub> (tl as))]}"
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using A0 unfolding mem_Collect_eq list_hd 
    by (metis cartesian_power_head list_hd)
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using A0 unfolding mem_Collect_eq list_tl 
    by (metis Qp_pow_ConsE list_tl)
  have C0: "x \<in>  b - (b_part k)"
    using A0 unfolding mem_Collect_eq list_tl by blast 
  have C1: "t#x \<in> condition_to_set (C k)"
    unfolding C_def condition_to_set.simps cell_def using A0 by blast 
  hence C2: "t#x \<in> condition_to_set (normal_cell m b)"
    using C_subset assms by auto 
  have C3: "t \<in> \<O>\<^sub>p"
    apply(rule val_ring_memI) 
    using t_closed apply linarith
    using C2 unfolding normal_cell_underlying_set mem_Collect_eq list_hd 
    by (metis Qp.add.nat_pow_eone Qp.cring_simprules(6) val_of_nat_inc val_one)
  have C4: "t#x \<in> condition_to_set  (Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)" 
    using is_cell_decompE(2) is_partitionE(2) s_def C1  C_def padic_fields.cell_def padic_fields_axioms by force
  have C5: "k > 0"
  proof-
    have "k \<in> {0<..<p ^ (M + 1)}"
      using assms unfolding  S_def by blast 
    thus ?thesis 
      using greaterThanLessThan_iff by blast
  qed
  have C6: "x \<in> b - b_part k"
    using  C0 C5 by (smt int_nat_eq)
  have C7: "\<forall> \<alpha> \<in> \<O>\<^sub>p. to_Zp \<alpha> (M+1) = k \<longrightarrow> to_Zp (SA_poly_to_Qp_poly m x g \<bullet> \<alpha>) (2*M + 1) \<noteq> 0"
    using C6 b_closed unfolding b_part_def by blast
  have C8: "t#x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> b \<and> val (hd x) = 0 \<and> to_Zp (hd x) (M+1) = k}"
  proof-
    have d: "k \<in> {0<..<p ^ (M + 1)}"
      using assms unfolding  S_def by blast 
    have 000: "{x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> b \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) (M+1) = k} =
condition_to_set
(Cond m b (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>)) (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M+1))] \<cdot> \<one>)) \<zero>\<^bsub>SA m\<^esub>
closed_interval)"
      apply(rule cong_set_is_cell[of m b k "M+1"])
      using b_semialg apply auto[1]
      using assms unfolding S_def  apply blast
      using d greaterThanLessThan_iff apply blast
      using d greaterThanLessThan_iff by blast
    show "t # x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl x \<in> b \<and> val (lead_coeff x) = 0 \<and> to_Zp (lead_coeff x) (M + 1) = k}"
      unfolding 000 using C4  by blast 
  qed
  have C9: "val t = 0"
    using C8 unfolding mem_Collect_eq list_hd by blast 
  have C10: "to_Zp t (M+1) = k" 
    using C8 unfolding mem_Collect_eq list_hd by blast 
  have C11: "to_Zp (SA_poly_to_Qp_poly m x g \<bullet> t) (2*M + 1) \<noteq> 0"
    using C3 C7 C10 by blast 
  have C12: "(SA_poly_to_Qp_poly m x g \<bullet> t) \<in> \<O>\<^sub>p"
    apply(rule  val_ring_poly_eval, rule SA_poly_to_Qp_poly_closed, rule x_closed, rule g_closed)
    using g_integral C6 C3  apply (meson DiffE g_cfs_integral(2))
    using C3 by blast
  have C13: "to_Zp (SA_poly_to_Qp_poly m x g \<bullet> t) \<in> carrier Z\<^sub>p"
    using C12 val_ring_memE to_Zp_closed by blast 
  have C14: "val_Zp (to_Zp (SA_poly_to_Qp_poly m x g \<bullet> t)) \<le> 2*M"
    apply(rule below_val_Zp_zero) using C13 apply blast using C11  
    using semiring_norm(175) by presburger
  have C15: "UPQ.taylor_term (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t \<in> \<O>\<^sub>p"
  proof-
    have C150: "taylor_expansion Q\<^sub>p (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<in> \<O>\<^sub>p"
      apply(rule UPQ.UP_subring_taylor')
      using val_ring_subring apply blast
      apply(rule  SA_poly_to_Qp_poly_closed, rule x_closed, rule g_closed)
      using g_integral C6 C3  apply (meson DiffE g_cfs_integral(2))
      using x_closed unfolding constant_function_def restrict_def  
      using Qp.int_inc_closed val_of_int_inc val_ring_memI by presburger
    have C151: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) = [k] \<cdot> \<one>"
      unfolding constant_function_def restrict_def using x_closed by meson 
    have C152: "up_ring.monom (UP Q\<^sub>p) \<one> 1 \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) ([k] \<cdot> \<one>) 0 \<in> carrier (UP Q\<^sub>p)"
      apply(rule ring.ring_simprules)
      using UPQ.P.is_ring apply blast
      using UPQ.is_UP_monomE(1) UPQ.is_UP_monomI apply blast
      using Qp.int_inc_closed UPQ.is_UP_monomE(1) UPQ.monom_is_UP_monom(2) by blast
    have C153: "(up_ring.monom (UP Q\<^sub>p) \<one> 1 \<ominus>\<^bsub>UP Q\<^sub>p\<^esub> up_ring.monom (UP Q\<^sub>p) ([k] \<cdot> \<one>) 0) \<bullet> t =    t \<ominus> [k] \<cdot> \<one>"
    proof- 
      have C154: "up_ring.monom (UP Q\<^sub>p) \<one> 1 \<bullet> t = t"
        using Qp.nat_pow_eone UPQ.to_fun_monic_monom t_closed by blast
      have C155: "(up_ring.monom (UP Q\<^sub>p) ([k] \<cdot> \<one>) 0) \<bullet> t  = [k]\<cdot>\<one>"
        using Qp.int_inc_closed UPQ.to_fun_const t_closed by blast
      show ?thesis using C154 C155 
        using Qp.cring_simprules(6) Qp.int_inc_closed UPQ.is_UP_monomE(1) UPQ.monom_is_UP_monom(1) UPQ.to_fun_diff t_closed by presburger
    qed
    have C154: "UPQ.X_minus (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) [^]\<^bsub>UP Q\<^sub>p\<^esub> i \<bullet>  t =
              (t \<ominus> [k] \<cdot> \<one>)[^]i"
      unfolding C151 X_poly_minus_def X_poly_def to_polynomial_def
      using C152 C153  UPQ.to_fun_nat_pow t_closed by presburger
    have C155: "UPQ.taylor_term (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t  = 
        taylor_expansion Q\<^sub>p (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<otimes> (t \<ominus> [k] \<cdot> \<one>)[^]i"
      unfolding UPQ.taylor_term_def  using C150 C154 C152 C153
      unfolding X_poly_minus_def X_poly_def to_polynomial_def 
      using UPQ.to_fun_smult val_ring_memE 
      by (smt C151 UPQ.P.nat_pow_closed t_closed)
    show ?thesis unfolding C155 unfolding  C151
      apply(rule val_ring_times_closed)
      using C150 unfolding C151 apply blast
      apply(rule val_ring_nat_pow_closed)
      apply(rule val_ring_minus_closed) 
      using C3 apply blast
      using Qp.int_inc_closed val_of_int_inc val_ring_memI by blast
  qed
  have C16: "val (UPQ.taylor_term (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t) \<ge> 0"
    apply(rule val_ring_memE) using C15 by blast 
  have C17: "eint (2*M) \<le> val (UPQ.taylor_term (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t) + eint (int (2 * M))"
    using C16 by (metis Groups.add_ac(2) add_left_mono arith_simps(50))
  show " val (SA_poly_to_Qp_poly m x g \<bullet> t)
\<le> val (UPQ.taylor_term (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x) (SA_poly_to_Qp_poly m x g) i \<bullet> t) + eint (int (2 * M))"
   apply(rule order_trans[of _ "eint (2*M)"]) using C14 C12 
     apply (metis to_Zp_val) by( rule C17 )      
qed

definition D where D_def: 
"D k = Cond m (b_part k) (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval"

lemma D_subset:
  assumes "k \<in> S"
  shows "condition_to_set (D k) \<subseteq> condition_to_set (normal_cell m b)"
proof- 
  have 0: "condition_to_set (D k) \<subseteq> condition_to_set (Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval)"
    unfolding b_part_def D_def condition_to_set.simps cell_def by blast 
  have  "(Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval) \<in> normal_cell_decomp"
    unfolding normal_cell_decomp_def using assms by blast
  hence 1: " condition_to_set (Cond m b (\<cc>\<^bsub>m\<^esub> ([k]\<cdot>\<one>)) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval) \<subseteq> condition_to_set (normal_cell m b)"
    using assms normal_cell_decomp_is_decomp  
    by (meson is_cell_decomp_subset)
  show ?thesis using 0 1 by auto 
qed

definition D' where D'_def: 
"D' k =  Cond m (b_part k) (\<xi> k) (\<cc>\<^bsub>m\<^esub> ([(p^(M+1))]\<cdot>\<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval"

lemma D_ubounded:
  assumes "(k::nat) \<in> S"
  shows "condition_to_set (D k) = condition_to_set (D' k)"
        "SA_poly_ubounded p m g (center (D' k)) (condition_to_set (D' k)) (2*M)"
proof-
  have \<xi>_closed: "\<xi> k \<in> carrier (SA m)"
    using \<xi>_prop assms by blast 
  have k_pos: "k > 0"
    using assms greaterThanLessThan_iff unfolding S_def 
    by simp
  have D': "is_cell_condition (D' k)"
    unfolding D'_def apply(rule is_cell_conditionI')
    using b_part_semialg
    using Qp.int_inc_closed constant_fun_closed apply blast
       apply (simp add: \<xi>_closed)
      apply (meson Qp.int_inc_closed constant_fun_closed)
    apply blast
    by (simp add: is_convex_condition_def)
  have P0: "to_Zp ([k]\<cdot>\<one>) (M+1) = k"
  proof-
    have l: "k \<in> {0<..<p ^ (M + 1)}"
      using assms unfolding S_def by blast 
    hence uu: "k \<in> carrier (Zp_res_ring (M+1))"
      by (meson greaterThanLessThan_iff less_numeral_extra(1) p_residue_ring_car_memI pos_add_strict zle_add1_eq_le)
    have "to_Zp ([k]\<cdot>\<one>) (M+1) = k mod p^(M+1)"
      using Zp_int_inc_res[of k "M+1"] to_Zp_int_inc 
      by (metis Qp.int_add_pow)
    thus ?thesis  using greaterThanLessThan_iff[of k 0 "p^(M+1)"] l uu  
      by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(2))
  qed 
  have ink: "int (nat k) = k"
    using k_pos by linarith 
  have \<xi>_closure: "\<And>x. x \<in> b_part k \<Longrightarrow> \<xi> k x \<in> \<O>\<^sub>p"
    using \<xi>_prop assms by blast 
  show P1: "condition_to_set (D k) = condition_to_set (D' k)"
    apply(rule equalityI') 
  proof- 
    fix x assume At: "x \<in> condition_to_set (D k)" 
    show "x \<in> condition_to_set (D' k)"
      unfolding condition_to_set.simps D'_def 
      apply(rule cell_memI)
      using At unfolding D_def condition_to_set.simps cell_def apply blast
      using At unfolding D_def condition_to_set.simps cell_def apply blast
      apply(rule closed_interval_memI)
    proof- 
      have P10: "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = M+1"
      proof- 
        have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using At unfolding D_def condition_to_set.simps cell_def 
          using Qp_pow_ConsE(1) by blast
        have P000: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = [(p ^ (M + 1))] \<cdot> \<one>"
          using tl_x_closed Qp.int_inc_closed Qp_constE by blast
        show ?thesis unfolding P000 
          using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
      qed
      have P11:"tl x \<in> b_part k" 
        using At k_pos unfolding ink D_def condition_to_set.simps cell_def mem_Collect_eq  by blast 
      have P12: "to_Zp ((\<xi> k) (tl x)) (M+1) = k"
        using assms \<xi>_prop  P11 by blast 
      have \<xi>_tl_x_closed: "(\<xi> k) (tl x) \<in> carrier Q\<^sub>p"
        using assms \<xi>_prop P11 unfolding b_part_def 
        using val_ring_memE by presburger
      have P13: "(to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>)) (M+1) = 0"
        using P12 P0 Qp.int_inc_closed \<xi>_tl_x_closed res_diff_zero_fact'' to_Zp_closed 
              Qp.nat_inc_closed by presburger        
      have P14: "val_Zp ((to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))) \<ge> M+1"
      proof- 
        have p0: "(to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>)) \<in> carrier Z\<^sub>p"
          apply(rule Zp.ring_simprules)
           apply (meson \<xi>_tl_x_closed to_Zp_closed)
          apply(rule to_Zp_closed) by auto 
        have p1: "\<And>a j. a \<in> carrier Z\<^sub>p \<Longrightarrow> a j = 0 \<Longrightarrow> val_Zp a \<ge> j"
          by (metis Zp.add.l_cancel_one' Zp.cring_simprules(4) Zp.r_right_minus_eq val_Zp_dist_def val_Zp_dist_res_eq2 val_Zp_not_equal_ord_plus_minus zero_below_val_Zp)
        show ?thesis 
          by(rule p1, rule p0, rule P13)
      qed
      have P15: "to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>) =  (to_Zp ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>))"
        using \<xi>_prop P11  Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
             assms val_ring_nat_inc_closed by presburger
      have P16: "val ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>) = val_Zp  (to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))"
        using \<xi>_prop P11 Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
              \<xi>_prop(2) assms val_dist_to_Zp val_ring_nat_inc_closed 
        using Qp.nat_inc_closed \<xi>_tl_x_closed val_dist_sym by metis
      have P17: "val ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>) \<ge> M+1"
        using P14 unfolding P16 P15   by blast 
      have P12: "to_Zp ((\<xi> k) (tl x)) (M+1) = k"
        using \<xi>_prop  P11 P12 by force
      have hd_x_closed: "hd x \<in> carrier Q\<^sub>p"
        using At unfolding condition_to_set.simps cell_def D_def mem_Collect_eq  
        using Qp_pow_ConsE(2) by blast
      have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using At unfolding condition_to_set.simps cell_def D_def mem_Collect_eq  
        using Qp_pow_ConsE by blast
      have P18: " constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x) = [k]\<cdot>\<one>"
        using P11 Qp.int_inc_closed Qp_constE unfolding b_part_def by blast
      have P19: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = [(p ^ (M + 1))] \<cdot> \<one>"
        using tl_x_closed Qp.int_inc_closed Qp_constE by blast
      have P20: "(\<zero>\<^bsub>SA m\<^esub> (tl x)) = \<zero>"
        using tl_x_closed SA_zeroE by blast 
      have P21: "val ([(p ^ (M + 1))] \<cdot> \<one>) = M+1"
        using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
      have P22: "val ((hd x) \<ominus> [k]\<cdot>\<one>) \<ge> M+1"
        using At unfolding P18 P19 P20 P21   condition_to_set.simps  
          cell_def mem_Collect_eq D_def list_tl list_hd closed_interval_def 
        by (simp add: P18 Qp.int_add_pow)      have P23: "val ([k]\<cdot>\<one>) = 0"
        using assms unfolding S_def 
        by (simp add: Qp.int_add_pow)        
      have P24: "M+1 > 0"
        by simp
      have P25: "val ([k] \<cdot> \<one>) < val ((\<xi> k) (tl x) \<ominus> [k] \<cdot> \<one>)"
        apply(rule less_le_trans[of _ "eint (M+1)"])
         unfolding P23 apply (meson P24 eint_pow_int_is_pos of_nat_0_less_iff)
         using P17 by blast
      have P26: "  val ((\<xi> k) (tl x)) = val ([k]\<cdot>\<one>)"
        using P25 \<xi>_tl_x_closed by (metis Qp.nat_inc_closed ultrametric_equal_eq)
      have P27: "val ((hd x) \<ominus> [k]\<cdot>\<one>) > val ([k] \<cdot> \<one>)"
        apply(rule less_le_trans[of _ "eint (M+1)"])
        unfolding P23  apply (meson P24 eint_pow_int_is_pos of_nat_0_less_iff)
        using P22 by blast
      have P28: "val (hd x) = val ([k]\<cdot>\<one>)"
        using P27 hd_x_closed Qp.int_inc_closed ultrametric_equal_eq 
        by (metis Qp.nat_inc_closed)
      have P29: "val (lead_coeff x \<ominus> (\<xi> k) (tl x)) \<ge> M + 1"
        apply(rule Qp_isosceles[of _ "[k]\<cdot>\<one>"], rule hd_x_closed, blast, rule \<xi>_tl_x_closed)
        using P22 apply blast
        using P17 by linarith
      show "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) \<le> val (lead_coeff x \<ominus> (\<xi> k) (tl x))"
        unfolding P19 P21 by(rule P29)
      show "val (lead_coeff x \<ominus> (\<xi> k) (tl x)) \<le> val (\<zero>\<^bsub>SA m\<^esub> (tl x))"
        unfolding P20  using eint_ord_code(3) local.val_zero by presburger
    qed
  next fix x assume At: "x \<in> condition_to_set (D' k)"
    show "x \<in> condition_to_set (D k)"
      unfolding condition_to_set.simps D_def 
      apply(rule cell_memI)
      using At unfolding D'_def condition_to_set.simps cell_def apply blast
      using At unfolding D'_def condition_to_set.simps cell_def apply blast
      apply(rule closed_interval_memI)
    proof-
      have P10: "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = M+1"
      proof- 
        have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using At unfolding D'_def condition_to_set.simps cell_def 
          using Qp_pow_ConsE(1) by blast
        have P000: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = [(p ^ (M + 1))] \<cdot> \<one>"
          using tl_x_closed Qp.int_inc_closed Qp_constE by blast
        show ?thesis unfolding P000 
          using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
      qed
      have P11:"tl x \<in> b_part k" 
        using At k_pos unfolding ink D'_def condition_to_set.simps cell_def mem_Collect_eq  by blast 
      have P12: "to_Zp ((\<xi> k) (tl x)) (M+1) = k"
        using \<xi>_prop  P11 assms by blast
      have \<xi>_tl_x_closed: "(\<xi> k) (tl x) \<in> carrier Q\<^sub>p"
        using \<xi>_closure P11 unfolding b_part_def 
        using val_ring_memE by blast
      have P13: "(to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>)) (M+1) = 0"
        using P12 P0 Qp.nat_inc_closed \<xi>_tl_x_closed res_diff_zero_fact'' to_Zp_closed 
        by presburger
          have P14: "val_Zp ((to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))) \<ge> M+1"
      proof- 
        have p0: "(to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>)) \<in> carrier Z\<^sub>p"
          apply(rule Zp.ring_simprules)
           apply (meson \<xi>_tl_x_closed to_Zp_closed)
          apply(rule to_Zp_closed) by auto 
        have p1: "\<And>a j. a \<in> carrier Z\<^sub>p \<Longrightarrow> a j = 0 \<Longrightarrow> val_Zp a \<ge> j"
          by (metis Zp.add.l_cancel_one' Zp.cring_simprules(4) Zp.r_right_minus_eq val_Zp_dist_def val_Zp_dist_res_eq2 val_Zp_not_equal_ord_plus_minus zero_below_val_Zp)
        show ?thesis 
          by(rule p1, rule p0, rule P13)
      qed      
      have P15: "to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>) =  (to_Zp ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>))"
        using \<xi>_prop P11  Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
             assms val_ring_nat_inc_closed by presburger
      have P16: "val ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>) = val_Zp  (to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))"
        by (metis P11 Qp.int_inc_closed \<xi>_prop(2) assms  val_dist_to_Zp  val_ring_nat_inc_closed Qp.nat_inc_closed \<xi>_tl_x_closed val_dist_sym)
      have P17: "val ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>) \<ge> M+1"
        using P14 unfolding P16 P15   by blast 
          have P15: "to_Zp ((\<xi> k) (tl x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>) =  (to_Zp ((\<xi> k) (tl x) \<ominus> [k]\<cdot>\<one>))"
        using \<xi>_prop P11  Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
             assms val_ring_nat_inc_closed by presburger
      have hd_x_closed: "hd x \<in> carrier Q\<^sub>p"
        using At unfolding condition_to_set.simps cell_def D'_def mem_Collect_eq  
        using Qp_pow_ConsE(2) by blast
      have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using At unfolding condition_to_set.simps cell_def D'_def mem_Collect_eq  
        using Qp_pow_ConsE by blast
      have P18: " constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) (tl x) = [k]\<cdot>\<one>"
        using P11 Qp.int_inc_closed Qp_constE unfolding b_part_def by blast
      have P19: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x)) = [(p ^ (M + 1))] \<cdot> \<one>"
        using tl_x_closed Qp.int_inc_closed Qp_constE by blast
      have P20: "(\<zero>\<^bsub>SA m\<^esub> (tl x)) = \<zero>"
        using tl_x_closed SA_zeroE by blast 
      have P21: "val ([(p ^ (M + 1))] \<cdot> \<one>) = M+1"
        using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
      have P22: "val ((hd x) \<ominus> (\<xi> k) (tl x)) \<ge> M+1"
        using At unfolding P18 P19 P20 P21   condition_to_set.simps  
          cell_def mem_Collect_eq D'_def list_tl list_hd closed_interval_def by blast
      have int: "[k]\<cdot>\<one> = [int k]\<cdot>\<one>"
        by (simp add: Qp.int_add_pow)
      have P23: "val ([k]\<cdot>\<one>) = 0"
        using assms unfolding S_def Int_iff mem_Collect_eq int by blast 
      have P24: "M+1 > 0"
        by simp
      have P25: "val ([k] \<cdot> \<one>) < val ((\<xi> k) (tl x) \<ominus> [k] \<cdot> \<one>)"
        apply(rule less_le_trans[of _ "eint (M+1)"])
         unfolding P23 apply (meson P24 eint_pow_int_is_pos of_nat_0_less_iff)
         using P17 by blast
      have P26: "  val ((\<xi> k) (tl x)) = val ([k]\<cdot>\<one>)"
        using P25 \<xi>_tl_x_closed unfolding int by (metis Qp.int_inc_closed ultrametric_equal_eq)
      have P27: "val ((hd x) \<ominus> (\<xi> k) (tl x)) > val ([k] \<cdot> \<one>)"
        apply(rule less_le_trans[of _ "eint (M+1)"])
        unfolding P23  apply (meson P24 eint_pow_int_is_pos of_nat_0_less_iff)
        using P22 by blast
      have P29: "val (lead_coeff x \<ominus> [int k]\<cdot>\<one>) \<ge> M + 1"
        apply(rule Qp_isosceles[of _ "(\<xi> k) (tl x)"], rule hd_x_closed, rule \<xi>_tl_x_closed, blast)
        using P22 apply linarith
        using P17 \<xi>_tl_x_closed Qp.int_inc_closed[of k] val_dist_sym int by auto
      show "val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) (tl x))
    \<le> val (lead_coeff x \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([int k] \<cdot> \<one>) (tl x))"
        using P18  P29 unfolding P19 P21 int  by auto 
      show " val (lead_coeff x \<ominus> constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([int k] \<cdot> \<one>) (tl x)) \<le> val (\<zero>\<^bsub>SA m\<^esub> (tl x))"
        unfolding P20 int  using eint_ord_code(3) local.val_zero by presburger
    qed
  qed
  have int: "[k]\<cdot>\<one> = [int k]\<cdot>\<one>"
      by (simp add: Qp.int_add_pow)  
  have \<xi>_val: "\<And>x. x \<in> b_part k \<Longrightarrow> val (\<xi> k x) = 0"
  proof- fix x assume As: "x \<in> b_part k" 
    have \<xi>_x_closed: "\<xi> k x \<in> carrier Q\<^sub>p"
      using \<xi>_prop[of k] As SA_car_closed assms unfolding int b_part_def by blast
    have P12: "to_Zp (\<xi> k x) (M+1) = k"
      using assms \<xi>_prop As by blast 
    have P13: "(to_Zp (\<xi> k x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>)) (M+1) = 0"
      using assms P12 P0 Qp.int_inc_closed \<xi>_x_closed res_diff_zero_fact'' to_Zp_closed 
      unfolding int
      by presburger
    have P14: "val_Zp ((to_Zp (\<xi> k x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))) \<ge> M+1"
      using P13 to_Zp_closed \<xi>_x_closed assms  P0 P12 Q\<^sub>p_def Qp.int_inc_closed
            Zp.cring_simprules(4) Zp_def Zp_residue_eq2 equal_res_imp_val_diff_bound
            padic_fields.inc_of_diff padic_fields.inc_of_int padic_fields.val_of_inc 
            padic_fields_axioms to_Zp_int_inc val_of_int_inc val_ring_memI 
      unfolding int by metis 
    have P15: "to_Zp (\<xi> k x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>) =  (to_Zp (\<xi> k x \<ominus> [k]\<cdot>\<one>))"
      using \<xi>_prop As Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
            assms unfolding int by metis 
    have P16: "val (\<xi> k x \<ominus> [k]\<cdot>\<one>) = val_Zp  (to_Zp (\<xi> k x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp ([k]\<cdot>\<one>))"
      using \<xi>_prop As Qp.int_inc_closed to_Zp_minus val_of_int_inc val_ring_memI
            val_dist_to_Zp assms 
      unfolding int by (simp add: \<xi>_x_closed val_dist_sym)      
    have P17: "val (\<xi> k x \<ominus> [k]\<cdot>\<one>) \<ge> M+1"
      using P14 unfolding P16 P15   by blast 
    have P12: "to_Zp (\<xi> k x) (M+1) = k"
      using \<xi>_prop  As assms  unfolding int by blast 
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using As unfolding condition_to_set.simps cell_def b_part_def mem_Collect_eq  
      by blast                         
    have P18: " constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x = [k]\<cdot>\<one>"
      using As Qp.int_inc_closed Qp_constE unfolding int b_part_def by blast
    have P19: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) x) = [(p ^ (M + 1))] \<cdot> \<one>"
      using x_closed Qp.int_inc_closed Qp_constE by blast
    have P20: "(\<zero>\<^bsub>SA m\<^esub> x) = \<zero>"
      using x_closed SA_zeroE by blast 
    have P21: "val ([(p ^ (M + 1))] \<cdot> \<one>) = M+1"
      using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
    have P23: "val ([k]\<cdot>\<one>) = 0"
      using assms unfolding S_def int mem_Collect_eq Int_iff
      by auto  
    have P24: "M+1 > 0"
      by simp
    have P25: "val ([k] \<cdot> \<one>) < val (\<xi> k x \<ominus> [k] \<cdot> \<one>)"
      apply(rule less_le_trans[of _ "eint (M+1)"])
       unfolding P23 apply (meson P24 eint_pow_int_is_pos of_nat_0_less_iff)
       using P17 by blast
    have P26: "  val (\<xi> k x) = val ([k]\<cdot>\<one>)"
      using P25 \<xi>_x_closed Qp.int_inc_closed ultrametric_equal_eq assms
      unfolding int  by metis
    thus "val (\<xi> k x) = 0 " unfolding P23 
      by blast 
  qed
  show P2: "SA_poly_ubounded p m g (center (D' k)) (condition_to_set (D' k)) (2*M)"
    apply(rule SA_poly_uboundedI[of _ _ _ _ "2*M"], rule g_closed)
    unfolding D'_def center.simps 
    using \<xi>_prop assms apply blast
    unfolding condition_to_set.simps cell_def apply blast
    unfolding mem_Collect_eq list_tl list_hd
  proof-
    fix x t j 
    assume As: "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and>
             x \<in> b_part (int k) \<and> val (t \<ominus> \<xi> k x) \<in> I[val (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) x) val (\<zero>\<^bsub>SA m\<^esub> x)]"
    show    "val (SA_poly_to_Qp_poly m x g \<bullet> t) \<le> val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) + eint (int (2 * M))  "
    proof- 
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using As unfolding mem_Collect_eq  
        by (metis cartesian_power_head list_hd)
      have x_in_Fk: "x \<in> b_part k"
        using As k_pos unfolding list_tl mem_Collect_eq  
        by (metis arith_extra_simps(5) nat_int zless_iff_Suc_zadd)
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using As unfolding mem_Collect_eq  by (metis Qp_pow_ConsE(1) list_tl)
      have P0: " constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>) x = [k]\<cdot>\<one>"
        using x_closed Qp.int_inc_closed Qp_constE unfolding int by blast
      have P1: "(constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>) x) = [(p ^ (M + 1))] \<cdot> \<one>"
        using x_closed Qp.int_inc_closed Qp_constE by blast
      have P2: "(\<zero>\<^bsub>SA m\<^esub> x) = \<zero>"
        using x_closed SA_zeroE by blast 
      have P3: "val ([(p ^ (M + 1))] \<cdot> \<one>) = M+1"
        using Qp.int_nat_pow_rep ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
      have P4: "val (t \<ominus> (\<xi> k x)) \<ge> M+1"
        using As unfolding mem_Collect_eq  list_tl list_hd P0 P1 P2 P3 closed_interval_def by blast 
      have P5: "val ([k]\<cdot>\<one>) = 0"
        using assms unfolding S_def int by blast 
      have P6: "M+1 > 0"
        by simp
      have \<xi>_closed: "\<xi> k \<in> carrier (SA m)"
        using \<xi>_prop assms by blast 
      have P9: " \<xi> k x \<in> \<O>\<^sub>p"
        using \<xi>_prop x_in_Fk  assms by blast 
      have P10: "to_Zp (\<xi> k x) (M+1) = k" 
        using \<xi>_prop x_in_Fk assms by blast 
      have P11: "SA_poly_to_Qp_poly m x g \<bullet> (\<xi> k x) = \<zero>"
        using \<xi>_prop x_in_Fk assms by blast 
      show ?thesis
      proof(cases "j = 0")
        case True
        have T0: "(UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) = taylor_expansion Q\<^sub>p (\<xi> k x) (SA_poly_to_Qp_poly m x g) 0 \<otimes>( UPQ.X_minus (\<xi> k x) [^]\<^bsub>UP Q\<^sub>p\<^esub> j \<bullet> t)"
          unfolding True UPQ.taylor_term_def 
          apply(rule UPQ.to_fun_smult[of "UPQ.X_minus (\<xi> k x) [^]\<^bsub>UP Q\<^sub>p\<^esub> 0" t "taylor_expansion Q\<^sub>p (\<xi> k x) (SA_poly_to_Qp_poly m x g) 0"])
            apply(rule UPQ.P.nat_pow_closed, rule UPQ.X_minus_closed, rule SA_car_closed[of _ m], rule \<xi>_closed, rule x_closed
                  , rule t_closed) unfolding taylor_expansion_def 
          by(rule UPQ.cfs_closed, rule UPQ.sub_closed, rule UPQ.X_plus_closed, 
                rule SA_car_closed[of _ m], rule \<xi>_closed, rule x_closed, rule SA_poly_to_Qp_poly_closed, rule x_closed, rule g_closed)
        have T1: "taylor_expansion Q\<^sub>p (\<xi> k x) (SA_poly_to_Qp_poly m x g) 0 = \<zero>"
          using UPQ.taylor_zcf[of "SA_poly_to_Qp_poly m x g" "\<xi> k x"]
                SA_poly_to_Qp_poly_closed[of x m g] g_closed x_closed \<xi>_closed

          unfolding zcf_def UPQ.taylor_def P11 
          using SA_car_closed by blast
        have T2: "(UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) = \<zero>"
          unfolding T0 T1
          by(rule Qp.ring_simprules, rule UPQ.to_fun_closed,rule UPQ.P.nat_pow_closed,
                rule UPQ.X_minus_closed,rule SA_car_closed[of _ m], rule \<xi>_closed, rule x_closed, rule t_closed)                              
        show ?thesis unfolding T2 
          using eint_ord_code(3) local.val_zero plus_eint_simps(2) by presburger
      next
        case False
        obtain G where G_def: "G = SA_poly_to_Qp_poly m x g"
          by blast 
        obtain G' where G'_def: "G' = SA_poly_to_Qp_poly m x g'"
          by blast 
        have G_closed: "G \<in> carrier (UP Q\<^sub>p)"
          unfolding G_def 
          by(rule SA_poly_to_Qp_poly_closed, rule x_closed, rule g_closed)
        have G'_deriv: "G' = UPQ.pderiv G"
          unfolding G_def G'_def g'_def 
          using SA_poly_to_Qp_poly_pderiv  g_closed  x_closed by metis
        have \<xi>x_closed: "\<xi> k x \<in> carrier Q\<^sub>p"
          by(rule SA_car_closed[of _ m], rule \<xi>_closed, rule x_closed)
        have val_xi: "val (\<xi> (int k) x) = 0"
          using \<xi>_val x_in_Fk by presburger
        have F0: "val (G' \<bullet> (\<xi> k x)) \<le> M"
          unfolding G'_def 
          apply(rule g'_val_bound)
          apply(intro normal_cell_memI b_semialg)
          using assms x_in_Fk IntE b_part_def apply fastforce         
          using \<xi>x_closed apply blast 
          using val_xi by auto  
        have F1: "val(t \<ominus> (\<xi> k x)) \<ge> M+1"
          using As unfolding closed_interval_def mem_Collect_eq P1 P3 by blast 
        have \<xi>x_val: "val (\<xi> k x) = 0"
          apply(rule \<xi>_val) using As unfolding ink by blast 
        have t_val: "val t = 0"
        proof- 
          have 0: "(0::eint) < M+1"
            using M_pos eint_pow_int_is_pos of_nat_0_less_iff by auto 
          have "val(t \<ominus> \<xi> k x) > val (\<xi> k x)"
            apply(rule less_le_trans[of  "val (\<xi> k x)" "M+1" "val (t \<ominus> \<xi> k x)" ])
            using 0 unfolding \<xi>x_val
             apply blast
            using  F1  by blast 
          hence "val t = val (\<xi> k x)"
            using \<xi>x_closed t_closed 
            by (metis ultrametric_equal_eq)
          thus ?thesis unfolding \<xi>x_val by blast 
        qed
        obtain c1 where c1_def: "c1 = UPQ.taylor (\<xi> k x) G 1"
          by blast 
        have c1_closed: "c1 \<in> carrier Q\<^sub>p"
          unfolding c1_def
          by(rule UPQ.cfs_closed, rule UPQ.taylor_closed, rule G_closed, rule \<xi>x_closed)
        have F2: "(UPQ.taylor_term (\<xi> k x) G 1 \<bullet> t) = c1 \<otimes> (t \<ominus> \<xi> k x)"
          using c1_closed UPQ.to_fun_smult[of  "UPQ.X_minus (\<xi> k x) [^]\<^bsub>UP Q\<^sub>p\<^esub> 1 " t c1]
                UPQ.to_fun_nat_pow[of "UPQ.X_minus (\<xi> k x)" t 1] t_closed \<xi>_closed
                UPQ.to_fun_X_minus[of "\<xi> k x" t]
          unfolding UPQ.taylor_term_def c1_def UPQ.taylor_def
          using UPQ.P.nat_pow_eone UPQ.X_minus_closed UPQ.to_fun_smult \<xi>x_closed by presburger
        have F3: "UPQ.taylor_term (\<xi> k x) G 0  = \<zero>\<^bsub>UP Q\<^sub>p\<^esub>"
          unfolding UPQ.taylor_term_def
          using UPQ.taylor_zcf[of G "\<xi> k x"] G_closed \<xi>x_closed                                    
          unfolding G_def zcf_def UPQ.taylor_def P11 
          using UPQ.X_poly_minus_nat_pow_closed UPQ.smult_l_null by presburger
        have F4: "UPQ.taylor_term (\<xi> k x) G 0 \<bullet> t = \<zero>"
          unfolding F3 using t_closed UPQ.to_fun_zero by blast
        have F5: "\<exists> s \<in> \<O>\<^sub>p. G \<bullet> t = G \<bullet> \<xi> k x \<oplus> G' \<bullet> \<xi> k x \<otimes> (t \<ominus> \<xi> k x) \<oplus> s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)"
          unfolding G'_deriv apply(rule UPQ.taylor_deg_one_expansion_subring'[of _ \<O>\<^sub>p])
              apply(rule G_closed)
                using val_ring_subring apply blast
                unfolding G_def 
                using b_part_def g_cfs_integral(2) x_in_Fk apply fastforce
                 apply(rule val_ring_memI, rule \<xi>x_closed) using val_xi apply auto[1]
                apply(rule val_ring_memI, rule t_closed)
          by (simp add: t_val)
        then obtain s where s_def: "s \<in> \<O>\<^sub>p \<and> G \<bullet> t = G \<bullet> \<xi> k x \<oplus> G' \<bullet> \<xi> k x \<otimes> (t \<ominus> \<xi> k x) \<oplus> s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)"       
          by blast                            
        have F6: "G \<bullet> \<xi> k x = \<zero>"
          unfolding G_def 
          using P11 by blast
        have F7: "G' \<bullet> \<xi> k x = c1"

          using UPQ.pderiv_eval_deriv G_closed \<xi>x_closed
          unfolding c1_def G'_deriv derivative_def UPQ.taylor_def 
          by blast
        have F8: " G \<bullet> t = c1 \<otimes> (t \<ominus> \<xi> k x) \<oplus> s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)"
          using s_def unfolding F6 F7 
          using Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.cring_simprules(8) \<xi>x_closed c1_closed t_closed by presburger
        have F9: "val (c1 \<otimes> (t \<ominus> \<xi> k x)) = val c1 + val (t \<ominus> \<xi> k x)"
          by(rule val_mult, rule c1_closed, rule Qp.ring_simprules, rule t_closed, rule \<xi>x_closed)
        have F10: "val((t \<ominus> \<xi> k x) [^] (2::nat)) = val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x)"
        proof- 
          have 0: "t \<ominus> \<xi> k x \<in> carrier Q\<^sub>p"
            using \<xi>x_closed t_closed by blast
          show ?thesis 
          proof(cases "t \<ominus> \<xi> k x = \<zero>")
            case True
            then show ?thesis unfolding True 
              by (metis Qp.integral_iff Qp.nat_pow_zero Qp.zero_closed val_mult zero_neq_numeral)
          next
            case False
            have "t \<ominus> \<xi> k x \<in> nonzero Q\<^sub>p"
              using False 0 by (meson not_nonzero_Qp)
            hence "ord ((t \<ominus> \<xi> k x) [^] (2::nat)) = 2*ord ((t \<ominus> \<xi> k x))"
              using 0 False nonzero_nat_pow_ord by auto 
            then show ?thesis
              using False val_ord[of "t \<ominus> \<xi> k x"] val_ord[of "(t \<ominus> \<xi> k x)[^](2::nat)"]
              by (smt Qp_nat_pow_nonzero \<open>t \<ominus> \<xi> k x \<in> nonzero Q\<^sub>p\<close> plus_eint_simps(1))
          qed
        qed
        have F11: "val(s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)) = val s + val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x)"
          using s_def t_closed \<xi>x_closed val_mult[of s "(t \<ominus> \<xi> k x) [^] (2::nat)"]
          unfolding F10
          by (metis (no_types, lifting) Qp.cring_simprules(11) Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.nat_pow_closed val_ring_memE val_mult)
        have F12: "val(s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)) \<ge> val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x)"
          unfolding F11 using s_def val_ring_memE 
          by (metis F10 F11 Qp.cring_simprules(4) Qp.nat_pow_closed \<xi>x_closed t_closed val_val_ring_prod)
        have F13: "val(t \<ominus> \<xi> k x) > val c1"
        proof-
          have F130: "val c1 \<le> M"
            using F0 F7 by blast 
          have F131: "val c1 < M+1"
            apply(rule le_less_trans[of "val c1" M "M+1"], rule F130)
            using eint_ord_simps(2) by presburger
          show ?thesis apply(rule less_le_trans[of "val c1" "M+1"])
             apply (smt F130 F131 eint_ile eint_ord_code(1) eint_ord_simps(2))
            using F1 by blast 
        qed
        show ?thesis 
        proof(cases "t \<ominus> \<xi> k x = \<zero>")
          case True
          have T0: "(UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) = \<zero>"
            using UPQ.to_fun_taylor_term[of G t "\<xi> k x" j]
                  UPQ.taylor_closed[of G "\<xi> k x"]
                  UPQ.cfs_closed[of "UPQ.taylor (\<xi> k x) G" j]  
            unfolding True using False G_closed t_closed \<xi>x_closed 
            by (metis G_def Qp.cring_simprules(27) Qp.nat_pow_zero)
          show ?thesis unfolding T0 val_zero 
            using eint_ord_code(3) plus_eint_simps(2) by presburger
        next
          case F: False
          have F14: "val (t \<ominus> \<xi> k x) < \<infinity>"
            using D_def \<xi>x_closed t_closed Qp.cring_simprules(4) eint_ord_code(3) eint_ord_simps(4) val_ineq
            by (metis F)
          have F15: "val (c1 \<otimes> (t \<ominus> \<xi> k x)) < val (s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat))"
            apply(rule less_le_trans[of _ "val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x)"])
            unfolding F9 using F14 F13 False 
             apply (metis (no_types, lifting) Qp.m_comm Qp.minus_closed \<xi>x_closed c1_closed t_closed val_ineq_cancel_le' val_mult val_nonzero)
            by(rule F12)
          have F16: "val (G \<bullet> t) = val (c1 \<otimes> (t \<ominus> \<xi> k x))"
          proof-
            have 0: "c1 \<otimes> (t \<ominus> \<xi> k x) \<in> carrier Q\<^sub>p"
              by(rule Qp.ring_simprules, rule c1_closed,rule Qp.ring_simprules, rule t_closed, rule \<xi>x_closed)
            have 1: "(s \<otimes> (t \<ominus> \<xi> k x) [^] (2::nat)) \<in> carrier Q\<^sub>p"
              apply(rule Qp.ring_simprules, rule val_ring_memE)
              using s_def apply blast
              by( rule Qp.nat_pow_closed,rule Qp.ring_simprules, rule t_closed, rule \<xi>x_closed)
            show ?thesis using 0 1 F15 unfolding F8
              by (metis Qp.a_ac(2) val_ultrametric_noteq)
          qed
          have F17: "t \<ominus> \<xi> k x \<in> nonzero Q\<^sub>p"
            using F14 D_def \<xi>x_closed t_closed assms x_in_Fk  Qp.cring_simprules(4) not_nonzero_Qp
            by (metis F)
          have Case1: "j = 1 \<Longrightarrow> ?thesis"
          proof- assume C: "j = 1"
            show ?thesis using F16 F7 F2
              unfolding G_def M_pos 
              by (metis C F16 F2 G_def Suc_ile_eq eint_add_left_cancel_le 
                  eint_ord_code(2) mult_2 notin_closed of_nat_less_0_iff semiring_norm(51) val_of_int_inc zero_eint_def)
          qed
          have Case2: "j > 1 \<Longrightarrow> val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x) \<le> val((t \<ominus> \<xi> k x)[^]j)"
          proof- assume C: "j > 1"
            have F180: "ord (t \<ominus> \<xi> k x) > 0"
              using F17 F1 M_pos 
              by (smt P6 eint_ord_code(1) of_nat_0_less_iff val_ord)
            have F181: "ord ((t \<ominus> \<xi> k x)[^]j) = j*ord(t \<ominus> \<xi> k x)"
              using C F17 nonzero_nat_pow_ord by blast
            have F182: "ord(t \<ominus> \<xi> k x) + ord(t \<ominus> \<xi> k x) \<le>  j*ord(t \<ominus> \<xi> k x)"
            proof-
              have 0: "ord(t \<ominus> \<xi> k x) + ord(t \<ominus> \<xi> k x) = (2::int)*ord(t \<ominus> \<xi> k x)"
                by linarith
              have 1: "(2::int) \<le> j"
                using C by presburger 
              have 2: "\<And> a1 a2 a3. (a1::int) > 0 \<Longrightarrow> 0< a2 \<Longrightarrow>  a2 \<le> a3 \<Longrightarrow> a2*a1 \<le>a3*a1"
                by (smt mult_less_cancel_right)
              show ?thesis unfolding 0 by(rule 2, rule F180, presburger , rule 1)
            qed                                  
            have F183: "val((t \<ominus> \<xi> k x)[^]j) = eint(j*ord(t \<ominus> \<xi> k x))"
              using F17 F181 Qp_nat_pow_nonzero val_ord by presburger
            show ?thesis unfolding F183 using F182 F17 F180 
              using eint_ord_code(1) plus_eint_simps(1) val_ord by presburger
          qed
          have F17: "val((t \<ominus> \<xi> k x)[^]j) \<le> val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t)"
          proof- 
            have 00: " (UPQ.taylor_term (\<xi> k x) G j \<bullet> t) = UPQ.taylor (\<xi> k x) G j \<otimes> (t \<ominus> \<xi> k x) [^] j"
              by(rule UPQ.to_fun_taylor_term[of G t "\<xi> k x" j], rule G_closed,rule t_closed,rule \<xi>x_closed)
            have 01: "UPQ.taylor (\<xi> k x) G \<in> carrier (UP (Q\<^sub>p \<lparr>carrier := \<O>\<^sub>p\<rparr>))"
              unfolding UPQ.taylor_def
              apply(rule UPQ.UP_subring_taylor_closed, rule val_ring_subring, rule G_closed)
                unfolding G_def  As unfolding ink b_part_def 
                using b_part_def g_cfs_integral(2) x_in_Fk apply auto[1]                
              apply(rule val_ring_memI, rule \<xi>x_closed ) 
              by (metis \<xi>x_val order_refl)
            have 02: "UPQ.taylor (\<xi> k x) G j \<in> \<O>\<^sub>p"
              using 01  UPQ.UP_ring_subring_car[of \<O>\<^sub>p] val_ring_subring by blast
            have 03: "val (UPQ.taylor_term (\<xi> k x) G j \<bullet> t) = val(UPQ.taylor (\<xi> k x) G j) + val((t \<ominus> \<xi> k x) [^] j)"
              unfolding 00 apply(rule val_mult, rule UPQ.cfs_closed, rule UPQ.taylor_closed, rule G_closed, rule \<xi>x_closed)
              using F17 Qp.nonzero_closed by blast
            show " val ((t \<ominus> \<xi> k x) [^] j) \<le> val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t)"
              using 03 02 val_ring_memE[of "UPQ.taylor (\<xi> k x) G j "]
              unfolding G_def 
              by (metis "00" G_def Qp.cring_simprules(4) Qp.nat_pow_closed \<xi>x_closed t_closed val_val_ring_prod)
          qed
          have Case2_1: "1 < j \<Longrightarrow> val (G \<bullet> t) \<le> val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t)"
          proof- assume C: "1 < j"
            have 00: "val(t \<ominus> \<xi> k x) + val(t \<ominus> \<xi> k x) \<le> val((t \<ominus> \<xi> k x)[^]j)"
              using Case2 C by blast 
            have 01: "val (G \<bullet> t)  < val (t \<ominus> \<xi> k x) + val (t \<ominus> \<xi> k x)"
              unfolding F9 F16 using F14 F13 False assms
              using add.commute eint_add_left_cancel_less by fastforce
            have 02: "val (G \<bullet> t)  < val((t \<ominus> \<xi> k x)[^]j)"
              by(rule less_le_trans[of _ "val (t \<ominus> \<xi> k x) + val (t \<ominus> \<xi> k x)"], rule 01, rule 00)
            have 03: "val (G \<bullet> t) < val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t)"
              by(rule less_le_trans[of _ "val((t \<ominus> \<xi> k x)[^]j)"], rule 02, rule F17)
            have 04: "\<And>x y. (x::eint)<y \<Longrightarrow> x \<le> y"
              by auto 
            show" val (G \<bullet> t) \<le> val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t)"
              by(rule 04, rule 03) 
          qed
          have l: " eint (int (2 * M)) > 0"
            using M_pos by (meson eint_pow_int_is_pos nat_0_less_mult_iff of_nat_0_less_iff pos2)
          have k: "\<And>a. a \<le> a + eint (int (2 * M))"
            by (smt (verit, best) add.commute add.left_commute add_left_mono eint_ord_simps(1) padic_fields.add_cancel_eint_geq padic_fields_axioms plus_eint_simps(1) zle_iff_zadd)
          have l: "val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) \<le>val (UPQ.taylor_term (\<xi> k x) (SA_poly_to_Qp_poly m x g) j \<bullet> t) + eint (int (2 * M)) "
            by(rule k)    
          show ?thesis 
            apply(cases "j = 1", rule Case1, blast)
            using Case2_1 False l  unfolding G_def 
            by (metis G_def arith_extra_simps(5) arith_extra_simps(6) closed_interval_memE(1) closed_interval_memI eval_hom_def k less_one mult_2 nat_neq_iff padic_fields.eint_add_mono padic_fields_axioms)
        qed
      qed
    qed
  qed
qed

lemma normal_cell_final_decomp:
"\<exists> Cs. is_cell_decomp m Cs (condition_to_set (normal_cell m b)) \<and> 
        (\<forall>\<C> \<in> Cs. (\<exists>N. SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N ) )"
proof(rule refine_each_cell[of _ normal_cell_decomp], rule normal_cell_decomp_is_decomp)
  fix \<C> assume A: "\<C> \<in> normal_cell_decomp"
  then obtain k where k_def: "k \<in> S \<and> \<C> =  Cond m b (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>))
             (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval"
    unfolding normal_cell_decomp_def by blast 
  have \<C>_def: " \<C> =  Cond m b (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([k] \<cdot> \<one>))
        (constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) ([(p ^ (M + 1))] \<cdot> \<one>)) \<zero>\<^bsub>SA m\<^esub> closed_interval"
    using k_def by auto 
  have k_pos: "k > 0"
    using k_def unfolding S_def by auto  
  have ink: "int (nat k) = k"
    using k_pos by auto 
  obtain Cs where Cs_def:
    "Cs = {C k, D' k}"
    by blast 
  have decomp: "is_cell_decomp m Cs (condition_to_set \<C>)"
  proof(rule is_cell_decompI)
    show 1: "finite Cs"
      unfolding Cs_def by blast 
    have D'_set: "condition_to_set (D' k) = condition_to_set (D k)"
      using k_def ink D_ubounded[of "nat k"] by presburger
    have int_empty: "condition_to_set (D' k) \<inter> condition_to_set (C k) = {}"
      unfolding D'_set D_def C_def condition_to_set.simps cell_def by auto 
    have union: "condition_to_set (D' k) \<union> condition_to_set (C k) = condition_to_set \<C>"
      unfolding D'_set D_def C_def \<C>_def condition_to_set.simps cell_def 
      apply(rule equalityI') 
      unfolding Un_iff mem_Collect_eq b_part_def by auto 
    have D'_cond: "is_cell_condition (D' k)"
      unfolding D'_def apply(rule is_cell_conditionI')
          apply (metis b_part_semialg ink)
      using k_def \<xi>_prop apply blast 
        apply (meson Qp.int_inc_closed constant_fun_closed)
      unfolding is_convex_condition_def 
      by auto 
    have C_cond: "is_cell_condition (C k)"
      unfolding C_def apply(rule is_cell_conditionI')
          apply (metis b_semialg diff_is_semialgebraic b_part_semialg ink)
         apply (meson Qp.int_inc_closed constant_fun_closed)
        apply (meson Qp.int_inc_closed constant_fun_closed)
      unfolding is_convex_condition_def 
      by auto 
    have D'_arity: "arity (D' k) = m"
      unfolding D'_def arity.simps by auto 
    have C_arity: "arity (C k) = m"
      unfolding C_def arity.simps by auto 
    show 2: "\<And>s s'. s \<in> Cs \<Longrightarrow> s' \<in> Cs \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
      unfolding Cs_def using int_empty by blast
    show "condition_to_set ` Cs partitions condition_to_set \<C>"
      apply(rule is_partitionI, rule disjointI)
      using 2 apply blast 
      unfolding Cs_def using union by auto  
    show "\<And>s. s \<in> Cs \<Longrightarrow> is_cell_condition s \<and> arity s = m"
      using D'_cond C_cond D'_arity C_arity 
      unfolding Cs_def by auto 
    show "condition_to_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      unfolding \<C>_def condition_to_set.simps cell_def by auto 
  qed
  have 0: " \<exists>N. SA_poly_ubounded p m g (center (C k)) (condition_to_set (C k)) N"
    using k_def by (meson C_ubounded)
  have 1: " \<exists>N. SA_poly_ubounded p m g (center (D' k)) (condition_to_set (D' k)) N"
    using k_def ink D_ubounded[of "nat k"] by auto   
  have "is_cell_decomp m Cs (condition_to_set \<C>) \<and>
              (\<forall>\<C>\<in>Cs. \<exists>N. SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N)"
    using 0 1 decomp unfolding Cs_def by auto 
  thus "\<exists>Cs. is_cell_decomp m Cs (condition_to_set \<C>) \<and>
              (\<forall>\<C>\<in>Cs. \<exists>N. SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N)"
    by auto 
qed

lemma B_final_decomp:
"\<exists> Cs. is_cell_decomp m Cs (condition_to_set B) \<and> 
        (\<forall>\<C> \<in> Cs. \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N  )"
proof- 
  obtain Cs where Cs_def: "is_cell_decomp m Cs (condition_to_set (normal_cell m b)) \<and> 
        (\<forall>\<C> \<in> Cs. \<exists>N. SA_poly_ubounded p m g (center \<C>) (condition_to_set \<C>) N  )"
    using normal_cell_final_decomp by blast 
  show ?thesis 
    apply(rule transfer_decomp_ubounded)
    using Cs_def by auto 
qed

end

context A\<^sub>0_comp_refinement_i_zero
begin

lemma f_sum:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  shows "(SA_poly_to_Qp_poly m x f \<bullet> t) = 
              a i x \<otimes> (t \<ominus> c x) [^] i \<oplus> (\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j)"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms 
    by (meson Set.basic_monos(7) b_semialg is_semialgebraic_closed)
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms 
    by (metis (no_types, lifting) A\<^sub>0_comp_refinement.b_subset 
        A\<^sub>0_comp_refinement_axioms DiffE \<C>_mem_hd list.sel(1) subsetD)
  have term_closed: "\<And>j. j \<in> inds \<Longrightarrow> a j x \<otimes> (t \<ominus> c x) [^] j \<in> carrier Q\<^sub>p"
    by(intro Qp.ring_simprules Qp.nat_pow_closed SA_car_closed[of c m] 
          c_closed x_closed a_eval t_closed)
  have 0: "t#x \<in> condition_to_set \<C>"
    using assms b_subset by auto 
  have 1: "SA_poly_to_SA_fun m f (t # x) = (\<Oplus>i\<in>inds. a i x \<otimes> (t \<ominus> c x) [^] i)"
      using f_eval_formula'[of "t#x"] 0
     unfolding list_tl list_hd
    by auto 
  have 2: "(\<Oplus>j\<in>inds. a j x \<otimes> (t \<ominus> c x) [^] j) = 
            a i x \<otimes> (t \<ominus> c x) [^] i \<oplus> (\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j)"
  proof- 
    have 20: "inds = insert i (inds - {i})"
      using i_inds by auto 
    have 21: "(\<Oplus>j\<in>insert i (inds - {i}). a j x \<otimes> (t \<ominus> c x) [^] j) = 
            a i x \<otimes> (t \<ominus> c x) [^] i \<oplus> (\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j)"
      apply(rule Qp.finsum_insert)
        using inds_finite apply blast
          apply auto[1]
        using term_closed x_closed i_inds by auto 
    show ?thesis using 20 21 by auto 
  qed
  have 3: "(SA_poly_to_Qp_poly m x f \<bullet> t) = (\<Oplus>j\<in>inds. a j x \<otimes> (t \<ominus> c x) [^] j)"
    using "1" SA_poly_to_SA_fun_formula f_closed t_closed x_closed by auto
  thus ?thesis using 2 by auto 
qed

lemma term_closed:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  assumes "j\<in>inds"
  shows "a j x \<otimes> (t \<ominus> c x) [^] j \<in> carrier Q\<^sub>p"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms 
    by (meson Set.basic_monos(7) b_semialg is_semialgebraic_closed)
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms 
    by (metis (no_types, lifting) DiffE Set.basic_monos(7) \<C>_mem_hd b_subset list.sel(1))
  show ?thesis 
   by(intro Qp.ring_simprules Qp.nat_pow_closed SA_car_closed[of c m] 
          c_closed x_closed a_eval t_closed)
qed

lemma term_val:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  assumes "j\<in>inds - {i}"
  shows "val(a i x \<otimes> (t \<ominus> c x) [^] i) < val(a j x \<otimes> (t \<ominus> c x) [^] j)"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using assms 
    by (meson Set.basic_monos(7) b_semialg is_semialgebraic_closed)
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms 
    by (metis (no_types, lifting) DiffE Set.basic_monos(7) \<C>_mem_hd b_subset list.sel(1))
  have "j > 0"
    using assms unfolding i_zero by auto 
  thus ?thesis  
    using i_unique_min[of j x] assms H_eval[of j x] H_eval[of 0 x]
          x_closed t_closed 
    unfolding i_zero by (metis DiffE H_val' i_inds i_zero)
qed
  
lemma sum_closed:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  shows "(\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j) \<in> carrier Q\<^sub>p"
  by(intro Qp.finsum_closed, rule, intro term_closed assms, auto)

lemma sum_val:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  shows "val(a i x \<otimes> (t \<ominus> c x) [^] i) < val (\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j)"
proof- 
  have 0: "a i x \<otimes> (t \<ominus> c x) [^] i \<noteq> \<zero>"
    using assms 
    by (metis (no_types, lifting) Group.nat_pow_0 H_eval H_nonzero Set.basic_monos(7) 
          b_closed i_inds i_zero)
  show ?thesis 
  proof(intro finsum_val_ultrametric'')
    show "(\<lambda>j. a j x \<otimes> (t \<ominus> c x) [^] j) \<in> inds - {i} \<rightarrow> carrier Q\<^sub>p"
      using assms term_closed by auto 
    show " finite (inds - {i})"
      using inds_finite by auto 
    show "\<And>j. j \<in> inds - {i} \<Longrightarrow> 
          val (a i x \<otimes> (t \<ominus> c x) [^] i) < val (a j x \<otimes> (t \<ominus> c x) [^] j)"
      by(intro term_val assms, auto)
    show "val (a i x \<otimes> (t \<ominus> c x) [^] i) < \<infinity>"
      unfolding val_def using 0 by auto 
  qed
qed

lemma f_val:
  assumes "x \<in> b"
  assumes "t#x \<in> condition_to_set B"
  shows "val (SA_poly_to_Qp_poly m x f \<bullet> t) = val(a i x \<otimes> (t \<ominus> c x) [^] i)"
proof- 
  have 0: "(SA_poly_to_Qp_poly m x f \<bullet> t) = 
                a i x \<otimes> (t \<ominus> c x) [^] i \<oplus> (\<Oplus>j\<in>inds - {i}. a j x \<otimes> (t \<ominus> c x) [^] j)"
    by(intro f_sum assms)
  have 1: "\<And> x y. x \<in> carrier Q\<^sub>p \<Longrightarrow> y \<in> carrier Q\<^sub>p \<Longrightarrow> val y > val x \<Longrightarrow> val (x \<oplus> y) = val x"
    using val_ultrametric_noteq Qp.a_comm by metis
  show ?thesis
    unfolding 0 
    by(intro 1 term_closed assms i_inds sum_closed sum_val)
qed

lemma taylor_term:
  assumes "t#x \<in> condition_to_set B"
  shows "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) j \<bullet> t = a j x \<otimes> (t \<ominus> c x) [^] j"
proof-
  have xb: "x \<in> b"
    using assms unfolding B_eq condition_to_set.simps cell_def by auto 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using xb b_closed by blast
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms \<C>_mem_hd b_subset in_mono by fastforce
  have 0: "UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) j \<bullet> t =   
            taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) j \<odot>\<^bsub>UP Q\<^sub>p\<^esub>
                X_poly_minus Q\<^sub>p (c x) [^]\<^bsub>UP Q\<^sub>p\<^esub> j \<bullet>  t"
    unfolding UPQ.taylor_term_def by auto 
  have 1: "taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) j = a j x"
    using assms unfolding a_def 
    using SA_poly_to_Qp_poly_taylor_cfs b_closed common_g_prems(1) common_g_prems(2)  x_closed
    by presburger
  have 2: "(X_poly_minus Q\<^sub>p (c x) [^]\<^bsub>UP Q\<^sub>p\<^esub> j \<bullet> t) = (t \<ominus> (c x))[^]j"
    using x_closed t_closed 
    by (metis A\<^sub>0_comp_refinement.common_g_prems(2) A\<^sub>0_comp_refinement_axioms
        SA_car_closed UPQ.X_minus_closed UPQ.to_fun_X_minus UPQ.to_fun_nat_pow)
  have 3: "a j x \<odot>\<^bsub>UP Q\<^sub>p\<^esub> X_poly_minus Q\<^sub>p (c x) [^]\<^bsub>UP Q\<^sub>p\<^esub> j \<bullet> t = 
          a j x \<otimes> (X_poly_minus Q\<^sub>p (c x) [^]\<^bsub>UP Q\<^sub>p\<^esub> j \<bullet> t)"
    using SA_car_closed UPQ.X_poly_minus_nat_pow_closed UPQ.to_fun_smult 
        a_eval common_g_prems(2) t_closed x_closed by presburger
  show ?thesis 
    unfolding 0 1 2 3 by auto 
qed

lemma term_not_in_inds:
  assumes "t#x \<in> condition_to_set B"
  assumes "j \<notin> inds"
  shows "a j x \<otimes> (t \<ominus> c x) [^] j = \<zero>"
proof- 
  have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    by (metis (no_types, lifting) A\<^sub>0_comp_refinement.B_cell A\<^sub>0_comp_refinement.B_eq
        A\<^sub>0_comp_refinement_axioms assms cartesian_power_tail cell_condition_set_memE(1)
        list.sel(3))
  have t_closed: "t \<in> carrier Q\<^sub>p"
    using assms \<C>_mem_hd b_subset in_mono by fastforce
  have 0: "a j x = \<zero>"
    by(intro inds_non_memE assms x_closed)
  have 1: "(t \<ominus> c x) [^] j \<in> carrier Q\<^sub>p"
    by(intro Qp.nat_pow_closed Qp.ring_simprules c_closed 
          SA_car_closed[of c m] t_closed x_closed)
  show ?thesis unfolding 0 using 1 by auto 
qed

lemma ubounded: "SA_poly_ubounded p m f c (condition_to_set B) 0"
  apply(rule SA_poly_uboundedI[of _ _ _ _ ])
     apply(rule f_closed, rule c_closed)
  using B_eq  condition_to_set.simps cell_def apply blast 
proof- 
  fix x t j assume A: "t # x \<in> condition_to_set B"
  have 0: "x \<in> b"
    using A unfolding B_eq condition_to_set.simps cell_def by auto 
  have 1: "val (SA_poly_to_Qp_poly m x f \<bullet> t) = val(a i x \<otimes> (t \<ominus> c x) [^] i)"
    by(intro f_val A 0)
  have 2: "(UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) j \<bullet> t) 
            = a j x \<otimes> (t \<ominus> c x) [^] j"
    by(intro taylor_term A)
  have 3: "val (a i x \<otimes> (t \<ominus> c x) [^] i) \<le> val (a j x \<otimes> (t \<ominus> c x) [^] j)"
  proof(cases "j \<in> inds")
    case True
    show ?thesis
      apply(cases "i = j", blast)
      using term_val  by (metis "0" A H_ineq H_val' True i_inds)
  next
    case False
    have "a j x \<otimes> (t \<ominus> c x) [^] j = \<zero>"
      using A inds_def False term_not_in_inds by blast
    then show ?thesis 
      using val_zero by auto 
  qed
  show "val (SA_poly_to_Qp_poly m x f \<bullet> t)
       \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) j \<bullet> t) + eint 0"
    unfolding 0 1 2 using 3 by (simp add: eint_0)
qed
end

context denef_cell_decomp_I_induct_reduction
begin

lemma(in A\<^sub>0_comp_refinement) decomp:
  assumes "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
  shows "\<exists> Cs. is_cell_decomp m Cs (condition_to_set B) \<and> 
        (\<forall>\<C> \<in> Cs. \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N  )"
proof(cases "i > 0")
  case True
  interpret A\<^sub>0_comp_refinement_i_pos
    using A\<^sub>0_comp_refinement_axioms True assms
    unfolding A\<^sub>0_comp_refinement_i_pos_def A\<^sub>0_comp_refinement_i_pos_axioms_def
              Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
  show ?thesis using B_final_decomp by auto 
next
  case False
  have i_zero: "i = 0"
    using False by auto 
  show "\<exists>Cs. is_cell_decomp m Cs (condition_to_set B) \<and>
       (\<forall>\<C>\<in>Cs. \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N)"
  proof(cases "\<forall> j \<in> inds - {i}. \<forall> x \<in> b. val (H 0 x) < val (H j x)")
    case T: True
    have T0: "(\<forall>j x. j \<in> inds \<longrightarrow> 0 < j \<longrightarrow> x \<in> b \<longrightarrow> val (H 0 x) < val (H j x))"
      using T i_zero by blast
    interpret  A\<^sub>0_comp_refinement_i_zero _ _ _ _ _ _ _ _  _ _ _ _ _ B b
      using A\<^sub>0_comp_refinement_axioms T i_zero T0 assms
      unfolding A\<^sub>0_comp_refinement_i_zero_def A\<^sub>0_comp_refinement_i_zero_axioms_def
            Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
    have "is_cell_decomp m {B} (condition_to_set B) \<and>
       (\<forall>\<C>\<in>{B} . \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N)"
      apply(intro conjI ballI)
       apply (metis A\<^sub>0_comp_refinement.B_eq A\<^sub>0_comp_refinement_axioms
          B_cell arity.simps condition_to_set_cell_decomp)
      using B_eq ubounded by force        
    thus ?thesis 
      by blast      
  next
    case F: False
    obtain j x where jx_def: "j \<in> inds- {i} \<and> x \<in> b \<and> val (H 0 x) \<ge> val (H j x)"
      using F i_inds i_zero linorder_le_less_linear by blast
    have x_in_b: "x \<in> b"
      using jx_def by blast
    have F0: "val (H 0 x) \<le> val (H j x)"
      using x_in_b jx_def i_zero H_ineq by blast
    hence F1: "val (H 0 x) = val (H j x)"
      using jx_def by auto 
    have F2: "\<And>y. y \<in> b \<Longrightarrow> val (H i y) = val (H j y)"
      apply(rule static_ord_typeE(2)[of  "H ` inds" b "H i" "H j" x], rule static)
      using i_inds jx_def jx_def F1 i_zero 
      by auto 
    have F3: "\<And>j' x. j' \<in> inds \<Longrightarrow> x \<in> b \<Longrightarrow> val (H j x) \<le> val (H j' x)"
      using F2 H_ineq by auto 
    have F4: "A\<^sub>0_comp_refinement p d \<C> A c a1 a2 I f m B b \<phi> j H"
      apply(intro A\<^sub>0_comp_refinement.intro  common_refinement_locale_axioms )
      unfolding A\<^sub>0_comp_refinement_axioms_def 
      using assms F3 H_def common_g_prems(3) jx_def B_cell B_eq b_subset static by auto 
    interpret  A\<^sub>0_comp_refinement_i_pos _ _ _ _ _ _ _ _ _ _ _ _ _ B b _ j 
      using F4 jx_def i_zero assms
      unfolding A\<^sub>0_comp_refinement_i_pos_def
                A\<^sub>0_comp_refinement_i_pos_axioms_def 
                Q\<^sub>p_def Z\<^sub>p_def \<iota>_def 
      by auto 
    show ?thesis 
      using B_final_decomp by auto 
  qed 
qed

lemma A\<^sub>0_comp_final_decomp:
  assumes "inds \<noteq> {}"
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and> 
          (\<forall>B\<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
proof-
  obtain S where S_def: "(is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and>
                           (\<forall>B\<in>S. (\<exists> \<phi>. \<phi> \<in> Units (SA m) \<and> center B = c \<and> l_bound B = \<phi>  \<and>
                                         u_bound B = \<phi> \<and> boundary_condition B = closed_interval)))"
    using A\<^sub>0_comp_decomp by blast 
  show ?thesis 
    apply(rule refine_each_cell[of _ S])
    using S_def apply blast  
  proof- 
    fix B assume A: "B \<in> S"
    obtain b where b_def: "b = fibre_set B"
      by blast 
    obtain \<phi> where \<phi>_def: " \<phi> \<in> Units (SA m) \<and> center B = c \<and> l_bound B = \<phi> \<and> u_bound B = \<phi> \<and>
                             boundary_condition B = closed_interval"
      using A S_def by blast 
    have B_eq: "B = Cond m b c \<phi> \<phi> closed_interval"
      using A \<phi>_def b_def condition_decomp' S_def is_cell_decompE(4) 
      by metis 
    have  \<phi>_closed: "\<phi> \<in> carrier (SA m)"
      using \<phi>_def SA_Units_closed by blast 
    have \<phi>_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<noteq> \<zero>"
      using \<phi>_def SA_Units_memE' by blast
    have \<phi>_nonzero': "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<phi> x \<in> nonzero Q\<^sub>p"
      using \<phi>_closed \<phi>_nonzero SA_car_memE(3) unfolding nonzero_def by blast 
    have B_cell_cond: "is_cell_condition B"
      using A S_def is_cell_decompE by meson 
    have B0_semialg: "is_semialgebraic m b"
      using B_eq B_cell_cond is_cell_conditionE by blast
    obtain H where H_def: "H = (\<lambda>i. a i \<otimes>\<^bsub>SA m\<^esub>\<phi>[^]\<^bsub>SA m\<^esub> i)"
      by blast 
    have H_closed: "\<And> i. i \<in> inds \<Longrightarrow>  H i \<in> carrier (SA m)"
      unfolding H_def using inds_memE \<phi>_closed SA_Units_closed[of _ m]
      by blast
    have H_unit: "\<And>i. i \<in> inds \<Longrightarrow> H i \<in> Units (SA m)"
      unfolding H_def using inds_memE \<phi>_def R.Units_pow_closed by blast
    have H_eval: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x = a i x \<otimes> (\<phi> x [^] i)"
      unfolding H_def using \<phi>_closed inds_memE a_closed SA_mult SA_nat_pow by presburger
    have H_nonzero: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<noteq> \<zero>"
      using H_unit SA_Units_memE' by blast            
    have H_nonzero': "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> H i x \<in> nonzero Q\<^sub>p"
      unfolding nonzero_def mem_Collect_eq using SA_car_memE(3) H_closed H_nonzero by blast 
    have H_ord: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> ord (H i x) = ord (a i x) + i*ord(\<phi> x)"
      using H_eval \<phi>_nonzero inds_memE ord_mult nonzero_nat_pow_ord 
      by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero')
    have H_val: "\<And>x i. i \<in> inds \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> val (H i x) = val (a i x) + val (\<phi> x [^] i)"
      using  \<phi>_nonzero inds_memE  H_eval val_mult 
      by (metis Qp_nat_pow_nonzero SA_Units_nonzero \<phi>_nonzero' val_mult0)
    have b_semialg: "is_semialgebraic m b"
      using b_def B0_semialg by linarith
    have "\<exists>Bs. finite Bs \<and> Bs partitions b \<and> (\<forall>b\<in>Bs. is_semialgebraic m b \<and> static_order_type (H ` inds) b)"
      apply(rule static_order_type_decomp[of "H ` inds" m b])
      using inds_finite apply blast 
      using H_unit apply blast
      using b_semialg  by auto 
    then obtain Bs0 where Bs0_def: "finite Bs0 \<and> Bs0 partitions b \<and> (\<forall>b\<in>Bs0. is_semialgebraic m b \<and>
                                 static_order_type (H ` inds) b)"
      by blast 
    obtain Bs where Bs_def: "Bs = Bs0 - {{}}"
      by blast 
    have Bs_finite: "finite Bs"
      using Bs_def Bs0_def  by blast
    have Bs_semialg: "\<And>b. b \<in> Bs \<Longrightarrow> is_semialgebraic m b"
      using Bs_def Bs0_def  by blast 
    have Bs_partitions: "Bs partitions b"
      unfolding Bs_def apply(rule is_partitionI)
      using Bs0_def is_partitionE Generated_Boolean_Algebra.disjoint_def apply fastforce
      using Bs0_def is_partitionE(2)[of Bs0 b] by auto 
    have Bs_covers: "\<Union> Bs = b"
      using Bs_partitions is_partitionE[of Bs b] by auto 
    have Bs_static_order_type: "\<And>b'. b' \<in> Bs \<Longrightarrow> static_order_type (H ` inds) b'"
      using Bs_def Bs0_def by auto 
    have B_vals: "\<And>x. x \<in> condition_to_set B \<Longrightarrow> val (hd x \<ominus> c (tl x)) = val (\<phi> (tl x))"
      apply(rule basic_trans_rules(24))
      unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq closed_interval_def
       apply blast by blast 
    obtain T where T_def: "T = (\<lambda>b. Cond m b c \<phi> \<phi> closed_interval)"
      by blast 
    have a_closed: "H ` inds \<subseteq> carrier (SA m)"
      using H_unit SA_Units_closed by blast 
    have T_part: "condition_to_set ` T ` Bs partitions condition_to_set B"
    proof(rule is_partitionI)
      show "disjoint (condition_to_set ` T ` Bs)"
      proof(rule disjointI)
        fix x y assume A: "x \<in> condition_to_set ` T ` Bs" " y \<in> condition_to_set ` T ` Bs" "x  \<noteq> y "
        obtain x' where x'_def: "x' \<in> Bs \<and> x = condition_to_set (T x')"
          using A by blast 
        obtain y' where y'_def: "y' \<in> Bs \<and> y = condition_to_set (T y')"
          using A by blast 
        have x'_def': " x = condition_to_set (T x')"
          using x'_def by blast 
        have y'_def': " y = condition_to_set (T y')"
          using y'_def by blast 
        have "x' \<noteq> y'"
          using x'_def y'_def A by auto 
        hence 0:"x' \<inter> y' = {}"
          using Bs_partitions is_partitionE disjointE x'_def y'_def by blast
        show "x \<inter> y = {}"
          apply(rule equalityI')
          unfolding x'_def' y'_def' T_def condition_to_set.simps cell_def using 0 apply blast 
          by blast 
      qed
      show " \<Union> (condition_to_set ` T ` Bs) = condition_to_set B"
      proof 
        show " \<Union> (condition_to_set ` T ` Bs) \<subseteq> condition_to_set B"
        proof fix x assume A: " x \<in> \<Union> (condition_to_set ` T ` Bs)"
          then obtain b' where b_def: "b' \<in> Bs \<and> x \<in>  condition_to_set (T b')"
            by blast 
          have 0: "H ` inds \<subseteq> carrier (SA m)"
            using H_unit SA_Units_closed by blast 
          have 1: "H ` inds \<noteq> {}"
            using assms by blast
          have 2: "finite (H ` inds)"
            using inds_finite by blast 
          have 3: "b' \<subseteq> b"
            using  Bs_covers b_def by auto 
          show " x \<in> condition_to_set B"
            using 3 b_def unfolding T_def B_eq condition_to_set.simps cell_def mem_Collect_eq by blast 
        qed
        show "condition_to_set B \<subseteq> \<Union> (condition_to_set ` T ` Bs)"
        proof fix x assume A: "x \<in> condition_to_set B"
          have tl: "tl x \<in> b"
            using A unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq by blast 
          then obtain b' where b'_def: "b' \<in> Bs \<and> tl x \<in> b'"
            using Bs_covers by auto 
          have "x \<in> condition_to_set (T b')"
            unfolding T_def condition_to_set.simps
            apply(rule cell_memI)
            using A unfolding B_eq condition_to_set.simps cell_def apply blast 
            using b'_def apply blast
            using A unfolding B_eq condition_to_set.simps cell_def mem_Collect_eq by blast 
          thus "x \<in> \<Union> (condition_to_set ` T ` Bs) "
            using b'_def Bs_def Bs_covers by auto 
        qed
      qed
    qed
    have T_decomp: "is_cell_decomp m (T ` Bs) (condition_to_set B)"
      apply(rule is_cell_decompI)
      using Bs_finite apply blast 
      using T_part apply blast
      unfolding T_def 
      using arity.simps B_eq Bs_semialg change_of_fibres B_cell_cond apply blast
      unfolding B_eq condition_to_set.simps cell_def apply blast
    proof- fix s s' assume A: "s \<in> (\<lambda>b. Cond m b c \<phi> \<phi> closed_interval) ` Bs"
        "s' \<in> (\<lambda>b. Cond m b c \<phi> \<phi> closed_interval) ` Bs" "s \<noteq> s'" 
      obtain A where A_def: "A \<in> Bs \<and> s' = Cond m A c \<phi> \<phi> closed_interval" using A  by blast 
      obtain b' where b_def: "b' \<in> Bs \<and> s  = Cond m b' c \<phi> \<phi> closed_interval" using A  by blast 
      have s'_def: "s' = Cond m A c \<phi> \<phi> closed_interval" using A_def by blast
      have s_def: "s = Cond m b' c \<phi> \<phi> closed_interval" using b_def by blast 
      have 0: "A \<noteq> b'"
        using A A_def b_def by blast
      have 1: "A \<inter> b' = {}"
        using Bs_partitions is_partitionE disjointE A_def b_def 0 by blast 
      show "condition_to_set s \<inter> condition_to_set s' = {}"
        unfolding s'_def s_def condition_to_set.simps cell_def 
        using 1 by blast 
    qed
    show "\<exists>S. is_cell_decomp m S (condition_to_set B) \<and>
               (\<forall>C\<in>S. \<exists>N. SA_poly_ubounded p m f (center C) (condition_to_set C) N)"
      apply(rule refine_each_cell[of _ "T ` Bs"], rule T_decomp )
    proof- 
      fix C assume A': "C \<in> T ` Bs"
      obtain b' where b'_def: "b' \<in> Bs \<and> C = T b'"
        using A' by auto 
      have i_ex: "\<exists>i \<in> inds. \<forall> x \<in> b'. \<forall> j \<in> inds. val (H i x) \<le> val (H j x)"
      proof- 
        obtain x where x_def: "x \<in> b'"
          using Bs_def b'_def by blast
        obtain Y where Y_def: "Y = ((\<lambda> i. val (H i x))` inds)"
          by blast 
        have "\<exists>i \<in> inds. val (H i x) = Min Y"
        proof- 
          have "finite Y"
            using Y_def inds_finite by auto 
          then obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> Y \<and> \<alpha> = Min Y"
            using Min_in assms Y_def by blast 
          thus ?thesis unfolding Y_def by blast 
        qed
        then obtain i where i_def: "i \<in> inds \<and> val (H i x) = Min Y"
          by blast 
        have i_eq: "val (H i x) = Min Y"
          using i_def by auto 
        have i_ineq: "\<And> j. j \<in> inds \<Longrightarrow> val (H i x) \<le> val (H j x)"
          unfolding i_eq  apply(rule MinE[of Y])
          unfolding Y_def using inds_finite  by auto 
        have i_min: " \<forall>x\<in>b'. \<forall>j\<in>inds. val (H i x) \<le> val (H j x)"
        proof
          fix y 
          assume A0: "y \<in> b'"
          show "\<forall>j\<in>inds. val (H i y) \<le> val (H j y)"
          proof fix j assume A1: "j \<in> inds"
            have 1: "\<And> a (b::eint). a < b \<Longrightarrow> a \<le> b"
              by auto 
            have 2: "\<And> a (b::eint). a = b \<Longrightarrow> a \<le> b"
              by auto
            show " val (H i y) \<le> val (H j y)"
            proof(cases "val (H i x) < val (H j x)")
              case True
              show ?thesis
                apply(intro 1 static_ord_typeE[of "H ` inds" b' "H i" "H j" x y])
                using A0 A1 b'_def Bs_static_order_type i_def x_def True by auto   
            next
              case False
              then have F0: "val (H i x) = val (H j x)"
                using i_ineq[of j] A1 by auto 
              show ?thesis
                apply(intro 2 static_ord_typeE[of "H ` inds" b' "H i" "H j" x y])
                using A0 A1 b'_def Bs_static_order_type i_def x_def F0 by auto  
            qed
          qed
        qed
        thus ?thesis using i_def by auto 
      qed
      then obtain i where i_def: "i\<in>inds \<and> (\<forall>x\<in>b'. \<forall>j\<in>inds. val (H i x) \<le> val (H j x))"
        by blast 
      interpret A\<^sub>0_comp_refinement _ _ _ _ _ _ _ _ _ _ _ _ _ "T b'" b' \<phi> i H
        unfolding Z\<^sub>p_def Q\<^sub>p_def \<iota>_def apply auto 
      proof
        show "\<phi> \<in> Units (SA m)"
          using \<phi>_def by force
        show "is_cell_condition (T b')"
          using T_decomp b'_def is_cell_decompE(3) by blast
        show "T b' = Cond m b' c \<phi> \<phi> closed_interval"
          unfolding T_def by auto 
        show "condition_to_set (T b') \<subseteq> condition_to_set \<C> - A\<^sub>0"
        proof- 
          have 0: "condition_to_set B \<subseteq> condition_to_set \<C> - A\<^sub>0"
            apply(rule is_cell_decomp_subset[of m S])
            using S_def A by auto 
          have 1: "condition_to_set (T b') \<subseteq> condition_to_set B"
            apply(rule is_cell_decomp_subset[of m "T ` Bs"])
            using b'_def T_decomp by auto 
          show ?thesis using 0 1 by auto 
        qed
        show "i \<in> inds"
          using i_def by auto 
        show "H = (\<lambda>i. a i \<otimes>\<^bsub>SA m\<^esub> \<phi> [^]\<^bsub>SA m\<^esub> i)"
          using H_def by fastforce
        show "\<And>j x. j \<in> inds \<Longrightarrow> x \<in> b' \<Longrightarrow> val (H i x) \<le> val (H j x)"
          using i_def by fastforce
        show "b' \<noteq> {}"
          using b'_def Bs_def by auto 
        show "static_order_type (H ` inds) b'"
          using Bs_static_order_type b'_def by auto 
      qed
      show " \<exists>S. is_cell_decomp m S (condition_to_set C) \<and>
               (\<forall>C\<in>S. \<exists>N. SA_poly_ubounded p m f (center C) (condition_to_set C) N)"
        using deriv_bounded assms b'_def decomp by auto 
    qed
  qed
qed
      
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Finishing the Proof\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Denef's proof begins with a preliminary cell decomposition of $Q_p^{m+1}$ so that property 
      $I_d$ holds on each constituent cell. This lemma establishes that we may begin our proof of 
      $I_{d+1}$ by assuming our domain of decomposition is already a cell in such a decomposition, 
      rather than all of $Q_p^{m+1}$. \<close>


context denef_cell_decomp_I_induct_reduction
begin


lemma reduction_decomp:
  shows "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and> 
                          (\<forall>B \<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
proof(cases "inds = {}")
  case True
  have T0: "\<And>x. x \<in> condition_to_set \<C> \<Longrightarrow> SA_poly_to_SA_fun m f x = \<zero>"
    unfolding f_eval_formula' True Qp.finsum_empty by blast 
  have T1: " SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) 0"
    apply(rule SA_poly_uboundedI[of _ _ _ _ 0])
       apply (simp add: f_closed)
    using c_closed \<C>_def center.simps apply presburger
    using \<C>_def apply (simp add: cell_subset)         
  proof- 
    fix x t i assume A1: "t # x \<in> condition_to_set \<C>"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A1 Qp_pow_ConsE[of "t#x" m] unfolding \<C>_def condition_to_set.simps cell_def 
      by (metis (no_types, lifting) list_tl mem_Collect_eq)
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using A1 Qp_pow_ConsE[of "t#x" m] unfolding \<C>_def condition_to_set.simps cell_def 
      by (metis (no_types, lifting) list_hd mem_Collect_eq)
    have cx_closed: "c x \<in> carrier Q\<^sub>p"
      using c_closed x_closed  a_eval 
      by (meson SA_car_closed)
    have xinA: "x \<in> A"
      using A1 condition_to_set_memE' \<C>_cond \<C>_def by blast             
    then have T10: "SA_poly_to_SA_fun m f (t#x) = \<zero>"
      using A1 T0 by blast 
    then have T11: "(SA_poly_to_Qp_poly m x f \<bullet> t) = \<zero>"
      using SA_poly_to_SA_fun_formula[of f m x t] t_closed x_closed f_closed by blast
    have T12: "i \<notin> inds"
      unfolding True by blast 
    have T13: "A \<subseteq> SA_zero_set m (taylor_expansion (SA m) c f i)"
      by (metis A_semialg T12 a_def f_taylor_cfs inds_def mem_Collect_eq padic_fields.SA_zero_set_of_zero padic_fields.is_semialgebraic_closed padic_fields_axioms)
    have T14: "UPQ.taylor_term (center \<C> x) (SA_poly_to_Qp_poly m x f) i \<bullet> t =
  taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i \<otimes> (t \<ominus> c x) [^] i  "
      using  t_closed cx_closed  c_closed x_closed  UPQ.to_fun_taylor_term[of "SA_poly_to_Qp_poly m x f" t "c x" i]
        SA_poly_to_Qp_poly_closed[of x m f] unfolding UPQ.taylor_def \<C>_def center.simps 
      using f_closed by fastforce                   
    have T15: "taylor_expansion Q\<^sub>p (c x) (SA_poly_to_Qp_poly m x f) i = taylor_expansion (SA m) c f i x"
      using ring_hom_ring.homh[of "SA m" Q\<^sub>p "eval_hom x"] c_closed x_closed eval_hom_is_SA_hom[of x m] poly_lift_hom_comm_taylor_expansion_cf[of Q\<^sub>p "eval_hom x" m f c i] 
      unfolding eval_hom_def SA_poly_to_Qp_poly_def
      using Qp.cring f_closed by blast            
    have T16: "taylor_expansion (SA m) c f i x = \<zero>"
      using T13 xinA  unfolding SA_zero_set_def by blast
    have T17: "UPQ.taylor_term (center \<C> x) (SA_poly_to_Qp_poly m x f) i \<bullet> t = \<zero>"
      using T14 t_closed cx_closed unfolding T15 T16 
      using Qp.cring_simprules(26) Qp.minus_closed Qp.nat_pow_closed by presburger
    show "val (SA_poly_to_Qp_poly m x f \<bullet> t)
       \<le> val (UPQ.taylor_term (center \<C> x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint 0"
      unfolding T17 val_zero 
      by (metis eint_ord_simps(3) plus_eq_infty_iff_eint)
  qed
  have T2: "is_cell_decomp m {\<C>} (condition_to_set \<C>)"
    apply(rule is_cell_decompI) apply blast 
       apply(rule is_partitionI) 
        apply(rule disjointI) apply blast apply blast
    using \<C>_cond  \<C>_def  
    using arity.simps apply blast
    using \<C>_cond  \<C>_def  
     apply (metis arity.simps is_cellI is_cell_subset)
    by blast 
  have T3: "(\<forall>A\<in>{\<C>}. SA_poly_ubounded p m f (center A) (condition_to_set A) 0)"
    using T1 by blast 
    then show ?thesis using T2 T3 by blast 
next
  case False
  have F0: "\<exists>S. is_cell_decomp m S (condition_to_set \<C> - A\<^sub>0) \<and> (\<forall>B\<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using False A\<^sub>0_comp_final_decomp by auto 
  have F1: "\<exists>S. is_cell_decomp m S A\<^sub>0 \<and> 
                          (\<forall>B \<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using A\<^sub>0_decomp False
    by auto 
  obtain S0 where S0_def: "is_cell_decomp m S0 (condition_to_set \<C> - A\<^sub>0) \<and> (\<forall>B\<in>S0. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using F0 by auto 
  obtain S1 where S1_def: "is_cell_decomp m S1 A\<^sub>0 \<and> 
                          (\<forall>B \<in>S1. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using F1 by auto 
  have 0: "is_cell_decomp m (S0 \<union> S1) (condition_to_set \<C>)"
    apply(intro is_cell_decompI is_partitionI disjointI)
    using S0_def S1_def is_cell_decompE apply blast 
  proof-
    show "\<And>s s'. s \<in> S0 \<union> S1 \<Longrightarrow> s' \<in> S0 \<union> S1 \<Longrightarrow> s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
    proof- 
      fix s s' 
      assume A: "s \<in> S0 \<union> S1" "s' \<in> S0 \<union> S1" "s \<noteq> s'"
      show "condition_to_set s \<inter> condition_to_set s' = {}"
        apply(cases "s \<in> S0", cases "s' \<in> S0")
        using S0_def is_cell_decompE(5) A  apply meson
        using A is_cell_decomp_subset[of m S0 "condition_to_set \<C> - A\<^sub>0" s] is_cell_decomp_subset[of m S1 A\<^sub>0 s'] 
              S0_def S1_def apply blast
        apply(cases "s' \<in> S0")
        using A is_cell_decomp_subset[of m S0 "condition_to_set \<C> - A\<^sub>0" s'] is_cell_decomp_subset[of m S1 A\<^sub>0 s] 
              S0_def S1_def apply blast
        using S1_def is_cell_decompE(5) A  by blast
    qed
    thus "\<And>A B. A \<in> condition_to_set ` (S0 \<union> S1) \<Longrightarrow> B \<in> condition_to_set ` (S0 \<union> S1) \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}"
      by blast
    have 0: "condition_to_set \<C> = (condition_to_set \<C> - A\<^sub>0) \<union> A\<^sub>0"
      using A\<^sub>0_def by blast 
    have 1: "\<Union> (condition_to_set ` S0) = condition_to_set \<C> - A\<^sub>0"
      using S0_def is_cell_decompE(2) is_partitionE(2)   by blast 
    have 2: "\<Union> (condition_to_set ` S1) = A\<^sub>0"
      using S1_def is_cell_decompE(2) is_partitionE(2)   by blast 
    have 3: "\<Union> (condition_to_set ` (S0 \<union> S1)) = \<Union> (condition_to_set ` S0) \<union> \<Union> (condition_to_set ` S1)"
      by blast 
    show "\<Union> (condition_to_set ` (S0 \<union> S1)) = condition_to_set \<C>"
      using 0 1 2 S0_def S1_def is_cell_decompE(2) is_partitionE(2) 
             "3" by presburger
    show "\<And>s. s \<in> S0 \<union> S1 \<Longrightarrow> is_cell_condition s \<and> arity s = m"
      using S0_def S1_def is_cell_decompE by blast 
    show "condition_to_set \<C> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      unfolding \<C>_def condition_to_set.simps cell_def by auto 
  qed
  have 1: "(\<forall>B\<in> S0 \<union> S1. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using S0_def S1_def by auto 
  have 2: "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
    using deriv_bounded by auto 
  show "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and>
        (\<forall>B\<in>S. \<exists>N. SA_poly_ubounded p m f (center B) (condition_to_set B) N)"
    using 2  0 1 by auto 
qed

end

context common_decomp_proof_context
begin

text\<open>The final proof of the theorem proceeds as follows: We can invoke the lemma 
     denef\_I\_proof\_by\_property to reduce the result to showing that the carrier of $\mathbb{Q}_p^{m+1}$
     satisfies denef\_I\_property for some arbitrary m and f. We can then pass to a cell 
     decomposition of $\mathbb{Q}_p^{m+1}$ for which the conclusion of denef\_I holds for the 
     derivative of f. We then further decompose the cells to get that the taylor coefficients of f
     are either zero or units on each cell's fibres. Finally, we replace f with an equivalent
     polynomial g which satisfies the premises of the denef\_cell\_decomp\_I\_induct\_reduction 
     locale, and after a locale interpretation we can infer the result directly from 
     denef\_cell\_decomp\_I\_induct\_reduction.reduction\_decomp. \<close>

theorem denef_I:
"denef_I p (Suc d)"
proof(rule denef_I_proof_by_property)
  fix m f 
  assume A: "f \<in> carrier (UP (SA m))" "deg (SA m) f \<le> Suc d"
  obtain f' where f'_def: "f' = UPSA.pderiv m f"
    by blast 
  have deg_f': "deg (SA m) f' \<le> d"
    using A  unfolding f'_def  
    using UPSA.pderiv_deg_bound by blast
  have f'_closed: "f' \<in> carrier (UP (SA m))"
    unfolding f'_def using A(1) UPSA.pderiv_closed by blast
  obtain S where S_def: "is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> 
                           (\<forall>A\<in>S. (\<exists>N. SA_poly_ubounded p m f' (center A) (condition_to_set A) N))"
    using f'_def deg_f' common_decomp_proof_context_axioms A(1) UPSA.pderiv_closed
    unfolding common_decomp_proof_context_def  denef_I_def denef_I_axioms_def Q\<^sub>p_def Z\<^sub>p_def
    by metis
  show "denef_I_property m f (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  proof(intro denef_I_property_refine[of _ S], auto simp: S_def)
    fix \<C> assume B: "\<C> \<in> S"
    have deriv_ubounded: "\<exists>N. SA_poly_ubounded p m f' (center \<C>) (condition_to_set \<C>) N" 
      using B S_def by auto 
    show " denef_I_property m f (condition_to_set \<C>)"
    proof- 
      obtain C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
        by (metis  S_def B equal_CondI is_cell_decompE(4))
      have \<C>_cell_cond: "is_cell_condition \<C>"
        using B S_def is_cell_decompE(3) by blast
      have c_closed: "c \<in> carrier (SA m)"
        using \<C>_cell_cond is_cell_conditionE''(5) params by blast
      obtain a where a_def: "a = taylor_expansion (SA m) c f"
        by blast 
      have a_closed: "a \<in> carrier (UP (SA m))"
        unfolding a_def by(intro taylor_expansion_closed A c_closed)
      have cell_decomp: "is_cell_decomp m (decomp_by_cfs m a \<C>) (condition_to_set \<C>)"
        by(intro decomp_by_cfs_is_decomp A \<C>_cell_cond a_closed,
              unfold params arity.simps, auto)
      show "denef_I_property m f (condition_to_set \<C>)"
      proof(intro denef_I_property_refine[of _ "decomp_by_cfs m a \<C>"] conjI a_closed
                    decomp_by_cfs_is_decomp)
        show 1: " is_cell_condition \<C>"
          using B S_def is_cell_decompE by auto 
        show 2: " arity \<C> = m"
          unfolding params arity.simps by auto 
        show "\<forall>\<C>\<in>decomp_by_cfs m a \<C>. denef_I_property m f (condition_to_set \<C>)"
        proof
          fix \<B> assume C: "\<B> \<in> decomp_by_cfs m a \<C>"
          then obtain b where b_def: "b \<in> poly_cfs_part m a C \<and> \<B> = refine_fibres \<C> b"
            unfolding decomp_by_cfs_def params fibre_set.simps by auto 
          have b_eq: "b \<in> poly_cfs_part m a C"
            using b_def by auto 
          have B_eq: "\<B> = Cond m b c a1 a2 I"
            using b_def unfolding params refine_fibres_def arity.simps l_bound.simps u_bound.simps 
                      boundary_condition.simps center.simps by auto 
          obtain g where g_def: "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) 
                    (poly_unit_replacement m a b)"
            by blast 
          have prems: "is_semialgebraic m C"
                      "f \<in> carrier (UP (SA m))"
                      "c \<in> carrier (SA m)"
                      "b \<in> poly_cfs_part m a C"
                      "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) (poly_unit_replacement m a b)"
            using b_def a_closed a_def 1 A g_def  unfolding params by auto 
          have g_props: "g \<in> carrier (UP (SA m))"
                        "\<And>x i . x \<in> b \<Longrightarrow> g i x = f i x"
                        "\<And> x i. x \<in> b \<Longrightarrow> UPSA.pderiv m g i x = UPSA.pderiv m f i x"
                        "\<And>x. x \<in> b \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
                        "\<And>x. x \<in> b \<Longrightarrow> SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = 
                                        SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
                        "\<And> i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or> 
                              taylor_expansion (SA m) c g i \<in> Units (SA m)"                        
            using prems  poly_unit_replacement_on_cfs_part_taylor[of m C f c b g] unfolding a_def
            by auto
          show "denef_I_property m f (condition_to_set \<B>)"
          proof(rule denef_I_property_replace[of _ _ g], intro A)
            show " \<And>x t. t # x \<in> condition_to_set \<B> \<Longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f "
            proof-
              fix x t 
              assume A: "t # x \<in> condition_to_set \<B>"
              show "SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f "
                apply(rule g_props)
                using A unfolding B_eq condition_to_set.simps cell_def by auto 
            qed
            have deriv:  " \<And>x t. t # x \<in> condition_to_set \<B> \<Longrightarrow> 
                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f)  "
            proof-
              fix x t 
              assume A: "t # x \<in> condition_to_set \<B>"
              show "SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                         SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
                apply(rule g_props)
                using A unfolding B_eq condition_to_set.simps cell_def by auto 
            qed
            show "denef_I_property m g (condition_to_set \<B>)"
            proof- 
              interpret denef_cell_decomp_I_induct_reduction _ _ _ _ _ \<B> b c a1 a2 I g m
                unfolding Q\<^sub>p_def Z\<^sub>p_def \<iota>_def apply auto
              proof
                show "g \<in> carrier (UP (SA m))"
                  using g_props by auto 
                show "deg (SA m) g \<le> Suc d"
                proof- 
                  have 0: "\<And> x f. f \<in> carrier (UP (SA m)) \<Longrightarrow> x \<in> carrier (SA m) \<Longrightarrow> deg (SA m) (taylor_expansion (SA m) x f) = deg (SA m) f"
                    by (metis UP_cring.taylor_def UP_cring.taylor_deg UP_cring_def padic_fields.SA_is_cring padic_fields_axioms)
                  have 1: "deg (SA m) g = deg (SA m) (poly_unit_replacement m (taylor_expansion (SA m) c f) b)"
                    unfolding g_def a_def
                    by(intro 0 poly_unit_replacement_closed taylor_expansion_closed
                              A prems R.ring_simprules)
                  have 2: "deg (SA m) (taylor_expansion (SA m) c f) = deg (SA m) f"
                    by(intro 0 A prems)
                  show ?thesis 
                    using poly_unit_replacement_deg[of "taylor_expansion (SA m) c f" m b] A
                          taylor_expansion_closed[of f m c] le_trans prems(3)
                    unfolding 1 2 by blast
                qed
                show "\<B> = Cond m b c a1 a2 I"
                  unfolding B_eq by auto 
                show "is_cell_condition \<B>"
                  using C decomp_by_cfs_is_decomp[of a m \<C>] is_cell_decompE(3) "1" "2" a_closed A
                  by blast
                show "\<And>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or> taylor_expansion (SA m) c g i \<in> Units (SA m)"
                  using g_props by auto 
                show "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m g) c (condition_to_set \<B>) N"
                proof- 
                  obtain N where N_def: 
                     "SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<C>) N"
                    by (metis B S_def center.simps f'_def params)
                  have 0: "SA_poly_ubounded p m (UPSA.pderiv m f) c (condition_to_set \<B>) N"
                    by(rule SA_poly_ubounded_mono[of m _ _  "condition_to_set \<C>" ], rule  N_def,
                       intro is_cell_decomp_subset[of m "decomp_by_cfs m a \<C>"]  cell_decomp C)
                  have 1: "SA_poly_ubounded p m (UPSA.pderiv m g) c (condition_to_set \<B>) N"
                    apply(intro SA_poly_uboundedI prems pderiv_closed g_props)
                     apply (meson "0" SA_poly_ubounded_facts'(3))
                  proof- 
                    fix x t i assume D: "t#x \<in> condition_to_set \<B>"
                    have D0: "SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = 
                          SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
                      using D deriv by auto 
                    show " val (SA_poly_to_Qp_poly m x (UPSA.pderiv m g) \<bullet> t)
         \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x (UPSA.pderiv m g)) i \<bullet> t) + eint N"
                      unfolding D0 
                      using D SA_poly_uboundedE'[of m "UPSA.pderiv m f" c "condition_to_set \<B>" N]  0 
                      by auto 
                  qed
                  thus "\<exists>N. SA_poly_ubounded p m (UPSA.pderiv m g) c (condition_to_set \<B>) N"
                    by blast 
                qed
              qed
              show "denef_I_property m g (condition_to_set \<B>)"
                unfolding denef_I_property_def using reduction_decomp by auto 
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
end
