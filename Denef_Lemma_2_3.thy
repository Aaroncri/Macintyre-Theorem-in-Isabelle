theory Denef_Lemma_2_3
imports Constructing_Semialgebraic_Functions
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Denef's Lemma 2.3\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>This theory proves the first of two key lemmas needed to produce new semialgebraic functions 
from old ones via Hensel's Lemma. The exact statement of the lemma in Denef's paper is given below. 
Minor modifications have been made to the statement for consistency with our own notation. 


Assume that cell decomposition theorem $II_d$ holds. Let $t$ be one variable and $x = (x_1, \dots, x_m)$. Let $g(x,t)$ be a polynomial in $t$ of degree $\leq d+1$ with coefficients which are semialgebraic functions of $x$ taking values in $\mathcal{O}_p$. Let $e \in \mathbb{N}$, $\kappa \in \mathcal{O}_p$ be fixed. Suppose that $\xi(x)$ is a function from $\mathbb{Q}_p^m$ to $\mathcal{O}_p$ such that for all $x \in \mathbb{Q}_p^m$:
\begin{enumerate}
\item $g(x, \xi(x)) = 0$
\item $\xi(x) \equiv \kappa \text{ mod } p^{e+1}$
\item $\text{ ord }g'(x, \xi (x)) \leq e$,
\end{enumerate}
where g' denotes the derivative of $g$ with respect to $t$. Then $\xi(x)$ is a semialgebraic function. 


Our proof of this fact occurs within the locale \texttt{denef\_lemma\_2\_3} which is defined below. It extends the \texttt{denef\_II} locale, and it will also be possible to eventually show that it extends the \texttt{SA\_fun\_proof} locale as well. For algebraic simplicity, we have added the assumption that the lead coefficient of the semialgebraic polynomial $g$ is a semialgebraic unit. This guarantees that any time that we evaluate the coefficients of $g$, the result polynomial over $\mathbb{Q}_p$ will have the same degree. This doesn't really lose any generality, since given an arbitrary semialgebraic $g$, we can semialgebraically paritition $\mathbb{Q}_p^m$ according to the zero sets of the coefficients of $g$, cast the nonzero coefficients of $g$ to units on each piece, and apply the theorem separately there to each piece. We can then glue the individual semialgebraic functions $\xi(x)$ obtained by this process together along these pieces to get our global $\xi(x)$ consistent with $g$.
\<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Establishing a Locale for the Proof\<close>
(**************************************************************************************************)
(**************************************************************************************************)
lemma(in padic_fields) val_dist_sym:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  shows "val (a \<ominus> b) = val (b \<ominus> a)"
proof- 
  have 0: "b \<ominus> a = \<ominus>(a \<ominus> b)"
    using assms unfolding a_minus_def 
    by (simp add: Qp.a_ac(2) Qp.minus_sum)
  show ?thesis using assms unfolding 0 
    by (meson Qp.cring_simprules(4) val_minus)
qed

lemma(in padic_fields) val_dist_to_Zp:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "val (a \<ominus> b) = val_Zp (to_Zp b \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp a)"
  using to_Zp_val[of "a \<ominus> b"] assms 
  by (metis to_Zp_minus to_Zp_val val_dist_sym val_ring_memE(2) val_ring_minus_closed)

locale denef_lemma_2_3 = denef_II + 
  fixes g \<xi> e l m
  assumes DL_2_3_1:"deg (SA m) g \<le> Suc d"
  assumes DL_2_3_2:"deg (SA m) g > 0"
  assumes DL_2_3_3:"g \<in> carrier (UP (SA m))"
  assumes DL_2_3_4:"\<And>j. g j \<in> carrier  (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
  assumes DL_2_3_5:"\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p) \<and> \<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
  assumes DL_2_3_6:"UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes DL_2_3_7:"\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  assumes DL_2_3_8:"\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (Suc e) = l"
  assumes DL_2_3_9:"\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x#x)) \<le> e"
  assumes DL_2_3_10: "m > 0"
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Four Important Sublemmas\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>A the bottom of page 159 Denef writes "This will follow from i), ii), iii), and iv) below." 
These facts are proved here as \texttt{fact\_1}, \texttt{fact\_2}, \texttt{fact\_3}, and 
\texttt{fact\_4}.\<close>


context denef_lemma_2_3
begin

lemma \<xi>_closed:
" \<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
  using DL_2_3_5 by auto

text\<open>The proof (specifically the use of Denef's sublemma $i)$) will require us to decompose the 
fibres of a cell so that residues of the coefficients of the polynomial $g$ are constant. For a 
fixed residue degree $\alpha$, we only need to pass to a finite partition of $\mathbb{Q}_p^m$ to 
accomplish this constancy. Each piece in such a partition can be parametrized by a congruence choice 
function \texttt{cf\_congs}$: \{0, \dots, d+1 \} \to \mathbb{Z}/p^\alpha \mathbb{Z}$, which is what 
the below function does.\<close>

definition g_coeff_cong_set where
"g_coeff_cong_set \<alpha> cf_congs = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<forall>k \<le> Suc d. to_Zp (g k x) \<alpha> = cf_congs k}" 

lemma g_coeff_cong_set_is_semialg:
  assumes "cf_congs \<in> {..< Suc (Suc d)} \<rightarrow> carrier  (Zp_res_ring \<alpha>)"
  shows "is_semialgebraic m (g_coeff_cong_set \<alpha> cf_congs)"
proof- 
  have 0: "g_coeff_cong_set \<alpha> cf_congs = (\<Inter> k \<in> {.. Suc d}. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (g k x) \<alpha> = cf_congs k})"
    unfolding g_coeff_cong_set_def 
    apply(intro equalityI subsetI)
    unfolding mem_Collect_eq by(rule InterI, blast, blast)
  show ?thesis 

    unfolding 0 proof(rule finite_intersection_is_semialgebraic', blast, intro conjI subsetI)
    fix S assume A: "S \<in> (\<lambda>k. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (g k x) \<alpha> = cf_congs k}) ` {..Suc d}"
    then obtain k where k_def: "k \<le> Suc d \<and> S = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (g k x) \<alpha> = cf_congs k}"
      by blast 
    have S_eq: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (g k x) \<alpha> = cf_congs k}"
      using k_def by blast 
    have 1: "S =  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). g k x \<in> \<O>\<^sub>p \<and> Qp_res (g k x) \<alpha> = cf_congs k}"
      using DL_2_3_4[of k] unfolding Qp_res_def S_eq  by blast 
    have 2: "k \<in> {..<Suc (Suc d)}"
      using k_def by auto 
    have 3: "is_semialgebraic m S"
      unfolding 1 apply(rule SA_constant_res_set_semialg)
      using  assms 2 apply auto[1]
      by (simp add: DL_2_3_3 UPSA.UP_car_memE(1)) 
    show "S \<in> semialg_sets m"
      using 3 is_semialgebraic_def by auto 
  next 
    show "(\<lambda>k. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (g k x) \<alpha> = cf_congs k}) ` {..Suc d} \<noteq> {}"
      by auto 
  qed
qed

text\<open>This lemma formalizes the specific claim made in sublemma $i)$ that $\xi(x) \text{ mod } p^{\alpha}$
only depends on the coefficients of $g(x,t) \text{ mod }p^{e+\alpha}$.\<close>
lemma xi_cong:
  assumes "cf_congs \<in> {..< Suc (Suc d)} \<rightarrow> carrier  (Zp_res_ring (\<alpha>+e))"
  assumes  "a \<in> carrier Z\<^sub>p"
  shows "g_coeff_cong_set (\<alpha>+e) cf_congs \<subseteq>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}  \<or>
          {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} \<inter> g_coeff_cong_set (\<alpha>+e) cf_congs = {}"
proof(cases "g_coeff_cong_set (\<alpha>+e) cf_congs \<subseteq>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} ")
  case True
  then show ?thesis by blast 
next
  case False
  then obtain x where x_def: "x \<in>  g_coeff_cong_set (\<alpha>+e) cf_congs \<and> x \<notin> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
    by blast 
  have 0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using x_def 
    by (metis (no_types, lifting) g_coeff_cong_set_def mem_Collect_eq)    
  have 2: "\<And>x. x \<in>  g_coeff_cong_set (\<alpha>+e) cf_congs  \<Longrightarrow> x \<notin> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
  proof- fix x' assume A: "x' \<in>  g_coeff_cong_set (\<alpha>+e) cf_congs"
    have x'_closed: "x' \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A  g_coeff_cong_set_def by blast
    have 20: "(SA_poly_to_SA_fun m g) (\<xi> x'#x') = \<zero>"
      using x'_closed DL_2_3_7 by blast
    then have 21: "SA_poly_to_Qp_poly m x' g \<bullet> (\<xi> x') = \<zero>"
      using DL_2_3_5 SA_poly_to_SA_fun_formula[of g m x' "\<xi> x'" ] DL_2_3_10 DL_2_3_3 Qp.function_ring_car_memE x'_closed 
      by blast
    obtain G where G_def: "G = SA_poly_to_Qp_poly m x' g"
      by blast 
    have G_closed: "G \<in> carrier (UP Q\<^sub>p )"
      using SA_poly_to_Qp_poly_closed[of x' m g] DL_2_3_10 DL_2_3_3 G_def x'_closed by blast
    have P0: "G \<bullet> (\<xi> x') = \<zero>"
      using "21" G_def by blast
    have 21: "UPQ.poly_shift_iter 2 (UPQ.taylor (\<xi> x) G) \<bullet> (\<xi> x' \<ominus> \<xi> x) \<in> carrier Q\<^sub>p"
      by (meson "0" DL_2_3_5 G_closed Qp.function_ring_car_memE Qp.minus_closed UPQ.taylor_closed UPQ.shift_closed UPQ.to_fun_closed x'_closed)
    have 22: "\<xi> x \<in> \<O>\<^sub>p"
      using "0" DL_2_3_5 Qp.function_ring_car_memE by blast
    have 23: " \<xi> x' \<in> \<O>\<^sub>p "
      using DL_2_3_5 Qp.function_ring_car_memE x'_closed by blast
    have 24: "\<And>x j. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m x g j \<in> \<O>\<^sub>p"
    proof- fix x j assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      then have "SA_poly_to_Qp_poly m x g j = g j x"
        using DL_2_3_10 DL_2_3_3 SA_poly_to_Qp_poly_coeff by blast
      then show "SA_poly_to_Qp_poly m x g j \<in> \<O>\<^sub>p" using DL_2_3_4[of j] A  
        by (metis PiE)
    qed 
    then have 25: "(\<And>n. G n \<in> \<O>\<^sub>p)"
      using G_def x'_closed  by blast
    obtain c where c_def: "c \<in> \<O>\<^sub>p \<and>  G \<bullet> \<xi> x = G \<bullet> \<xi> x' \<oplus> UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) \<oplus> c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)"
      using Taylor_deg_1_expansion''[of G "\<xi> x'" "\<xi> x"] G_closed 22 23 24 25 G_def x'_closed by blast
    have 26: "val ((\<xi> x) \<ominus> (\<xi> x')) \<ge> \<alpha>"
    proof(cases "\<xi> x = \<xi> x'")
      case True
      then show ?thesis 
        by (metis "22" Qp.r_right_minus_eq val_ring_memE eint_ord_code(3) local.val_zero)     
    next
      case False
      then have Nz: "(\<xi> x) \<ominus> (\<xi> x') \<in> nonzero Q\<^sub>p"
        by (meson "22" "23" Qp.not_eq_diff_nonzero val_ring_memE)
      have 260: "G \<bullet> \<xi> x = \<zero> \<oplus> UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) \<oplus> c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)"
        using c_def P0 by presburger
      have 261: "G \<bullet> \<xi> x = UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) \<oplus> c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)"
        by (metis "0" "260" DL_2_3_5 G_closed Qp.add.r_cancel_one' Qp.function_ring_car_memE 
            Qp.m_closed Qp.minus_closed Qp.zero_closed UPQ.deriv_closed x'_closed)
      have 262: "UPQ.deriv G (\<xi> x') \<in> \<O>\<^sub>p"
        using Taylor_deg_1_expansion''[of G "\<xi> x'" "\<xi> x"] G_closed 22 23 24 25 G_def x'_closed by blast
      have 261: "val (\<xi> x \<ominus> \<xi> x') \<ge> e+1"
      proof-
        have 2611: "to_Zp (\<xi> x) (Suc e) = l"  
          using "0" DL_2_3_8 by blast
        have 2612: "to_Zp (\<xi> x') (Suc e) = l"  
          using DL_2_3_8 x'_closed by blast
        have 2613: "to_Zp (\<xi> x \<ominus> \<xi> x') = to_Zp (\<xi> x) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (\<xi>  x')"
          using "22" "23" to_Zp_minus by blast
        have 2614: "to_Zp (\<xi> x \<ominus> \<xi> x') (Suc e) = to_Zp (\<xi> x) (Suc e) \<ominus>\<^bsub>Zp_res_ring (Suc e)\<^esub> to_Zp (\<xi>  x') (Suc e)"
          by (metis (no_types, lifting) "2613" DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE Zp_def 
              padic_fields.prime padic_fields.to_Zp_closed padic_fields_axioms padic_integers.residue_of_diff padic_integers_def x'_closed)
        hence  "to_Zp (\<xi> x \<ominus> \<xi> x') (Suc e) = l \<ominus>\<^bsub>Zp_res_ring (Suc e)\<^esub> l"
          using "2611" "2612" by presburger
        hence  "to_Zp (\<xi> x \<ominus> \<xi> x') (Suc e) = 0"
          by (metis "0" "2611" DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE Zp_def padic_fields.prime padic_fields.to_Zp_closed padic_fields_axioms padic_integers.res_diff_zero_fact' padic_integers_def)
        then have "val_Zp (to_Zp (\<xi> x \<ominus> \<xi> x')) \<ge> Suc e"
          by (metis "0" "22" "23" "2611" "2612" "2613" DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE Qp.r_right_minus_eq Zp_def eint_ord_code(3) padic_fields.Qp_val_ringI padic_fields.prime padic_fields.to_Zp_closed padic_fields.to_Zp_inc padic_fields.to_Zp_zero padic_fields_axioms padic_integers.Zp_residue_eq2 padic_integers.val_Zp_def padic_integers_def to_Zp_val val_pos x'_closed)
        then show ?thesis 
          using to_Zp_val 22 23 
          by (metis "2611" "2612" Suc_eq_plus1 equal_res_imp_val_diff_bound)                    
      qed
      have 262: "val (UPQ.deriv G (\<xi> x')) \<le> e"
      proof-
        have 2620: "SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x'#x') = (UPQ.pderiv G) \<bullet> (\<xi> x')"
          unfolding G_def 
          by (metis DL_2_3_10 DL_2_3_3 DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE SA_poly_to_SA_fun_formula UP_cring.pderiv_closed Zp_def padic_fields.SA_is_UP_cring padic_fields.SA_poly_to_Qp_poly_comm_pderiv padic_fields_axioms x'_closed)
        hence 2621:  "val ((UPQ.pderiv G) \<bullet> (\<xi> x')) \<le> e"
          using val_ord  DL_2_3_9 by (metis x'_closed)
        then  show ?thesis  
          by (metis DL_2_3_5 G_closed Qp.function_ring_car_memE UPQ.pderiv_eval_deriv x'_closed)
      qed
      have 263: "val (c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)) > val (UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x')))"
      proof-
        have AA: "val (c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)) =  val c + val (((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat))"
          using c_def val_mult 
          by (meson "22" "23" Qp.minus_closed Qp.nat_pow_closed val_ring_memE)
        hence 2630:"val (c \<otimes> ((\<xi> x) \<ominus> (\<xi> x')) [^] (2::nat)) =  val c + 2*val ((\<xi> x) \<ominus> (\<xi> x'))"
          using Nz by (metis of_nat_numeral val_of_power)
        have  2631:  "2*val ((\<xi> x) \<ominus> (\<xi> x'))  > val (UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x')))"
        proof-
          have 26310: "val (\<xi> x \<ominus> \<xi> x') > val (UPQ.deriv G (\<xi> x'))"
            using 261 262  dual_order.trans eint_ord_simps(1) of_nat_1 of_nat_add 
            by (smt Nz eint_ile eint_ord_simps(2) val_ord)            
          hence 26311: "val (\<xi> x \<ominus> \<xi> x') + val (\<xi> x \<ominus> \<xi> x') > val (UPQ.deriv G (\<xi> x')) + val (\<xi> x \<ominus> \<xi> x')"
            using add_right_mono 
            by (metis "22" DL_2_3_5 False Nz Qp.function_ring_car_memE Qp.nonzero_closed 
                Qp.r_right_minus_eq val_ring_memE add.commute eint_add_left_cancel less_le 
                local.val_zero plus_eint_simps(3) val_ineq x'_closed)           
          have 26312: "val (UPQ.deriv G (\<xi> x') \<otimes> (\<xi> x \<ominus> \<xi> x')) = val (UPQ.deriv G (\<xi> x')) + val (\<xi> x \<ominus> \<xi> x')"
            using val_mult 
            by (meson "23" G_closed Nz Qp.nonzero_closed val_ring_memE UPQ.deriv_closed)
          then show ?thesis using two_times_eint  26311 Nz val_mult[of  "UPQ.deriv G (\<xi> x')" "(\<xi> x) \<ominus> (\<xi> x')"]  
            by presburger
        qed
        have 2632: "val c + 2*val ((\<xi> x) \<ominus> (\<xi> x')) \<ge>2*val ((\<xi> x) \<ominus> (\<xi> x'))"
          by (metis "2630" Nz Qp.nat_pow_closed Qp.nonzero_closed c_def of_nat_numeral val_of_power val_val_ring_prod)
        then show ?thesis using AA 2630 2631 
          by (smt less_le_trans)
      qed
      then have 264: "val (UPQ.deriv G (\<xi> x') \<otimes> ((\<xi> x) \<ominus> (\<xi> x'))) =  val (G \<bullet> \<xi> x)"
        using 261 DL_2_3_5 G_closed Nz P0 Qp.add.m_comm Qp.function_ring_car_memE
            Qp.l_zero Qp.m_closed Qp.nonzero_closed val_ring_memE UPQ.deriv_closed c_def 
            val_ultrametric_noteq x'_closed
        by (metis (no_types, lifting) "23" UPQ.monom_term_car)
      have 265: "val (G \<bullet> \<xi> x) \<ge> e + \<alpha>"
      proof-
        have 2640: "(SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
          using "0" DL_2_3_7 by blast
        then have 2641: "SA_poly_to_Qp_poly m x g \<bullet> (\<xi> x) = \<zero>"
          using DL_2_3_5 SA_poly_to_SA_fun_formula[of g m x "\<xi> x" ] DL_2_3_10 DL_2_3_3 Qp.function_ring_car_memE 
            "0" by blast
        obtain G' where G'_def: "G' = SA_poly_to_Qp_poly m x g"
          by blast 
        have G'_closed: "G' \<in> carrier (UP Q\<^sub>p )"
          using SA_poly_to_Qp_poly_closed[of x m g] DL_2_3_10 DL_2_3_3 G'_def 0  by blast              
        have 2641: "G' \<bullet> (\<xi> x) = \<zero>"
          using G'_def 0 2641 by blast
        have 2642: "\<And>j. val (G j \<ominus> G' j) \<ge> e + \<alpha>"
        proof- fix j
              have 26420: "\<forall>k \<le> Suc d. to_Zp (g k x) (\<alpha>+e) = cf_congs k"
                using x_def g_coeff_cong_set_def by blast
              have 26421: "\<forall>k \<le> Suc d. to_Zp (g k x') (\<alpha>+e) = cf_congs k"
                using A unfolding g_coeff_cong_set_def by blast 
              have 26422: "\<And>k. to_Zp (g k x) (\<alpha>+e) = to_Zp (g k x') (\<alpha>+e)"
              proof- fix k show "to_Zp (g k x) (\<alpha> + e) = to_Zp (g k x') (\<alpha> + e)"
                  apply(cases "k \<le>Suc d")
                  using "26420" "26421" apply presburger
                  proof- assume "\<not> k \<le> Suc d" then have "Suc d < k"
                    using not_less by blast
                  then have "g k = \<zero>\<^bsub>SA m\<^esub>"
                  using DL_2_3_1 UP_cring.UP_car_memE(2)[of "SA m" g k] 
                  by (meson DL_2_3_10 DL_2_3_3 SA_is_UP_cring dual_order.trans not_less)
                   then show ?thesis 
                   by (metis "0" function_zero_eval Q\<^sub>p_def Zp_def padic_fields.SA_zero padic_fields_axioms x'_closed)             
               qed
              qed
              hence 26423: "\<And>k. to_Zp ((g k x) \<ominus> (g k x')) (\<alpha>+e) = 0"
                by (smt "0" PiE Q\<^sub>p_def Zp_def denef_lemma_2_3.DL_2_3_4 denef_lemma_2_3_axioms
                    padic_fields.val_ring_memE padic_fields.prime padic_fields.to_Zp_minus
                    padic_fields_axioms padic_integers.res_diff_zero_fact' residue_of_diff 
                    padic_integers_def to_Zp_closed x'_closed)
              have 26424: "\<And>k. val_Zp (to_Zp ((g k x) \<ominus> (g k x'))) \<ge> \<alpha> + e"
              proof- fix k have "(to_Zp ((g k x) \<ominus> (g k x'))) \<in> carrier Z\<^sub>p"
                  by (metis (no_types, lifting) Zp.zero_closed Zp_def padic_fields.val_ring_memE  
                      padic_fields.to_Zp_closed padic_fields.to_Zp_def padic_fields_axioms)
                then show "eint (int (\<alpha> + e)) \<le> val_Zp (to_Zp (g k x \<ominus> g k x'))"
                  using 26423 by (metis Q\<^sub>p_def Zp_def eint_ord_code(3) eint_ord_simps(2) 
                      linorder_not_less local.val_zero padic_fields.prime padic_fields.to_Zp_val 
                      padic_fields.to_Zp_zero padic_fields.zero_in_val_ring padic_fields_axioms 
                      padic_integers.ord_Zp_geq padic_integers_def val_ord_Zp)
              qed
              have 26425: "\<And>k. val ((g k x) \<ominus> (g k x')) \<ge> \<alpha> + e"
              proof- fix k have " ((g k x) \<ominus> (g k x')) \<in> \<O>\<^sub>p"
                  using DL_2_3_4[of k] 0 x'_closed 
                  by (meson PiE val_ring_minus_closed)                                                  
                then show "eint (int (\<alpha> + e)) \<le> val (g k x \<ominus> g k x')"
                  using 26424  by (metis to_Zp_val)
              qed
              then show "val (G j \<ominus> G' j) \<ge> e + \<alpha>"
                unfolding G_def G'_def 
                by (metis "0" "24" DL_2_3_3 SA_poly_to_Qp_poly_coeff add.commute val_dist_sym val_ring_memE(2) x'_closed)
        qed
        hence 2643: "\<And>j. val ((G \<ominus>\<^bsub>UP Q\<^sub>p\<^esub>G') j) \<ge> e + \<alpha>"
          using G'_closed G_closed UPQ.cfs_minus by presburger
        then have "gauss_norm (G \<ominus>\<^bsub>UP Q\<^sub>p \<^esub> G') \<ge> e + \<alpha>"
          using  gauss_norm_coeff_norm[of "G \<ominus>\<^bsub>UP Q\<^sub>p\<^esub>G'"] 
          by metis
        then have 2644:"val ((G \<ominus>\<^bsub>UP Q\<^sub>p \<^esub> G') \<bullet> (\<xi> x)) \<ge> e + \<alpha>"
          using val_gauss_norm_eval 
          by (meson "22" G'_closed G_closed UPQ.P.minus_closed less_le_trans linorder_not_less)
        have 2645: "(G \<ominus>\<^bsub>UP Q\<^sub>p \<^esub> G') \<bullet> (\<xi> x) = G \<bullet>(\<xi> x)"
        proof-
          have "(G \<ominus>\<^bsub>UP Q\<^sub>p \<^esub> G') \<bullet> (\<xi> x) = (G \<bullet> (\<xi> x)) \<ominus>  (G' \<bullet> (\<xi> x))"
            using UPQ.to_fun_diff[of G G' "\<xi> x"] 22 G'_closed G_closed val_ring_memE by blast 
          hence "(G \<ominus>\<^bsub>UP Q\<^sub>p \<^esub> G') \<bullet> (\<xi> x) = (G \<bullet> (\<xi> x)) \<ominus>  \<zero>"
            using 2641  by presburger
          then show ?thesis 
            unfolding a_minus_def 
            using "22" G_closed Qp.minus_zero Qp.r_zero val_ring_memE UPQ.to_fun_closed 
            by (simp add: \<open>G \<in> carrier (UP Q\<^sub>p)\<close> \<open>\<And>a. a \<in> \<O>\<^sub>p \<Longrightarrow> a \<in> carrier Q\<^sub>p\<close> \<open>\<And>a. a \<in> carrier Q\<^sub>p \<Longrightarrow> a \<ominus> \<zero> = a\<close> \<open>\<And>x f. \<lbrakk>f \<in> carrier (UP Q\<^sub>p); x \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> f \<bullet> x \<in> carrier Q\<^sub>p\<close> \<open>\<xi> x \<in> \<O>\<^sub>p\<close> val_ring_memE(1) Qp.cring_simprules(15))
        qed
        show ?thesis using 2644 2645  by metis 
      qed
      hence 266: "val (UPQ.deriv G (\<xi> x')) + val ((\<xi> x) \<ominus> (\<xi> x')) \<ge> e + \<alpha>"
        using  264 265 
        by (metis DL_2_3_5 G_closed Nz Qp.function_ring_car_memE Qp.nonzero_closed UPQ.deriv_closed val_mult x'_closed) 
      hence 266: "val (UPQ.deriv G (\<xi> x')) + val ((\<xi> x) \<ominus> (\<xi> x')) \<ge> (eint (int e)) + \<alpha>"
        by (metis of_nat_add plus_eint_simps(1))
      hence 267: "e + val ((\<xi> x) \<ominus> (\<xi> x')) \<ge> (eint (int e)) + \<alpha>"
        using 262 add_right_mono dual_order.trans by blast
      then show ?thesis using add_cancel_eint_geq  
        by blast
    qed
    have 27: "(\<xi> x) \<ominus> (\<xi> x') \<in> \<O>\<^sub>p"
      by (simp add: "22" "23" val_ring_minus_closed)
    hence 28: "val_Zp (to_Zp ((\<xi> x) \<ominus> (\<xi> x'))) \<ge> \<alpha>"
      using "26" to_Zp_val by presburger
    have "to_Zp ((\<xi> x) \<ominus> (\<xi> x')) = (to_Zp (\<xi> x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp (\<xi> x'))"
      using "22" "23" to_Zp_minus by blast
    hence 29: "val_Zp ((to_Zp (\<xi> x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp (\<xi> x'))) \<ge> \<alpha>"
      using "28" by presburger
    hence "(to_Zp (\<xi> x)) \<alpha> = (to_Zp (\<xi> x')) \<alpha>"
      using "22" "23" val_ring_memE Zp.minus_closed res_diff_zero_fact(1) to_Zp_closed zero_below_val_Zp by presburger
    then show "x' \<notin> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
      by (metis (no_types, lifting) "0" mem_Collect_eq x_def)
  qed
  then have "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} \<inter> g_coeff_cong_set (\<alpha> + e) cf_congs = {}"
    by blast
  thus ?thesis by blast 
qed

lemma fact_1:
  assumes "(\<alpha>::nat) > 0"
  assumes "a \<in> carrier Z\<^sub>p"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
proof-
  obtain S where S_def: "S = g_coeff_cong_set (\<alpha>+e) ` ( {..< Suc (Suc d)} \<rightarrow>\<^sub>E carrier  (Zp_res_ring (\<alpha>+e)))"
    by blast 
  have finite_S: "finite S"
  proof-
    have 0: "finite {..<Suc (Suc d)}"
      by simp
    have 1: "finite (carrier (residue_ring (p ^ (\<alpha>+e))))"
      using residue_ring_card by blast
    thus ?thesis  
      using finite_extensional_funcset[of "{..< Suc (Suc d)}" "carrier  (Zp_res_ring (\<alpha>+e))"]  0 1 
      unfolding S_def by blast 
  qed      
  obtain S' where S'_def: "S' = {s \<in> S. s \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}}"
    by blast 
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} = \<Union> S'"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} \<subseteq> \<Union> S'"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A by blast
      obtain g_cf where g_cf_def: "g_cf = restrict (\<lambda>k. to_Zp (g k x) (\<alpha>+e)) {..< Suc (Suc d)}"
        by blast 
      have 1: "g_coeff_cong_set (\<alpha>+e) g_cf \<in> S'"
      proof-
        have 00: "g_cf \<in> {..< Suc (Suc d)} \<rightarrow> carrier  (Zp_res_ring (\<alpha>+e))"
          using x_closed unfolding g_cf_def  
          by (smt Zp.zero_closed Zp_def padic_fields.val_ring_memE padic_fields.prime
              padic_fields.to_Zp_closed padic_fields.to_Zp_def padic_fields_axioms padic_integers.residue_closed padic_integers_def restrictI)
        have 01: "\<forall> k \<in>{..< Suc (Suc d)}. g_cf k = to_Zp (g k x) (\<alpha>+e)"
          unfolding g_cf_def by (meson restrict_apply')
        hence 02: "x \<in> g_coeff_cong_set (\<alpha>+e) g_cf"
          unfolding g_coeff_cong_set_def using x_closed 
        proof -
          have "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (\<forall>n. \<not> n \<le> Suc d \<or> to_Zp (g n x) (\<alpha> + e) = g_cf n)"
            by (metis (no_types) "01" lessThan_iff less_Suc_eq_le x_closed)
          then show "x \<in> {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<forall>n\<le>Suc d. to_Zp (g n rs) (\<alpha> + e) = g_cf n}"
            by blast
        qed
        have 03: "g_cf \<in> ({..<Suc (Suc d)} \<rightarrow>\<^sub>E carrier (residue_ring (p ^ (\<alpha> + e))))"
          using g_cf_def  by (metis (mono_tags, lifting) "00" restrict_PiE restrict_apply' restrict_ext)
        hence 04: "g_coeff_cong_set (\<alpha>+e) g_cf \<in> S"
          unfolding S_def by blast
        have 05: "g_coeff_cong_set (\<alpha>+e) g_cf \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} \<noteq> {}"
          using  A 02 by blast 
        then have "g_coeff_cong_set (\<alpha>+e) g_cf \<subseteq>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>} "
          using xi_cong[of g_cf \<alpha> a] assms 03 00  by blast
        then show ?thesis  using S'_def 04 by blast 
      qed
      have 2: "g_cf \<in> {..< Suc (Suc d)} \<rightarrow> carrier  (Zp_res_ring (\<alpha>+e))"
        using x_closed unfolding g_cf_def  
        by (smt Zp.zero_closed Zp_def padic_fields.val_ring_memE padic_fields.prime
              padic_fields.to_Zp_closed padic_fields.to_Zp_def padic_fields_axioms padic_integers.residue_closed padic_integers_def restrictI)
      have 3: "\<forall> k \<in>{..< Suc (Suc d)}. g_cf k = to_Zp (g k x) (\<alpha>+e)"
        unfolding g_cf_def by (meson restrict_apply')
      hence 4: "x \<in> g_coeff_cong_set (\<alpha>+e) g_cf"
        unfolding g_coeff_cong_set_def using x_closed 
      proof -
          have "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> (\<forall>n. \<not> n \<le> Suc d \<or> to_Zp (g n x) (\<alpha> + e) = g_cf n)"
            by (metis (no_types) 3 lessThan_iff less_Suc_eq_le x_closed)
          then show "x \<in> {rs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<forall>n\<le>Suc d. to_Zp (g n rs) (\<alpha> + e) = g_cf n}"
            by blast
      qed
      then show "x \<in> \<Union> S'"
        using 1 by blast
    qed
    show "\<Union> S' \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) \<alpha> = a \<alpha>}"
      unfolding S'_def  by blast
  qed
  have 1: "are_semialgebraic m S'"
  proof(rule are_semialgebraicI)
    fix x assume A: "x \<in> S'"
    then obtain g_cf where g_cf_def: "x =  g_coeff_cong_set (\<alpha>+e) g_cf \<and> g_cf \<in>  {..< Suc (Suc d)} \<rightarrow>\<^sub>E carrier  (Zp_res_ring (\<alpha>+e))"
      unfolding S'_def S_def by blast 
    then show  " is_semialgebraic m x"
      using g_coeff_cong_set_is_semialg[of "g_cf" "\<alpha> + e"] 
      by blast 
  qed
  have "finite S'"
    unfolding S'_def using finite_S 
    by (metis (no_types, lifting) S'_def mem_Collect_eq rev_finite_subset subsetI)
  then show ?thesis using 0 1 
    by (metis (no_types, lifting) are_semialgebraicE finite_union_is_semialgebraic is_semialgebraicE subsetI)
qed

lemma fact_2: 
  fixes N::nat 
  fixes n::nat
  fixes a
  assumes "N > 0"
  assumes "n > 0"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "a \<in> \<O>\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val c \<le> - N"
  shows   "val (a \<ominus> c) = val (\<ominus> c)"
          "pow_res n (a \<ominus> c) = pow_res n (\<ominus> c)"
proof-
  have c_nonzero: "c \<in> nonzero Q\<^sub>p"
    using assms by (meson eint_ile val_nonzero')
  have 0: "a \<ominus> c = (\<ominus> c)\<otimes>(\<one> \<ominus> (a \<otimes>(inv c)))"
    using c_nonzero assms  
    by (metis (no_types, lifting) Qp.l_minus Qp.minus_a_inv Qp.minus_closed Qp.one_closed 
        Qp.r_minus_distr Qp.r_one val_ring_memE fract_closed local.fract_cancel_right)
  have 1: "val (a \<ominus> c) = val c + val (\<one> \<ominus> (a \<otimes>(inv c)))"
    using 0 assms val_mult Qp.add.inv_closed Qp.minus_closed Qp.one_closed val_ring_memE c_nonzero fract_closed val_minus by presburger
  have "ord (inv c) = - ord c"
    using assms c_nonzero Qp.nonzero_memE(2) ord_of_inv by blast
  hence P: "ord (inv c)  \<ge> N"
    using assms 
    by (metis add.inverse_inverse c_nonzero eint_ord_simps(1) neg_le_iff_le val_ord)
  have invc_nonzero:"inv c \<in> nonzero Q\<^sub>p"
    using c_nonzero nonzero_inverse_Qp by blast
  have P': "val (inv c) \<ge> N"
    using  invc_nonzero val_ord[of "inv c"] c_nonzero Qp.not_nonzero_memI Qp.zero_closed assms(1) assms(5) 
      local.val_zero val_nonzero' val_of_inv val_p_int_pow val_p_int_pow_neg
      P eint_ord_simps(1) by presburger
  hence 2: "val (a \<otimes>(inv c)) \<ge>  N"
    using assms val_mult[of a "inv c"] 
    by (metis (no_types, lifting) Qp.nonzero_memE(2) c_nonzero dual_order.trans inv_in_frac(1) val_val_ring_prod)
  have quot_closed: "(a \<div> c) \<in> carrier Q\<^sub>p"
    using assms invc_nonzero val_ring_memE c_nonzero fract_closed by blast
  have 30: "val \<one> = val (\<one> \<ominus> (a \<div> c))"    
    proof-
      have "val \<one> < val (a \<div> c)"
        using val_one P' 
        by (metis "2" assms(1) eint_pow_int_is_pos less_le_trans of_nat_0_less_iff)
      then show ?thesis 
        using quot_closed val_ultrametric_noteq''[of  "a \<div> c" \<one>] Qp.one_closed by presburger
  qed
  have "ac N (\<one> \<ominus> a \<otimes>(inv c)) = ac N \<one>"
  proof-
    have 31: "\<one> \<ominus> (a \<div> c) \<in> nonzero Q\<^sub>p"
      using 30 
      by (metis Qp.minus_closed Qp.one_closed quot_closed val_nonzero' val_one zero_eint_def)
    have "\<one> \<ominus> (\<one> \<ominus> (a \<div> c)) = (a \<div> c)"
      unfolding a_minus_def 
      by (metis Qp.add.inv_closed Qp.minus_minus Qp.minus_sum Qp.one_closed Qp.r_neg1 quot_closed)    
    hence 32: "val \<one> + eint (int N) \<le> val (\<one> \<ominus> (\<one> \<ominus> (a \<div> c)))"
      using val_one 2 31 quot_closed  
      by (metis add.left_neutral) 
    thus ?thesis 
      using 30 31 32 ac_val[of \<one> "\<one> \<ominus> a \<otimes>(inv c)" N] Qp.one_nonzero by linarith
  qed 
  then have "(\<one> \<ominus> a \<otimes>(inv c)) \<in> P_set n"
    using assms 30 ac_one val_one 
    by (metis Qp.minus_closed Qp.one_closed le_eq_less_or_eq less_one nat_le_linear not_gr_zero quot_closed)
  then show "pow_res n (a \<ominus> c) = pow_res n (\<ominus> c)" using 0 equal_pow_resI' 
    by (metis Qp.add.inv_closed Qp.m_closed Qp.minus_closed Qp.one_closed assms(2) assms(3) quot_closed)
  show "val (a \<ominus> c) = val (\<ominus> c)"
    by (metis "1" "30" add.right_neutral assms(3) val_minus val_one)
qed

lemma equal_res_ptimes_imp_equal_res:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "a k = b k"
  shows "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub>a) (k + n) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub> b) (k + n)"
proof-
  have "val_Zp (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b) \<ge> k"
    using assms  val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
  hence "val_Zp (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub> (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b)) \<ge> k + eint n"
    using val_Zp_mult[of "\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)" "(a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b)"] assms 
    by (metis Zp.minus_closed add.commute add_mono_thms_linordered_semiring(1) order_refl p_pow_nonzero(1) val_Zp_p_pow)
  hence "val_Zp (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub> (a \<ominus>\<^bsub>Z\<^sub>p\<^esub> b)) \<ge> k + n"
    by (metis of_nat_add plus_eint_simps(1))
  hence "val_Zp ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub>a) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)\<otimes>\<^bsub>Z\<^sub>p\<^esub>b)) \<ge> k + n"
    using assms Zp.r_minus_distr p_pow_nonzero(1) 
    by presburger
  then show ?thesis 
    using Zp.m_closed Zp.minus_closed assms(1) assms(2) p_pow_nonzero(1) res_diff_zero_fact(1) zero_below_val_Zp 
    by presburger
qed

lemma fact_3: 
  fixes N::nat 
  fixes n::nat
  fixes a 
  fixes a'
  fixes c
  fixes c'
  assumes "\<exists>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<xi> x = a"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "val c > -N"
  assumes "val (a \<ominus> c) < e + N"
  assumes "\<exists>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). \<xi> x = a'"
  assumes "c' \<in> carrier Q\<^sub>p"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "val c' > -N"
  assumes "val (a' \<ominus> c') < e + N"
  assumes "to_Zp a (e+2*N) = to_Zp a' (e+2*N) "
  assumes "to_Zp (\<pp>[^]N \<otimes> c) (e+3*N) = to_Zp (\<pp>[^]N \<otimes> c') (e+3*N)"
  assumes "N > 0"
  assumes "n > 0"
  shows "val (a \<ominus> c) = val (a' \<ominus> c')"
        "pow_res n (a \<ominus> c) = pow_res n (a' \<ominus> c')"
proof-
  obtain v where v_def: "v = \<pp>[^](N::nat) \<otimes> a \<ominus> \<pp>[^](N::nat) \<otimes> c"
    by blast 
  obtain v' where v'_def: "v' = \<pp>[^](N::nat) \<otimes> a' \<ominus> \<pp>[^](N::nat) \<otimes> c'"
    by blast 
  have v_closed: "v \<in> carrier Q\<^sub>p"
    using v_def assms DL_2_3_5 Qp.function_ring_car_memE by blast
  have v'_closed: "v' \<in> carrier Q\<^sub>p"
    using v'_def assms DL_2_3_5 Qp.function_ring_car_memE by blast
  have a_closed: "a \<in> \<O>\<^sub>p"
    using DL_2_3_5 assms by blast
  have a'_closed: "a' \<in> \<O>\<^sub>p"
    using DL_2_3_5 assms(6) by blast
  have val_a: "val a \<ge> 0"
    using a_closed val_ring_memE by blast
  have val_a': "val a' \<ge> 0"
    using a'_closed val_ring_memE by blast
  have val_c: "val (\<pp>[^]N \<otimes> c) \<ge> 0"
  proof- 
    have "val (\<pp>[^]N \<otimes> c) = N + val c"
      using val_mult assms ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) val_ord by presburger
    have "N + val c > N + eint (-N)"
      using assms(4) eint_add_left_cancel_less by blast
    hence "N + val c > N + (-N)"
      by (metis plus_eint_simps(1))
    then show ?thesis 
      by (metis (mono_tags, opaque_lifting) \<open>val (\<pp> [^] N \<otimes> c) = eint (int N) + val c\<close> add.commute 
        add.left_neutral add.right_inverse add_right_mono add_strict_mono eint_ord_simps(1)
        gr_implies_not_zero linorder_not_less of_nat_0_less_iff of_nat_eq_0_iff zero_eint_def)
  qed
  have val_c': "val (\<pp>[^]N \<otimes> c') \<ge> 0"
  proof- 
    have "val (\<pp>[^]N \<otimes> c') = N + val c'"
      using val_mult assms ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) val_ord by presburger
    have "N + val c' > N + eint (-N)"
      using assms eint_add_left_cancel_less by blast
    hence "N + val c' > N + (-N)"
      by (metis plus_eint_simps(1))
    then show ?thesis 
      by (metis (mono_tags, opaque_lifting) \<open>val (\<pp> [^] N \<otimes> c') = eint (int N) + val c'\<close> add.commute 
        add.left_neutral add.right_inverse add_right_mono add_strict_mono eint_ord_simps(1)
        gr_implies_not_zero linorder_not_less of_nat_0_less_iff of_nat_eq_0_iff zero_eint_def)
  qed
  have pnc_closed: "(\<pp>[^]N \<otimes> c) \<in> \<O>\<^sub>p"
    using val_ring_val_criterion assms(2) p_natpow_closed(1) val_c by blast
  have pnc'_closed: "(\<pp>[^]N \<otimes> c') \<in> \<O>\<^sub>p"
    by (meson Qp.int_inc_closed Qp.m_closed Qp.nat_pow_closed val_ring_val_criterion assms(7) val_c')
  have pna_closed: "(\<pp>[^]N \<otimes> a) \<in> \<O>\<^sub>p"
    using val_ring_val_criterion a_closed p_natpow_closed(1) val_a 
    by (smt Qp.m_closed val_ring_memE Zp.one_closed Zp_int_mult_closed dual_order.trans image_eqI p_inc val_ring_nat_pow_closed val_val_ring_prod)
  have pna'_closed: "(\<pp>[^]N \<otimes> a') \<in> \<O>\<^sub>p"
    using val_ring_val_criterion a_closed p_natpow_closed(1) val_a 
    by (smt Qp.int_inc_closed Qp.m_closed val_ring_memE Zp.one_closed Zp_int_mult_closed a'_closed dual_order.trans val_Zp_p val_a' val_p val_pos val_ring_nat_pow_closed val_val_ring_prod)
  have v_closed: "v \<in> \<O>\<^sub>p"
    using val_ring_val_criterion v_closed v_def pna_closed pnc_closed val_ring_minus_closed
    by presburger
  have v'_closed: "v' \<in> \<O>\<^sub>p"
    using val_ring_val_criterion  v'_closed  v'_def  val_ring_minus_closed
    using pna'_closed pnc'_closed by presburger
  have "val v \<ge> 0"
    using val_c v_def assms val_ring_memE v_closed by blast
  have "val v' \<ge> 0"
    using val_c' v'_def assms v'_closed  val_ring_memE by blast
  have v_factor: "v = \<pp>[^]N \<otimes> (a \<ominus> c)"
    using v_def assms by (metis DL_2_3_5 Qp.function_ring_car_memE Qp.r_minus_distr p_natpow_closed(1))
  have v'_factor: "v' = \<pp>[^]N \<otimes> (a' \<ominus> c')"
  using Qp.r_minus_distr val_ring_memE a'_closed assms(7) p_natpow_closed(1) v'_def by presburger
  have v_val: "val v = N + val (a \<ominus> c)"
    using val_mult assms 
    by (metis DL_2_3_5 Qp.function_ring_car_memE Qp.minus_closed ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) v_factor val_ord)
  have v'_val: "val v' = N + val (a' \<ominus> c')"
    using val_mult assms Qp.minus_closed val_ring_memE a'_closed ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) v'_factor val_ord 
    by presburger
  have 0: "val v' < e + 2*N"
  proof-
    have "N + val (a' \<ominus> c') < N + eint (e + N)"
      using assms by (meson add_cancel_eint_geq linorder_not_less)
    hence "N + val (a' \<ominus> c') < N + e + N"
      by (metis of_nat_add plus_eint_simps(1) zadd_int_left)
    hence  "N + val (a' \<ominus> c') < 2*N + e"
      by (metis add.commute left_add_twice)
    then show ?thesis using v'_factor  by (metis add.commute v'_val)
  qed
  have 1: "val v < e + 2*N"
  proof-
    have "N + val (a \<ominus> c) < N + eint (e + N)"
      using assms by (meson add_cancel_eint_geq linorder_not_less)
    hence "N + val (a \<ominus> c) < N + e + N"
      by (metis of_nat_add plus_eint_simps(1) zadd_int_left)
    hence  "N + val (a \<ominus> c) < 2*N + e"
      by (metis add.commute left_add_twice)
    then show ?thesis using v_factor  by (metis add.commute v_val)
  qed
  have 2: "to_Zp v (e+2*N) = to_Zp v' (e+2*N)"
  proof-
    have 20: "to_Zp (\<pp>[^]N \<otimes> c) \<in> carrier Z\<^sub>p"
      using val_ring_memE pnc_closed to_Zp_closed by blast
    have 21: "to_Zp (\<pp>[^]N \<otimes> c') \<in> carrier Z\<^sub>p"
      using val_ring_memE pnc'_closed to_Zp_closed by blast
    have 22: "e+2*N \<le> e+3*N"
      using assms by linarith
    have 23: "to_Zp (\<pp>[^]N \<otimes> c) (e+2*N) = to_Zp (\<pp>[^]N \<otimes> c') (e+2*N)"
      using p_residue_padic_int assms 20 21 22  by metis
    have "\<And>x y n. x \<in> carrier Z\<^sub>p \<Longrightarrow> y \<in> carrier Z\<^sub>p \<Longrightarrow> (x \<otimes>\<^bsub>Z\<^sub>p\<^esub> y) n = x n \<otimes>\<^bsub>Zp_res_ring n\<^esub> y n"
      using residue_of_prod by blast
    hence 24: "to_Zp (\<pp> [^] N \<otimes> a) (e+2*N)  = to_Zp (\<pp> [^] N \<otimes> a') (e+2*N) "
      using assms(11) a_closed a'_closed to_Zp_mult[of "\<pp> [^] N " a ] to_Zp_mult[of "\<pp> [^] N " a' ] 
      by (metis Qp.int_inc_closed Zp.one_closed Zp_int_mult_closed val_ring_val_criterion 
          residue_of_prod val_Zp_p val_p val_pos val_ring_nat_pow_closed)
    have "\<And>x y x' y' n. x \<in> carrier Z\<^sub>p \<Longrightarrow> y \<in> carrier Z\<^sub>p \<Longrightarrow>
                          x' \<in> carrier Z\<^sub>p \<Longrightarrow> y' \<in> carrier Z\<^sub>p \<Longrightarrow> x n = x' n \<Longrightarrow> y n = y' n \<Longrightarrow> (x \<ominus>\<^bsub>Z\<^sub>p\<^esub> y) n = (x' \<ominus>\<^bsub>Z\<^sub>p\<^esub> y') n"
      using residue_of_diff by presburger
    then show ?thesis using 23 24  v_def v'_def 
      by (smt val_ring_memE pna'_closed pna_closed pnc'_closed pnc_closed to_Zp_closed to_Zp_minus)
  qed
  have 3: "val v = val v'"
    unfolding v_def v'_def 
    apply(rule val_ring_equal_res_imp_equal_val[of _ _ "e + 2*N"])
    using v_closed v_def apply blast
    using v'_closed v'_def apply blast
    using 1 unfolding v_def apply blast   
    using 0 unfolding v'_def apply blast   
    using 2     unfolding v_def v'_def by blast 
  then show "val (a \<ominus> c) = val (a' \<ominus> c')"
    using v_factor v'_factor val_mult prod_equal_val_imp_equal_val[of "\<pp>[^]N"]
    by (meson Qp.minus_closed Qp_nat_pow_nonzero val_ring_memE a'_closed assms(2) assms(7) local.a_closed p_nonzero)    
  have 4: "to_Zp v (e+3*N) = to_Zp v' (e+3*N)"
  proof-
    have 20: "to_Zp (\<pp>[^]N \<otimes> c) \<in> carrier Z\<^sub>p"
      using val_ring_memE pnc_closed to_Zp_closed by blast
    have 21: "to_Zp (\<pp>[^]N \<otimes> c') \<in> carrier Z\<^sub>p"
      using val_ring_memE pnc'_closed to_Zp_closed by blast
    have 23: "to_Zp (\<pp>[^]N \<otimes> c) (e+3*N) = to_Zp (\<pp>[^]N \<otimes> c') (e+3*N)"
      using assms(12) by blast
    have 24: "to_Zp (\<pp> [^] N \<otimes> a) (e+3*N)  = to_Zp (\<pp> [^] N \<otimes> a') (e+3*N) "
    proof-
      have 240: "to_Zp a (e + 2 * N) = to_Zp a' (e + 2 * N)"
        using assms(11) by blast
      have 241: "to_Zp (\<pp> [^] (N::nat) \<otimes> a) = ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a)"
        by (metis Q\<^sub>p_def Qp.int_inc_closed Zp.one_closed Zp_def Zp_int_mult_closed val_ring_val_criterion 
            local.a_closed p_pow_nonzero(1) padic_fields.inc_to_Zp padic_fields.p_natpow_inc
            padic_fields_axioms to_Zp_mult val_Zp_p val_p val_pos val_ring_nat_pow_closed)
      have 242: "to_Zp (\<pp> [^] (N::nat) \<otimes> a') = ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a')"
        by (metis Q\<^sub>p_def Qp.int_inc_closed Zp.one_closed Zp_def Zp_int_mult_closed val_ring_val_criterion 
            a'_closed p_pow_nonzero(1) padic_fields.inc_to_Zp padic_fields.p_natpow_inc 
            padic_fields_axioms to_Zp_mult val_Zp_p val_p val_pos val_ring_nat_pow_closed)
      have 243: "to_Zp a' \<in> carrier Z\<^sub>p"
        using val_ring_memE a'_closed to_Zp_closed by blast
      have 244: "to_Zp a \<in> carrier Z\<^sub>p"
        using val_ring_memE local.a_closed to_Zp_closed by blast
      have 245:"([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a) (e + 2 * N + N) = ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a') (e + 2 * N + N)"
        using 240 243 244 equal_res_ptimes_imp_equal_res[of "to_Zp a" "to_Zp a'" "e+2*N" N]
        by blast
      have 246: "to_Zp (\<pp> [^] (N::nat) \<otimes> a) (e + 2 * N + N) = ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a) (e + 2 * N + N)"
        using "241" by presburger
      have 247: "to_Zp (\<pp> [^] (N::nat) \<otimes> a) (e + 2 * N + N) = ([p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (N::nat) \<otimes>\<^bsub>Z\<^sub>p\<^esub> to_Zp a) (e + 2 * N + N)"
        using "246" by blast
      hence "to_Zp (\<pp> [^] (N::nat) \<otimes> a) (e + 2 * N + N) = to_Zp (\<pp> [^] (N::nat) \<otimes> a') (e + 2 * N + N)"
        using 241 242 245  by presburger
      thus ?thesis 
        by (smt Suc_numeral mult_2 mult_Suc_right semiring_norm(5) semiring_normalization_rules(21) semiring_normalization_rules(7))
    qed      
    have "\<And>x y x' y' n. x \<in> carrier Z\<^sub>p \<Longrightarrow> y \<in> carrier Z\<^sub>p \<Longrightarrow>
                          x' \<in> carrier Z\<^sub>p \<Longrightarrow> y' \<in> carrier Z\<^sub>p \<Longrightarrow> x n = x' n \<Longrightarrow> y n = y' n \<Longrightarrow> (x \<ominus>\<^bsub>Z\<^sub>p\<^esub> y) n = (x' \<ominus>\<^bsub>Z\<^sub>p\<^esub> y') n"
      using residue_of_diff by presburger
    then show ?thesis using 23 24  v_def v'_def 
      by (smt val_ring_memE pna'_closed pna_closed pnc'_closed pnc_closed to_Zp_closed to_Zp_minus)
  qed
  show "pow_res n (a \<ominus> c) = pow_res n (a' \<ominus> c')"
  proof-
    have "pow_res n v = pow_res n v'"
    proof-
      have 50: "val (v \<ominus> v') \<ge> e+3*N"
        using 4  
        by (metis equal_res_imp_val_diff_bound pna'_closed pna_closed pnc'_closed pnc_closed v'_def v_def val_ring_minus_closed)
      hence 51: "val (v \<ominus> v') \<ge> val v + N"
      proof-
        have 510: "val v + N < e + 2*N + eint N"
          using 1 by (metis add.commute eint.distinct(2) eint_add_left_cancel_less)
        have 511: "e + 2*N + eint N = e + 2*N + N"        
        using int_ops(5) plus_eint_simps(1) by presburger
        hence 512: "e + 2*N + eint N = e + 3*N" 
          by (metis add.commute left_add_mult_distrib mult.left_neutral numeral_Bit1 numeral_One one_add_one)
        hence "val v + N < e + 3*N"
          using 510  by presburger
        thus ?thesis 
          using 50 dual_order.trans less_le by blast
      qed
      have v_nonzero: "v \<in> nonzero Q\<^sub>p"
        by (metis "0" "3" val_ring_memE v_closed val_nonzero)
      have v'_nonzero: "v' \<in> nonzero Q\<^sub>p"
        using "0" val_ring_memE v'_closed val_nonzero by blast
      then have "ac N v = ac N v'"
        using 51 v_nonzero v'_nonzero 3 ac_val by blast

      then have "ac N (v \<otimes> inv v') = 1"
        using ac_inv'''(1) ac_mult' assms(13) nonzero_inverse_Qp v'_nonzero v_nonzero by presburger
      then have "v \<otimes> inv v' \<in> P_set n"
        using assms by (metis (no_types, opaque_lifting) "3" Q\<^sub>p_def Qp.Units_r_inv Qp.m_closed 
            Qp.nonzero_closed Zp_def nonzero_inverse_Qp padic_fields.Units_eq_nonzero
            padic_fields_axioms v'_nonzero v_nonzero val_mult val_one)
      thus ?thesis 
        using assms(14) equal_pow_resI'' v'_nonzero v_nonzero unfolding nonzero_def  by blast
    qed
    thus ?thesis unfolding v_def v'_def using equal_pow_resI'''
      by (metis Qp.not_eq_diff_nonzero Qp.r_right_minus_eq Qp_nat_pow_nonzero val_ring_memE
          \<open>val (a \<ominus> c) = val (a' \<ominus> c')\<close> a'_closed assms(14) assms(2) assms(7) eint.distinct(2)
          equal_pow_resI'' local.a_closed local.val_zero p_nonzero v'_def v'_factor v_def v_factor val_ord)
  qed
qed

lemma fact_4:
  fixes N::nat 
  fixes n::nat
  fixes a
  fixes x
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> \<xi> x = a"
  assumes "c \<in> \<O>\<^sub>p"
  assumes "\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n"
  assumes "to_Zp a (e + N) = to_Zp c (e + N)"
  assumes "N > 0"
  assumes "n > 0"
  shows "(UPQ.deriv (SA_poly_to_Qp_poly m x g) c) \<noteq> \<zero>"
        "pow_res n ((\<ominus> UPQ.to_fun (SA_poly_to_Qp_poly m x g) c) \<otimes> inv (UPQ.deriv (SA_poly_to_Qp_poly m x g) c)) = pow_res n (a \<ominus> c)"  
        "val ((\<ominus> UPQ.to_fun (SA_poly_to_Qp_poly m x g) c) \<otimes> inv (UPQ.deriv (SA_poly_to_Qp_poly m x g) c)) = val (a \<ominus> c)" 
proof-
  obtain G where G_def: "G = SA_poly_to_Qp_poly m x g"
    by blast 
  have G_closed: "G \<in> carrier (UP Q\<^sub>p)"
    using G_def assms  DL_2_3_10 DL_2_3_3 Q\<^sub>p_def Zp_def padic_fields.SA_poly_to_Qp_poly_closed padic_fields_axioms by blast
  have G_closed':"(\<And>n. G n \<in> \<O>\<^sub>p)" unfolding G_def using assms 
    by (metis (no_types, lifting) DL_2_3_10 DL_2_3_3 DL_2_3_4 PiE SA_poly_to_Qp_poly_coeff)
  then obtain h where h_def: "UPQ.to_fun G c \<in> \<O>\<^sub>p \<and> UPQ.deriv G c \<in> \<O>\<^sub>p \<and> h\<in> \<O>\<^sub>p \<and>
                  UPQ.to_fun G a = UPQ.to_fun G c \<oplus> UPQ.deriv G c \<otimes> (a \<ominus> c) \<oplus> (h \<otimes> (a \<ominus> c)[^](2::nat))"
    using assms G_closed Taylor_deg_1_expansion''[of G c a] 
    by (metis (no_types, lifting) DL_2_3_5 PiE)
  have a_closed: "a \<in> carrier Q\<^sub>p"
    using assms DL_2_3_10 DL_2_3_3 DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE val_ring_closed by auto 
  have 0: "G \<bullet> a = \<zero>"
    using assms a_closed unfolding G_def 
    by (metis (no_types, lifting) DL_2_3_3 Q\<^sub>p_def Z\<^sub>p_def denef_II_def denef_lemma_2_3.DL_2_3_7 denef_lemma_2_3_axioms denef_lemma_2_3_def padic_fields.SA_poly_to_SA_fun_formula)
  then have 1: "\<zero> =  UPQ.to_fun G c \<oplus> UPQ.deriv G c \<otimes> (a \<ominus> c) \<oplus> (h \<otimes> (a \<ominus> c)[^](2::nat))"
    using h_def by blast
  have 2: "h \<otimes> (a \<ominus> c)[^](2::nat) \<in> carrier Q\<^sub>p"
    apply(intro Qp.ring_simprules Qp.nat_pow_closed a_closed)
    using  h_def assms val_ring_closed by auto 
  have 3: "UPQ.deriv G c \<otimes> (a \<ominus> c) \<in> carrier Q\<^sub>p"
    by (metis DL_2_3_5 Qp.function_ring_car_memE Qp.m_closed Qp.minus_closed val_ring_memE assms(1) assms(2) h_def)
  have 30: "UPQ.to_fun G c \<in> carrier Q\<^sub>p"
    using val_ring_memE h_def by blast
  have 4: "\<ominus> UPQ.to_fun G c = UPQ.deriv G c \<otimes> (a \<ominus> c) \<oplus> (h \<otimes> (a \<ominus> c)[^](2::nat))"
    using 1 2 3 30 
    by (metis (no_types, lifting) Qp.add.inv_closed Qp.add.m_assoc Qp.add.m_closed Qp.l_neg Qp.minus_unique)
  have a_closed: "a \<in> \<O>\<^sub>p"
    using DL_2_3_5 assms(1) by blast
  have pderiv_G_closed: "\<And>n. UPQ.pderiv G n \<in> \<O>\<^sub>p"
    using G_closed' a_closed G_closed UPQ.UP_subring_pderiv_closed'[of \<O>\<^sub>p]  val_ring_subring by blast
  have 50: "UPQ.deriv G c = (UPQ.pderiv G)\<bullet>c"
    using G_closed assms val_ring_memE UPQ.pderiv_eval_deriv by presburger
  have 51: "UPQ.deriv G a = (UPQ.pderiv G)\<bullet>a"
    using DL_2_3_5 G_closed Qp.function_ring_car_memE UPQ.pderiv_eval_deriv assms(1) by blast
  hence 52: "val (UPQ.deriv G a) \<le> e"
    using 50  DL_2_3_9 G_closed assms unfolding G_def 
    by (metis DL_2_3_10 DL_2_3_3 DL_2_3_5 Q\<^sub>p_def Qp.function_ring_car_memE SA_poly_to_SA_fun_formula  UP_cring.pderiv_closed Zp_def padic_fields.SA_is_UP_cring padic_fields.SA_poly_to_Qp_poly_comm_pderiv padic_fields_axioms)
  have 53: "val (UPQ.pderiv G \<bullet> a) < eint (int (e + N))"
    using 52 assms 
    by (metis (no_types, opaque_lifting) "51" add.commute add_le_same_cancel2 dual_order.trans 
          eint_ord_simps(1) linorder_not_less of_nat_add of_nat_le_0_iff zero_less_iff_neq_zero)      
  hence 54: "val (UPQ.deriv G c) \<le> e"
    using a_closed poly_eval_equal_val[of "UPQ.pderiv G" a c "e + N"] pderiv_G_closed
        assms "50" "51" "52" G_closed UPQ.pderiv_closed by presburger  
  then have 55: "UPQ.deriv G c \<in> nonzero Q\<^sub>p"
    using G_closed assms 
    by (meson val_ring_memE eint_ile h_def val_nonzero')
  then have 5 : "UPQ.deriv G c \<in> Units   Q\<^sub>p"
    using Units_eq_nonzero by blast
  have 6: "inv (UPQ.deriv G c) \<otimes> (\<ominus> UPQ.to_fun G c) = inv (UPQ.deriv G c) \<otimes> (UPQ.deriv G c \<otimes> (a \<ominus> c) \<oplus> (h \<otimes> (a \<ominus> c)[^](2::nat)))"
    using "4" by presburger
  have 7: "inv (UPQ.deriv G c) \<otimes> (\<ominus> UPQ.to_fun G c) = (inv (UPQ.deriv G c) \<otimes> UPQ.deriv G c \<otimes> (a \<ominus> c)) \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)[^](2::nat))"
    using 6 
    by (metis "2" "3" "5" DL_2_3_5 Qp.Units_inv_closed Qp.function_ring_car_memE Qp.m_assoc Qp.minus_closed Qp.r_distr val_ring_memE assms(1) assms(2) h_def)
  have 8: "inv (UPQ.deriv G c) \<otimes> (\<ominus> UPQ.to_fun G c) = (a \<ominus> c) \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)[^](2::nat))"
    by (metis "3" "5" "7" DL_2_3_5 Qp.Units_inv_closed Qp.function_ring_car_memE Qp.inv_cancelR(1) Qp.m_assoc Qp.minus_closed val_ring_memE assms(1) assms(2) h_def)
  have 9: "(a \<ominus> c) \<in> carrier Q\<^sub>p"
    using val_ring_memE assms(2) local.a_closed by blast
  have 10: "inv (UPQ.deriv G c) \<otimes> (\<ominus> UPQ.to_fun G c) = (a \<ominus> c) \<otimes> (\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)))"
  proof-
    have "(h \<otimes> (a \<ominus> c)[^](2::nat)) = h \<otimes> (a \<ominus> c)\<otimes> (a \<ominus> c)"
      using h_def 9  assms 
      by (metis Qp.m_assoc Qp.nat_pow_eone Qp.nat_pow_mult val_ring_memE one_add_one)
    hence "(h \<otimes> (a \<ominus> c)[^](2::nat)) =(a \<ominus> c)\<otimes> h \<otimes>  (a \<ominus> c)"
      using h_def  9 Qp.m_comm val_ring_memE by presburger
    hence "inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)[^](2::nat)) =(a \<ominus> c) \<otimes> (inv (UPQ.deriv G c)) \<otimes> (h \<otimes> (a \<ominus> c))"  
      by (metis (no_types, lifting) "5" "9" Qp.Units_inv_closed Qp.m_assoc Qp.m_closed Qp.m_comm val_ring_memE h_def)
    then show ?thesis using 8 9 
      by (smt "5" Qp.Units_inv_closed Qp.Units_l_inv Qp.m_assoc Qp.m_closed Qp.r_distr Qp.r_one val_ring_memE h_def)
  qed
  have 11: "val (inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) = val h + val (a \<ominus> c) - val (UPQ.deriv G c)"
    using val_mult 
    by (metis (no_types, lifting) "5" "9" Qp.Units_inv_closed Qp.m_closed Qp.m_comm val_ring_memE Units_eq_nonzero h_def val_fract)
  have 12: "val (a \<ominus> c) \<ge> e + N"
  proof-
    have 120: "to_Zp (a \<ominus> c) (e + N) = 0"
      using assms a_closed  val_ring_memE res_diff_zero_fact'' to_Zp_closed to_Zp_minus by presburger
    hence "val_Zp (to_Zp (a \<ominus> c)) \<ge> e + N"
      using assms equal_res_imp_val_diff_bound local.a_closed to_Zp_val val_ring_minus_closed by presburger
    then show ?thesis
      by (meson assms(2) assms(4) equal_res_imp_val_diff_bound local.a_closed)
  qed
  have 13: "val (UPQ.deriv G c) \<noteq> \<infinity>"
    using 55 unfolding val_def 
    by (metis eint.distinct(2) val_def val_ord)
  hence 14: "val (a \<ominus> c) - val (UPQ.deriv G c) \<ge> e + N - val (UPQ.deriv G c)" 
    using 12 eint_minus_ineq by blast
  hence 15: "val (a \<ominus> c) - val (UPQ.deriv G c) \<ge> e + N - eint e" 
    using eint_minus_ineq'[of "val (UPQ.deriv G c)" e "e + N" "val (a \<ominus> c) - val (UPQ.deriv G c)"] 54
    by blast 
  have 16: "val (inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) \<ge> val (a \<ominus> c) - val (UPQ.deriv G c)"
    using "11" "13" "9" val_ring_memE eint_minus_ineq h_def val_mult val_val_ring_prod by presburger
  hence 17: "val (inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) \<ge> e + N - eint e"
    using 15 dual_order.trans by blast
  hence 18: "val (inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) \<ge> N"
    by (metis "11" add.commute add_diff_cancel idiff_eint_eint of_nat_add)
  have "(\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) \<ominus> \<one> = inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))"
    by (metis (no_types, lifting) "5" "9" Qp.Units_inv_closed Qp.add.inv_closed Qp.add.m_closed Qp.add.m_comm Qp.m_closed Qp.minus_eq Qp.one_closed Qp.r_neg1 val_ring_memE h_def)
  hence 190: "val ((\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) \<ominus> \<one>) \<ge> N"
    using 18 by presburger
  have 191: "val \<one> = val (\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)))"
  proof-
    have P0: "inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)) \<in> carrier Q\<^sub>p"
      using "5" "9" Qp.Units_inv_closed Qp.m_closed val_ring_memE h_def by presburger
    have P1: "val \<one> < val (inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)))"
      using 18 assms val_one 
      by (metis "11"  eint_ord_simps(2) less_le_trans of_nat_0_less_iff zero_eint_def)
    show ?thesis using P0 P1 val_one 
      by (metis Qp.add.m_closed Qp.one_closed \<open>\<one> \<oplus> inv UPQ.deriv G c \<otimes> (h \<otimes> (a \<ominus> c)) \<ominus> \<one> = inv UPQ.deriv G c \<otimes> (h \<otimes> (a \<ominus> c))\<close> ultrametric_equal_eq)
  qed
  have 192: "\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)) \<in> carrier Q\<^sub>p"
    by (meson "5" "9" Qp.Units_inv_closed Qp.add.m_closed Qp.m_closed Qp.one_closed val_ring_memE h_def)
  have 19: "ac N (\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) = ac N \<one>"
    using 190 191 192 ac_val[of "\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))" \<one> N]
    by (smt Qp.one_nonzero plus_eint_simps(1) val_nonzero' val_one zero_eint_def)
  hence 20: "ac N (\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))) = 1"
    by (metis Qp.one_nonzero ac_inv' ac_inv'''(2) ac_one' assms(5))
  have 21: "\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c)) \<in> P_set n"
    using 19 20 191 assms(3) val_one by (metis "192") 
  have "pow_res n ((\<ominus> UPQ.to_fun G c) \<otimes> inv (UPQ.deriv G c)) = pow_res n (a \<ominus> c)"  
    apply(rule equal_pow_resI''''[of _ _ _ "\<one> \<oplus> inv (UPQ.deriv G c) \<otimes> (h \<otimes> (a \<ominus> c))"]) using assms apply blast 
    using "30" "5" apply blast
      using "9" apply blast
        using "10" "30" "5" Qp.Units_inv_closed Qp.add.inv_closed Qp.m_comm apply presburger
          using "21" by blast
  thus "pow_res n ((\<ominus> UPQ.to_fun (SA_poly_to_Qp_poly m x g) c) \<otimes> inv (UPQ.deriv (SA_poly_to_Qp_poly m x g) c)) = pow_res n (a \<ominus> c)" 
    unfolding G_def by blast 
  show "val (\<ominus> (SA_poly_to_Qp_poly m x g \<bullet> c) \<div> UPQ.deriv (SA_poly_to_Qp_poly m x g) c) = val (a \<ominus> c)"
    using 10 190 assms val_mult val_one 
    by (metis "191" "192" "30" "5" "9" G_def Qp.Units_inv_closed Qp.add.inv_closed Qp.l_one Qp.m_comm Qp.one_closed)
  show "(UPQ.deriv (SA_poly_to_Qp_poly m x g) c) \<noteq> \<zero>"
    using "55" G_def Qp.nonzero_memE(2) by blast
qed

lemma g_not_zero:
"g \<noteq> \<zero>\<^bsub>UP (SA m)\<^esub>"
  using DL_2_3_5 DL_2_3_4 DL_2_3_3 DL_2_3_2 DL_2_3_1 DL_2_3_10
        UP_ring.deg_zero[of "SA m"] 
  by (metis UP_ring_def neq0_conv padic_fields.SA_is_ring padic_fields_axioms)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Completing the Proof\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The previous section showed how various conditions on the expression $\xi(x) - c(x)$ can be 
fully determined by certain congruences over the valuation ring. This section shows how to use those 
to complete the proof, using the basic proof scheme given by the lemma \texttt{SA\_fun\_proof} in 
\texttt{Constructing\_Semialgebraic\_Functions}.\<close>
lemma pre_denef_lemma_2_3_0:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "t \<in> carrier (Zp_res_ring (e+3*N))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). -N < val (c x) \<and> to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t}"
proof-
  obtain f where f_def: "f = \<pp>[^]N \<odot>\<^bsub>SA(m+k)\<^esub> c"
    by blast 
  have f_closed: "f \<in> carrier (SA (m+k))"
    unfolding f_def using assms SA_smult_closed[of  c] DL_2_3_10 p_natpow_closed(1) by blast
  have f_eval: "{x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>).  -N < val (c x) \<and> to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t} = 
                        {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>).  -N < val (c x) \<and> to_Zp (f x) (e+3*N) = t}"
    using SA_smult_formula[of c "m+k" "\<pp>[^]N"] assms unfolding f_def 
    by (metis (no_types, lifting) add.commute p_natpow_closed(1))
  have 0: " ([t] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (e + 3 * N) = t"
    using assms 
    by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  have 1: "[t] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p"
    by blast
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). -N < val (c x)}"
    by blast 
  have S_SA: "is_semialgebraic (k+m) S"
    unfolding S_def using assms semialg_val_strict_ineq_set_is_semialg''[of  c "k+m" "-N"] 
    by (smt DL_2_3_10 add.commute add_gr_0)
  obtain h where h_def: "h = fun_glue (m+k) S f \<one>\<^bsub>SA (m+k)\<^esub>"
    by blast 
  have h_closed: "h \<in> carrier (SA (m+k))"
    unfolding h_def using f_closed S_SA 
    by (metis DL_2_3_10 add.commute add_gr_0 fun_glue_closed monoid.one_closed padic_fields.SA_is_monoid padic_fields_axioms)
  have h': "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> h x \<in> \<O>\<^sub>p"
  proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
    have "val (h x) \<ge> 0"
    proof(cases "x \<in> S")
      case True
      then have "h x = f x"
        unfolding h_def 
        by (metis DL_2_3_10 S_SA add.commute add_gr_0 f_closed fun_glueE is_semialgebraic_closed monoid.one_closed padic_fields.SA_is_monoid padic_fields_axioms)
      then have 0: "h x = \<pp>[^]N \<otimes> (c x)"
        unfolding f_def using A assms SA_smult_formula p_natpow_closed(1) by blast
      have "c x \<in> carrier Q\<^sub>p"
        using A Qp.function_ring_car_memE SA_car_memE(2) assms(1) by blast
      hence "val (h x) = val (\<pp>[^]N) + val (c x)"
        unfolding 0 f_def using A assms val_mult[of "\<pp>[^]N" "c x"] 
        using p_natpow_closed(1) by blast
      hence 1: "val (h x) = N + val (c x)"
        by (metis int_pow_int val_p_int_pow)
      have "val (c x) > - N"
        using True unfolding S_def by blast 
      then show ?thesis using 1 True 
        by (metis add.right_neutral add_cancel_eint_geq add_diff_cancel_eint eint.distinct(2) eint_uminus_eq linorder_not_less order_le_less val_p_int_pow val_p_int_pow_neg)        
    next
      case False
      then have "h x = \<one>"
        unfolding h_def 
        by (metis (no_types, lifting) A DL_2_3_10 DiffI function_one_eval SA_one S_SA add.commute
            add_gr_0 f_closed fun_glueE' is_semialgebraic_closed monoid.one_closed padic_fields.SA_is_monoid padic_fields_axioms)        
      then show ?thesis using val_one 
        by (metis order_refl)      
    qed
    then show "h x \<in> \<O>\<^sub>p"  
      by (meson A Qp.function_ring_car_memE SA_car_memE(2) h_closed val_ringI)
  qed
  have 2: "\<And>x. x \<in> S \<Longrightarrow> h x = \<pp>[^]N \<otimes> (c x)"
  proof- fix x assume A: "x \<in> S"
    then have "h x = f x"
        unfolding h_def 
        by (metis DL_2_3_10 S_SA add.commute add_gr_0 f_closed fun_glueE is_semialgebraic_closed monoid.one_closed padic_fields.SA_is_monoid padic_fields_axioms)
      then show 0: "h x = \<pp>[^]N \<otimes> (c x)"
        unfolding f_def using A assms SA_smult_formula p_natpow_closed(1) 
        by (metis (no_types, lifting) S_def add.commute mem_Collect_eq)
    qed
  have 3: "{x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). -N < val (c x) \<and> to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t} = 
          S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (h x) (e+3*N) = t}"
  proof show "{x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}
    \<subseteq> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t}"
    proof(rule subsetI) fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}"
      then have "x \<in> S"
        unfolding S_def by blast 
      then show " x \<in> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t}"
      using 2 A unfolding S_def mem_Collect_eq using IntI S_def  order_refl subsetI subset_iff 
      proof -
      assume "x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>) \<and> eint (- int N) < val (c x)"
      assume a1: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>) \<and> eint (- int N) < val (c x) \<Longrightarrow> h x = \<pp> [^] N \<otimes> c x"
      assume "x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>) \<and> eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t"
      then have "to_Zp (h x) (e + 3 * N) = t"
        using a1 by presburger
      then show "x \<in> {rs \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). eint (- int N) < val (c rs)} \<inter> {rs \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h rs) (e + 3 * N) = t}"
        using S_def \<open>x \<in> S\<close> by blast
      qed
    qed
    show "S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}"
    proof(rule subsetI) fix x assume A: "x \<in> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t}"
      then show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}"
      using 2 unfolding S_def mem_Collect_eq 
      by (metis (mono_tags, lifting) IntE mem_Collect_eq)
    qed
  qed
  have 4: "is_semialgebraic (k+m)  {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (h x) (e+3*N) = t}"
    using h_closed h' val_ring_cong_set[of h "k+m" t "e+3*N"] 
    by (metis (no_types, lifting) DL_2_3_10 add.commute add_gr_0 assms(2))
  have 5: "is_semialgebraic (k + m) (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t})"
    using    S_SA  h_closed  add.commute 
      intersection_is_semialg[of "k+m" S " {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (h x) (e + 3 * N) = t}"]
      "4" by blast 
  hence 6: "is_semialgebraic (k + m){x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). -N < val (c x) \<and> to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t}"
    using 3 by presburger
  then show ?thesis using add.commute[of k m]    
    by (metis (no_types, lifting) Collect_cong val_p_int_pow val_p_int_pow_neg)
qed

lemma pre_denef_lemma_2_3_1:
  assumes "s \<in> carrier (Zp_res_ring (e+2*N))"
  assumes "N > 0"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s}"
proof-
  have 0: "s = ([s] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (e + 2 * N)"
    using assms 
 by (smt Zp_int_inc_rep p_residue_def p_residue_ring_car_memE(1) p_residue_ring_car_memE(2) residue_id)
  have  1: "([s] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) \<in> carrier Z\<^sub>p"
    using assms  by blast
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s} = take m  \<inverse>\<^bsub>m+k\<^esub>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x ) (e+2*N) = s}"
  proof-
    have 20: "k + m = m + k"
      by auto 
    show ?thesis 
      proof
        show "{x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (\<xi> (take m x)) (e + 2 * N) = s}
    \<subseteq> take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + 2 * N) = s}"
          by (smt add.commute add.left_commute evimage_eq le_add2 local.take_closed mem_Collect_eq mult.commute mult_2_right subset_iff)
        show "take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + 2 * N) = s}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>k + m\<^esup>). to_Zp (\<xi> (take m x)) (e + 2 * N) = s}"
          by (smt "20" evimage_eq mem_Collect_eq subset_iff)
      qed
    qed
  have 2: "{x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s} = take m  \<inverse>\<^bsub>m+k\<^esub>  {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x ) (e+2*N) =  ([s] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (e + 2 * N)}"
    using 0 2  by presburger
  have 3: "is_semialg_map (m + k) m (take m)"
    using DL_2_3_10 le_add1 take_is_semialg_map by blast
  have 4: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + 2 * N) = ([s] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (e + 2 * N)}"
    using assms 1 fact_1[of "e+2*N" "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"]  by linarith
  thus ?thesis 
    using 0 4 2 3  assms 
    semialg_map_evimage_is_semialg[of "m+k" m "take m" " {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + 2 * N) = ([s] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) (e + 2 * N)}"] DL_2_3_10
    using add_gr_0 by presburger
qed
 
lemma pre_denef_lemma_2_3_2:
  assumes "c \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  - (N::nat) < val (c x)}"
    using assms semialg_val_strict_ineq_set_is_semialg''[of c "m+k" "- (N::nat)"] DL_2_3_10 by blast 

lemma pre_denef_lemma_2_3_3:
  assumes "a \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). \<alpha> \<le> val (a x)}"
  using semialg_val_ineq_set_is_semialg''[of a "m+k" \<alpha>] assms DL_2_3_10 by blast

lemma xi_take_closed:
  assumes "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
  shows "\<xi> (take m x) \<in> \<O>\<^sub>p" "val (\<xi> (take m x)) \<ge> 0"
  using assms DL_2_3_5 take_closed[of m "m+k" x]
  apply (meson PiE le_add1)
  using assms DL_2_3_5 take_closed[of m "m+k" x]
  by (meson PiE le_add1 val_ring_memE(1))

lemma xi_cong_set_SA:
  assumes "N > 0"
  assumes "s \<in> carrier (Zp_res_ring N)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) N = s }"
proof-
  have 0: "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p"
    by blast 
  have 1: "([s]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) N = s"
    using assms 
    by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
  show ?thesis using assms 0 fact_1[of N "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"] unfolding 1 by blast 
qed

lemma xi_take_cong_sets_SA:
  assumes "N > 0"
  assumes "s \<in> carrier (Zp_res_ring N)"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) N = s }"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) N = s } = 
              take m  \<inverse>\<^bsub>m+k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) N = s }"
  proof
    show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) N = s} \<subseteq> take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) N = s}"
      apply(rule subsetI) unfolding evimage_def using take_closed[of m "m+k"] 
    by (metis (no_types, lifting) IntI le_add1 mem_Collect_eq vimageI)
    show " take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) N = s} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) N = s}"
      apply(rule subsetI) unfolding evimage_def using take_closed[of m "m+k"] by blast
  qed
  have 1: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) N = s }"
    using xi_cong_set_SA assms by blast 
  show ?thesis using 0 1 take_is_semialg_map 
    by (metis (no_types, lifting) DL_2_3_10 add_gr_0 le_add1 semialg_map_evimage_is_semialg)
qed

lemma pre_denef_lemma_2_3_4:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "(\<alpha>::eint) < e + N"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
proof(cases "\<alpha> < 0")
  case True
  have T0: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> \<xi> (take m x) \<in> \<O>\<^sub>p" proof- fix x assume "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
    then  have "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" using take_closed[of m "m + k" x] le_add1 by blast
    thus "\<xi> (take m x) \<in> \<O>\<^sub>p"  using DL_2_3_5 by blast 
  qed
  then have T1:  "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow>val ( \<xi> (take m x)) > \<alpha>"
    using True by (metis (no_types, opaque_lifting) val_ring_memE add.comm_neutral add.commute
                   add.right_neutral add_strict_mono comm_monoid_add_class.add_0  order_le_less)
  have T2: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>} = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) = \<alpha>}"
  proof
    show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) = \<alpha>}"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
      have 0: "\<xi> (take m x) \<in> carrier Q\<^sub>p \<and> val (\<xi> (take m x)) > \<alpha>"
        using A T0  T1 val_ring_memE by blast
      have 1: "c x \<in> carrier Q\<^sub>p"
        using assms A function_ring_car_closed SA_car_memE(2) by blast
      have 2: "val (\<xi> (take m x) \<ominus> c x) < val (\<xi> (take m x))"
        using  0  A by blast 
      then have "val (\<xi> (take m x) \<ominus> (\<xi> (take m x) \<ominus> c x)) = val (\<xi> (take m x) \<ominus> c x)"
        using 0 1  assms T1 val_ultrametric_noteq'[of "\<xi> (take m x)" "\<xi> (take m x) \<ominus> c x" ] 
        by blast 
      then have  "val (c x) = val (\<xi> (take m x) \<ominus> c x)"
        by (smt "0" "1" "2" min_le_iff_disj neq_iff not_less val_ultrametric' val_ultrametric_noteq')
      then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) = \<alpha>}"
        using A by blast 
    qed
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) = \<alpha>} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) = \<alpha>}"
      then have "val (c x) < val (\<xi> (take m x))"
        using  T1[of x] by blast 
      then have "val (\<xi> (take m x) \<ominus> c x) = \<alpha>"
        using T0 T1 assms A val_ultrametric_noteq'[of "\<xi> (take m x)" "c x"] 
        by (metis (mono_tags, lifting) function_ring_car_closed val_ring_memE SA_car_memE(2) mem_Collect_eq)
      thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
        using A by blast 
    qed
  qed  
  show "is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
    using T2 semialg_val_eq_set_is_semialg'[of  c "m + k" \<alpha>] DL_2_3_10 add_gr_0 assms(1) by presburger
next
  case False
  obtain I where I_def: "I = {(t, s) \<in> carrier (Zp_res_ring (e+N)) \<times> carrier (Zp_res_ring (e+N)). 
                            (\<exists>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha> \<and> 
                                          to_Zp (\<xi> (take m x)) (e+N) = s \<and> to_Zp (c x) (e+N) = t) }"
    by blast 
  have p_fin: "finite (carrier (Zp_res_ring (e+N)) \<times> carrier (Zp_res_ring (e+N)))" by (meson finite_SigmaI residue_ring_card)
  have "I \<subseteq>(carrier (Zp_res_ring (e+N)) \<times> carrier (Zp_res_ring (e+N)))" unfolding I_def by blast 
  hence I_fin: "finite I" using p_fin finite_subset by blast
  have 0: "\<And>t s x. (t, s) \<in> I \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> c x \<in> \<O>\<^sub>p \<Longrightarrow>  to_Zp (\<xi> (take m x)) (e+N) = s \<Longrightarrow> to_Zp (c x) (e+N) = t
            \<Longrightarrow> val (\<xi> (take m x) \<ominus> c x) = \<alpha>"
  proof- fix t s x assume A: "(t, s) \<in> I" "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)" "to_Zp (\<xi> (take m x)) (e+N) = s" "to_Zp (c x) (e+N) = t" "c x \<in> \<O>\<^sub>p"
    obtain y where y_def: "y \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<and> val (\<xi> (take m y) \<ominus> c y) = \<alpha> \<and> 
                                          to_Zp (\<xi> (take m y)) (e+N) = s \<and> to_Zp (c y) (e+N) = t"
      using A(1) unfolding I_def by blast 
    have 0: "val (\<xi> (take m y) \<ominus> c y) < e + N"
      using y_def assms by blast 
    have 1: "val (c y) \<ge> 0"
    proof(rule ccontr) assume C: " \<not> 0 \<le> val (c y)" then have C0: "val (c y) < 0" using not_le by blast
      have C1: "c y \<in> carrier Q\<^sub>p"
        using y_def assms  function_ring_car_closed SA_car_memE(2) by blast
      have C2: "\<xi> (take m y) \<in> carrier Q\<^sub>p"
        using DL_2_3_5 y_def take_closed by (meson function_ring_car_closed le_add1)
      have  "\<xi> (take m y) \<in> \<O>\<^sub>p"
      proof- have "take m y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" using  y_def take_closed[of m " m + k " y] by linarith
        then show ?thesis 
          using DL_2_3_5 by blast 
      qed
      hence C3: "val (\<xi> (take m y)) \<ge> 0"
        using val_ring_memE by blast
      hence "val (c y) <val (\<xi> (take m y))"
        by (metis (no_types, opaque_lifting) C0 less_le_trans )
      hence "val (c y) = val (\<xi> (take m y) \<ominus> c y) "
        using C1 C2 val_ultrametric_noteq' by presburger
      then show False using False  by (metis C0 y_def)
    qed
    have 2: "c y \<in> \<O>\<^sub>p"
      using 1 function_ring_car_closed Qp_val_ringI SA_car_memE(2) assms(1) y_def by blast
    have 3: "\<xi> (take m y) \<in> \<O>\<^sub>p"
      using y_def DL_2_3_5 take_closed[of m "m+k" y] by (meson PiE le_iff_add)
    have 4: "to_Zp (\<xi> (take m y)) (e+N) \<noteq> to_Zp (c y) (e+N)"
    proof
      assume " to_Zp (\<xi> (take m y)) (e + N) = to_Zp (c y) (e + N)"
      then have "(to_Zp (\<xi> (take m y)) \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp (c y)) (e + N) = 0"
        using 2 3  val_ring_memE res_diff_zero_fact'' to_Zp_closed by presburger
      then have "to_Zp (\<xi> (take m y) \<ominus>(c y)) (e + N) = 0"
        using 2 3 to_Zp_minus by presburger
      then have "val_Zp (to_Zp (\<xi> (take m y) \<ominus>(c y))) \<ge> e + N"
      proof(cases "to_Zp (\<xi> (take m y) \<ominus>(c y)) = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
        case True
        then show ?thesis 
          using eint_ord_simps(3) val_Zp_def by presburger
      next
        case False
        then show ?thesis unfolding val_Zp_def using above_ord_nonzero 
          by (smt "2" "3" val_ring_memE Zp.minus_closed \<open>to_Zp (\<xi> (take m y) \<ominus> c y) (e + N) = 0\<close> 
              eint_ord_simps(1) ord_Zp_def to_Zp_closed to_Zp_minus)
      qed
      then have "val (\<xi> (take m y) \<ominus>(c y)) \<ge> e + N"
        using 2 3 by (simp add: to_Zp_val val_ring_minus_closed)
      then show False using False  y_def assms(2) not_less by blast
    qed
    hence 5: "to_Zp (\<xi> (take m x)) (e+N) \<noteq> to_Zp (c x) (e+N)"
      using A(3) A(4) y_def by linarith
    have 6: "\<xi> (take m x) \<in> \<O>\<^sub>p"
      using A(2) xi_take_closed(1) by blast
    have 7: "to_Zp (\<xi> (take m x)\<ominus> (c x)) (e+N) \<noteq> 0"
      using 6 A(5) 5 
      by (metis val_ring_memE res_diff_zero_fact(1) to_Zp_closed to_Zp_minus)
    have 8: "to_Zp (\<xi> (take m x)\<ominus> (c x)) (e+N) = to_Zp (\<xi> (take m y)\<ominus> (c y)) (e+N)"
      using y_def  A "2" "3" "6" val_ring_res by presburger
    then show "val (\<xi> (take m x)\<ominus> (c x)) = \<alpha>"
      using y_def equal_res_equal_val by (metis "0" "2" "3" "6" A(5) val_ring_minus_closed)
  qed
  obtain F where F_def: "F =(\<lambda> (t,s). {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e+N) = s}
                                   \<inter>  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e+N) = t})"
    by blast 
  have F_SA: "\<And> ps. ps \<in> I \<Longrightarrow> is_semialgebraic (m+k) (F ps)"
  proof- fix ps assume A: "ps \<in> I" then obtain t s where ts_def: "ps = (t, s)" by (meson surj_pair)
    have s_closed: "s \<in> carrier (Zp_res_ring (e+N))"
      using ts_def  A unfolding I_def by blast 
    have t_closed: "t \<in> carrier (Zp_res_ring (e+N))"
      using ts_def  A unfolding I_def by blast 
    have 0: "0 < e + N"
      using assms by (metis False gr0I of_nat_0 zero_eint_def)
    have 1: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e+N) = s}"
      using assms xi_take_cong_sets_SA[of "e + N" s k] s_closed 0  by blast 
    have 2: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e+N) = t}"
      using assms t_closed 0 res_eq_set_is_semialg[of "m+k" c t "e+N"]  DL_2_3_10 by blast
    then show "is_semialgebraic (m+k) (F ps)" using A 1 intersection_is_semialg[of "m+k"]
      unfolding F_def by (metis (mono_tags, lifting) case_prod_conv ts_def)
  qed
  have F_SA_partitions:  "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>} = \<Union> (F ` I)"
  proof
    show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>} \<subseteq> \<Union> (F ` I)"
    proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
      then have 0: "\<xi> (take m x) \<ominus> c x \<in> \<O>\<^sub>p"
        using False 
        by (metis (mono_tags, lifting) function_ring_car_closed Q\<^sub>p_def Qp.minus_closed SA_car_memE(2) Zp_def \<iota>_def assms(1) mem_Collect_eq not_less padic_fields.val_ring_memE padic_fields_axioms val_ring_memI xi_take_closed(1))
      then have 1: "c x \<in> \<O>\<^sub>p"
        using A res_diff_in_val_ring_imp_in_val_ring[of "\<xi> (take m x)" "c x"]
        by (metis (no_types, lifting) function_ring_car_closed SA_car_memE(2) assms(1) mem_Collect_eq xi_take_closed(1))
      obtain s where s_def: "to_Zp (\<xi> (take m x)) (e+N) = s"
        by blast 
      obtain t where t_def: "to_Zp (c x) (e+N) = t"
        by blast 
      have 2: "(t, s) \<in> carrier (Zp_res_ring (e+N)) \<times> carrier (Zp_res_ring (e+N))"
        using s_def t_def  0 1 A 
        by (metis (no_types, lifting) mem_Collect_eq mem_Sigma_iff residue_closed to_Zp_closed val_ring_memE(2) xi_take_closed(1))
      have 3: "x\<in>carrier (Q\<^sub>p\<^bsup>m + k\<^esup>) \<and> val (\<xi> (take m x) \<ominus> c x) = \<alpha> \<and> to_Zp (\<xi> (take m x)) (e + N) = s \<and> to_Zp (c x) (e + N) = t"
        using 0 1 2 s_def t_def A by blast
      hence st_closed: "(t, s) \<in> I"
        unfolding I_def using 2  by blast  
      then have " x \<in> F (t, s)"
        unfolding F_def using s_def  t_def A 1  by blast
      thus "x \<in> \<Union> (F ` I)"
        using st_closed by blast
    qed
    show "\<Union> (F ` I) \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
    proof fix x assume A: " x \<in> \<Union> (F ` I)"
      then obtain s t where st_def: "(s, t) \<in> I \<and>  x \<in> F (s, t)"
        using I_def by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
        using A unfolding F_def by blast 
      then show " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
        using x_closed st_def 0 unfolding F_def  by blast
    qed
  qed
  have FI_finite: "finite (F` I)"
    using I_fin by blast
  show ?thesis using FI_finite  F_SA finite_union_is_semialgebraic[of "F` I" "m+k"] 
    unfolding F_SA_partitions by (meson image_subsetI is_semialgebraicE)
qed

lemma pre_denef_lemma_2_3_5:
  assumes "c \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < e + N}"
proof-
  obtain F where F_def: "F = (\<lambda> \<alpha>.{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>})"
    by blast 
  have F_SA: "\<And>\<alpha>::eint. \<alpha> < e + N \<Longrightarrow> is_semialgebraic (m+k) (F \<alpha>)"
    using pre_denef_lemma_2_3_4[of  c k _ N] assms unfolding F_def by blast
  have F_partitions: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < e + N} =
           \<Union> (F` eint `{0..<e+N})"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}
    \<subseteq> \<Union> (F ` (\<lambda>x. eint (int x)) ` {0..<e + N})"
    proof (rule subsetI) fix x assume A: " x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))} "
      obtain n where n_def: "val (\<xi> (take m x) \<ominus> c x) = eint n "
        using A by (metis (mono_tags, lifting) eint_iless mem_Collect_eq)
      then have 0: "nat n \<in> {0..< e + N}"
        using A unfolding n_def by (metis (mono_tags, lifting) atLeastLessThan_iff eint_ord_simps(1)
                              eint_ord_simps(2) le0 mem_Collect_eq n_def nat_less_iff zero_eint_def)
      have 1: "x \<in> F (nat n)"
        unfolding F_def using n_def A  by (smt eint_defs(1) eint_ord_simps(1) int_nat_eq mem_Collect_eq)
      show " x \<in> \<Union> (F ` (\<lambda>x. eint (int x)) ` {0..<e + N}) "
        using 1 0 A   by blast 
    qed
    show "\<Union> (F ` (\<lambda>x. eint (int x)) ` {0..<e + N})
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}"
    proof fix x assume A: "x \<in> \<Union> (F ` (\<lambda>x. eint (int x)) ` {0..<e + N})"
      then obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> {0..<e+N} \<and> x \<in> F (eint \<alpha>)" by blast 
      then have "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<and> val (\<xi> (take m x) \<ominus> c x) = \<alpha>"
        unfolding F_def by blast 
      then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}"
        using \<alpha>_def 
        by (metis (no_types, lifting) atLeastLessThan_iff eint_ord_simps(2) mem_Collect_eq of_nat_0 of_nat_less_iff order_le_less zero_eint_def)
    qed
  qed
  have 0: "finite (F` eint `{0..<e+N})"
    by blast
  have 1: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < e + N}"
    using F_SA finite_union_is_semialgebraic[of "F` eint `{0..<e+N}" "m+k"] unfolding  F_partitions 
    by (smt "0" atLeastLessThan_iff eint_ord_simps(2) imageE image_subsetI is_semialgebraicE of_nat_less_iff)
  have 2: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
  proof-
    have 00: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0} = 
                {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) < 0}"
    proof
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) < 0}"
      proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
        then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
          by blast 
        have 0: "val (\<xi> (take m x)) > val (\<xi> (take m x) \<ominus> c x)"
          using x_closed A by (metis (no_types, lifting) less_le_trans mem_Collect_eq xi_take_closed(2))
        then have "val (c x) = val (\<xi> (take m x) \<ominus> c x)"
          by (metis (mono_tags, lifting) A function_ring_car_closed val_ring_memE val_ring_memE 
              SA_car_memE(2) assms(1) mem_Collect_eq neq_iff not_less val_ring_memI val_ring_minus_closed 
              val_ultrametric_noteq' val_ultrametric_noteq'' xi_take_closed(1))
        then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) < 0}"
          using A by (metis (mono_tags, lifting) mem_Collect_eq)
      qed
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) < 0} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
      proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) < 0}"
        have "val (\<xi> (take m x)) \<ge> 0"
          using A by (metis (mono_tags, lifting) mem_Collect_eq xi_take_closed(2))
        then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
          using A 
          by (metis (mono_tags, lifting) DL_2_3_5 function_ring_car_closed Qp.minus_closed val_ring_memE 
              SA_car_memE(2) assms(1) le_add1 local.take_closed mem_Collect_eq not_less 
              res_diff_in_val_ring_imp_in_val_ring val_ring_memI)
      qed
    qed
    show ?thesis unfolding 00 using assms semialg_val_strict_ineq_set_is_semialg'[of  c"m+k" 0] 
      using DL_2_3_10 by blast
  qed
  have "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))} 
        = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < e + N} \<union>
          {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
  proof
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))} \<union>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}"
      apply(rule subsetI)
      by (metis (no_types, lifting) Un_iff mem_Collect_eq not_less)
    show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). 0 \<le> val (\<xi> (take m x) \<ominus> c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))} \<union>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < 0}
    \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}"
     proof- have 0: "\<And>\<alpha>::eint. \<alpha> < 0 \<Longrightarrow> \<alpha> < e + N"
      by (metis add.commute eint_pow_int_is_pos gr0I less_le_trans of_nat_0 of_nat_0_less_iff order_le_less zero_eint_def)
    show ?thesis 
    apply(rule subsetI) using 0 by blast
   qed
  qed
  thus ?thesis using 1 2 union_is_semialgebraic by presburger
qed

lemma xi_res_eq_set_is_semialg:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "N > 0"
  shows "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
proof-
  have m_pos: "m > 0"
    by (simp add: DL_2_3_10)
  obtain A where A_def: "A = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
    by blast 
  obtain F where F_def: "F = (\<lambda>s. {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e+N) = s} \<inter> A)"
    by blast 
  have F_partitions: "A = \<Union> (F` (carrier (Zp_res_ring (e+N))))"
  proof 
    show " A \<subseteq> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
    proof fix x assume A: "x \<in> A"
      then have 0: "c x \<in> \<O>\<^sub>p"
        using A_def by blast
      then obtain s where s_def: "s = to_Zp (c x ) (e+N)"
        by blast 
      have "s \<in> carrier (Zp_res_ring (e+N))"
        using s_def 0  val_ring_memE residue_closed to_Zp_closed by blast
      then have "x \<in> F s"
        using 0 A unfolding F_def s_def A_def by blast
      then show " x \<in> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
        using \<open>s \<in> carrier (residue_ring (p ^ (e + N)))\<close> by blast
    qed
    show " \<Union> (F ` carrier (residue_ring (p ^ (e + N)))) \<subseteq> A"
      unfolding F_def by blast 
  qed
  have Fs_finite: "finite (F` (carrier (Zp_res_ring (e+N))))"
    using residues.finite 
    by (meson finite_imageI padic_fields.prime padic_fields_axioms padic_integers.residue_ring_card padic_integers_def)
  have Fs_semialg: "\<And>s. s \<in> carrier (Zp_res_ring (e+N)) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
  proof- fix s assume A: "s \<in> carrier (Zp_res_ring (e+N))"
    have 0: "F s = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e+N) = s} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  to_Zp (\<xi> (take m x)) (e+N) = s}"
    proof
      show "F s \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e + N) = s} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
        unfolding F_def A_def by blast
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e + N) = s} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<subseteq> F s"
        unfolding F_def A_def by blast
    qed
    have 1: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (c x) (e+N) = s}"
      using assms res_eq_set_is_semialg[of "m+k" c s "e+N"] A m_pos by linarith
    have 00: "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p"
      by blast
    have 11: "([s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) (e+N) =  s"
      using A 
      by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
    then obtain a where a_def: "a \<in> carrier Z\<^sub>p \<and> a (e+N) = s"
      using 00 by blast 
    have 2: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
    proof-
      have 20: "0 < e + N"
        using assms by (simp add: assms(2))
      have 21: " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} = 
                  take m  \<inverse>\<^bsub>m+k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
      proof
        show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<subseteq> take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
          using a_def take_closed by (smt evimageI2 le_add1 mem_Collect_eq subsetI)
        show "take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
          unfolding evimage_def using a_def  by blast
      qed
      thus ?thesis
        using fact_1[of "e+N" a] assms a_def 21 take_is_semialg_map[of m "m+k"] m_pos semialg_map_evimage_is_semialg
          "20" DL_2_3_10 le_add1 semialg_map_evimage_is_semialg 
        by (metis (no_types, lifting) add_gr_0)
    qed
    show "is_semialgebraic (m + k) (F s)"
      using 0 1 2 intersection_is_semialg by presburger
  qed
  have "is_semialgebraic (m+k) A"
    using F_partitions Fs_finite Fs_semialg
    by (meson finite_union_is_semialgebraic image_subset_iff is_semialgebraicE)
  thus ?thesis unfolding A_def by blast 
qed

lemma helper_partition_lemma:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "is_semialgebraic (m+k) (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -(N::nat)})"
  assumes "is_semialgebraic (m+k) (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) > -(N::nat) \<and> val (\<xi> (take m x) \<ominus> c x) < e + N})"
  assumes "is_semialgebraic (m+k) (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (c x) \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)})"
  assumes "S \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
  shows "is_semialgebraic (m+k) S"
proof- 
  obtain S0 where S0_def: "S0 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
    by blast 
  obtain S1 where S1_def: "S1 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) > -N \<and> val (\<xi> (take m x) \<ominus> c x) < e + N}"
    by blast 
  obtain S2 where S2_def: "S2 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (c x) \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
    by blast 
  have S_cover: "S = S0 \<union> S1 \<union> S2"
  proof
    show "S \<subseteq> S0 \<union> S1 \<union> S2"
    proof fix x assume A: "x \<in> S"
      show "x \<in> S0 \<union> S1 \<union> S2"
      proof(cases "x \<in> S0 \<or> x \<in> S1")
        case True
        then show ?thesis by blast 
      next
        case False
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using assms A by blast 
        have x_not_S0: "x \<notin> S0"
          using False by blast 
        then have F0: "val (c x) > -N"
          unfolding S0_def using x_closed 
          by (metis (mono_tags, lifting) A IntI linorder_not_less mem_Collect_eq)
        have x_not_S1: "x \<notin> S1"
          using False by blast 
        hence F1: "val (\<xi> (take m x) \<ominus> c x) \<ge> e + N"
          unfolding S1_def using F0 x_closed 
          by (metis (no_types, lifting) A Int_Collect linorder_not_less)
        have xi_take_closed: "\<xi> (take m x) \<in> \<O>\<^sub>p"
          using x_closed DL_2_3_5 
          by (meson PiE le_add1 local.take_closed)
        hence F2: "val (\<xi> (take m x)) \<ge> 0"
          using val_ring_memE by blast
        have cx_closed: "c x \<in> carrier Q\<^sub>p"
          using SA_car_closed assms(1) x_closed by blast
        have F3: "val (c x) \<ge> 0"
        proof-
          have "val (\<xi> (take m x) \<ominus> c x) \<ge> 0"
            using F1 
            by (metis add.commute add.right_neutral dual_order.trans eint.distinct(2)
                eint_add_left_cancel_le eint_ord_simps(1) of_nat_0_le_iff of_nat_add order_refl plus_eint_simps(1))
          then show ?thesis 
            using F1 F2 
            by (metis (no_types, opaque_lifting) val_ring_memE(2) cx_closed dual_order.trans less_le_trans 
                linorder_not_less order_refl val_ultrametric_noteq' xi_take_closed)
        qed
        then have cx_closed': "c x \<in> \<O>\<^sub>p"
          using val_ring_val_criterion cx_closed by blast
        have "to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)"
        proof-
          have "val_Zp (to_Zp (\<xi> (take m x) \<ominus> c x)) \<ge> e + N"
            using F1 cx_closed' to_Zp_val val_ring_minus_closed xi_take_closed by presburger
          hence "val_Zp (to_Zp (\<xi> (take m x)) \<ominus>\<^bsub>Z\<^sub>p\<^esub>to_Zp (c x)) \<ge> e + N"
            by (simp add: cx_closed' to_Zp_minus xi_take_closed)    
          then show ?thesis 
            using val_ring_memE Zp.minus_closed cx_closed res_diff_zero_fact(1) to_Zp_closed xi_take_closed zero_below_val_Zp by presburger
        qed
        then show ?thesis 
          by (smt A F3 Int_Collect S2_def UnCI val_ring_val_criterion cx_closed x_closed)        
      qed
    qed
    show "S0 \<union> S1 \<union> S2 \<subseteq> S"
      unfolding S0_def S1_def S2_def by blast 
  qed
  have "is_semialgebraic (m+k) (S0 \<union> S1 \<union> S2)"
    by(intro union_is_semialgebraic, unfold S0_def S1_def S2_def, 
          intro assms, intro assms, intro assms)
  thus ?thesis 
    unfolding S_cover unfolding S1_def S2_def S0_def by auto 
qed

lemma val_leq_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "a \<in> carrier (SA (m+k))"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
proof-
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
    by blast 
  obtain n where n_def: "(n::nat) > 0"
    by blast 
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using n_def nth_power_fact' by blast 
  obtain S0 where S0_def: "S0 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
    by blast 
  obtain S1 where S1_def: "S1 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) > -N \<and> val (\<xi> (take m x) \<ominus> c x) < e + N}"
    by blast 
  obtain S2 where S2_def: "S2 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (c x) \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
    by blast 
  have S0_semialg: "is_semialgebraic (m+k) S0" 
  proof-
    have 0: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N} \<Longrightarrow> val (\<xi> (take m x) \<ominus> c x) = val (c x)"
    proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
        using A assms by force          
      have takemx_closed: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using le_add1 local.take_closed x_closed by blast
      have cx_closed: "c x \<in> carrier Q\<^sub>p"
        using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms x_closed by blast
      have ax_closed: "a x \<in> carrier Q\<^sub>p"
        using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(2) padic_fields.SA_car_memE(2) padic_fields_axioms x_closed by blast
      have 00: "0 \<le> val (\<xi> (take m x))"
        by (metis DL_2_3_5 PiE val_ring_memE takemx_closed)
      have 01: "val (c x) < 0"
      proof-
        have "-N < (0::eint)"
          by (metis N_def add.right_neutral eint.distinct(2) eint_0_iff(2) eint_add_cancel_fact
              eint_add_left_cancel_less eint_ord_simps(1) eint_ord_simps(4) idiff_0 idiff_0_right 
              less_infinityE nat_int nat_zminus_int of_nat_0_le_iff order.not_eq_order_implies_strict 
              the_eint.simps zero_less_iff_neq_zero)
        then show ?thesis  
          using A N_def less_le_trans linorder_not_less by blast
      qed
      then have "val (c x) < val (\<xi> (take m x))"
        using 00 less_le_trans by blast 
      then show "val (\<xi> (take m x) \<ominus> c x) = val (c x)" 
        using DL_2_3_5 Qp.function_ring_car_memE cx_closed takemx_closed val_ultrametric_noteq' by blast
    qed
    have "S0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  val (c x) \<le> val (a x)}"
    proof
      show "S0 \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> val (a x)}"
      proof fix x assume A: "x \<in> S0"
        then have "val (\<xi> (take m x) \<ominus> c x) = val (c x)"
          unfolding S0_def using 0 by blast
        then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> val (a x)}"
          using A unfolding S0_def 
          by (metis (no_types, lifting) Int_Collect S_def mem_Collect_eq)
      qed
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> val (a x)} \<subseteq> S0"
      proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> val (a x)}"
        then have " val (\<xi> (take m x) \<ominus> c x) = val (c x)"
          using 0  by blast
        then show "x \<in> S0"  
          unfolding S0_def using S_def assms semialg_val_ineq_set_is_semialg semialg_val_ineq_set_is_semialg'
          by (metis (no_types, lifting) A Int_Collect mem_Collect_eq)
      qed
    qed
    then show ?thesis 
      using semialg_val_ineq_set_is_semialg'[of  c "m + k" "-N"] 
            semialg_val_ineq_set_is_semialg[of c "m + k"  a] assms add_gr_0 intersection_is_semialg 
           DL_2_3_10 by presburger     
  qed
  have S1_semialg: "is_semialgebraic (m+k) S1"
  proof-
    obtain F where F_def: "F = (\<lambda> s \<in> carrier (Zp_res_ring (e+2*N)). {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s} \<inter> S1)"
      by blast 
    have F_partitions: "S1 = \<Union> (F `(carrier (Zp_res_ring (e+2*N))))"
    proof 
      show "S1 \<subseteq> \<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
      proof fix x assume A: "x \<in> S1"
        then have "\<xi> (take m x) \<in> \<O>\<^sub>p"
          using DL_2_3_5 unfolding S1_def 
          by (metis (no_types, lifting) Int_Collect PiE le_add1 local.take_closed)
        then have "to_Zp (\<xi> (take m x)) (e+2*N) \<in> carrier (Zp_res_ring (e+2*N))"
          using val_ring_memE residue_closed to_Zp_closed by blast
        then have "to_Zp (\<xi> (take m x)) (e+2*N) \<in> carrier (Zp_res_ring (e+2*N)) \<and> x \<in> F (to_Zp (\<xi> (take m x)) (e+2*N))"
          using A unfolding F_def S1_def
        proof -
          assume a1: "x \<in> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}"
          have "\<forall>i I f. (i::int) \<notin> I \<or> restrict f I i = (f i::((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list set)"
            by (meson restrict_apply')
          then show "to_Zp (\<xi> (take m x)) (e + 2 * N) \<in> carrier (residue_ring (p ^ (e + 2 * N))) \<and> x \<in> (\<lambda>i\<in>carrier (residue_ring (p ^ (e + 2 * N))). {rs \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m rs)) (e + 2 * N) = i} \<inter> (S \<inter> {rs \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c rs) \<and> val (\<xi> (take m rs) \<ominus> c rs) < eint (int (e + N))})) (to_Zp (\<xi> (take m x)) (e + 2 * N))"
            using a1 \<open>to_Zp (\<xi> (take m x)) (e + 2 * N) \<in> carrier (residue_ring (p ^ (e + 2 * N)))\<close> by blast
        qed  
        then show "x \<in> \<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
          by blast
      qed
      show "\<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N)))) \<subseteq> S1"
        unfolding F_def 
        by (smt Collect_mem_eq Int_Collect UN_ball_bex_simps(2) image_restrict_eq semiring_normalization_rules(7) subset_iff)
    qed
    have 0:"\<And>s. s \<in> carrier (Zp_res_ring (e+2*N)) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
    proof- fix s assume A: "s \<in> carrier (Zp_res_ring (e+2*N))"
      show "is_semialgebraic (m+k) (F s)"
      proof(cases "F s = {}")
        case True
        then show ?thesis 
          by (simp add: empty_is_semialgebraic)        
      next
        case False
        have Fs_closed: "F s \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using A unfolding F_def 
          by (smt IntE mem_Collect_eq restrict_apply' subsetI)            
        obtain G where G_def: "G = (\<lambda> t \<in> carrier (Zp_res_ring (e + 3*N)). {x \<in> F s. to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t})"
          by blast 
        have G_partitions: "F s = \<Union> (G ` (carrier (Zp_res_ring (e + 3*N))))"
        proof 

            show "F s \<subseteq> \<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
            proof fix x assume A0: "x \<in> F s"
              then have "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using Fs_closed by blast 
              have "x \<in> S1" using A0 A unfolding F_def 
                by (metis (no_types, lifting) IntE restrict_apply')
              then have 0: "val (c x) \<ge> eint (-N)"
                by (metis (no_types, lifting) Int_Collect S1_def le_cases linorder_not_less)
              have cx_closed: "c x \<in> carrier Q\<^sub>p"
                by (metis (no_types, lifting) Int_Collect Q\<^sub>p_def Qp.function_ring_car_memE 
                    S1_def Zp_def \<open>x \<in> S1\<close> assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms)
              have 1: "val (\<pp>[^]N \<otimes> c x) \<ge> N + eint (-N)"
                using DL_2_3_5 Fs_closed cx_closed 0 val_mult[of "\<pp>[^]N" "c x"]
                by (metis eint_add_left_cancel_less linorder_not_less ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) val_ord)  
              then have 2: "\<pp>[^]N \<otimes> c x \<in> \<O>\<^sub>p"
                by (metis Qp.int_inc_closed Qp.int_nat_pow_rep Qp.m_closed cx_closed p_intpow_closed(1)
                    p_intpow_inv' times_p_pow_val val_one val_p_int_pow val_ringI)
              then have 3: "to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) \<in> carrier (Zp_res_ring (e+3*N))"
                using val_ring_memE residue_closed to_Zp_closed by blast
              then have "x \<in> G (to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N))"
                unfolding G_def using A by (smt A0 mem_Collect_eq restrict_apply')
              then show "x \<in> \<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
                using 3 by blast
            qed
            show "\<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N)))) \<subseteq> F s"
              unfolding G_def by (smt UN_iff mem_Collect_eq restrict_apply' subsetI)
        qed
        have 0: "\<And>t. t \<in> carrier (Zp_res_ring (e+3*N)) \<Longrightarrow> is_semialgebraic (m+k) (G t)"
        proof- fix t assume A0: "t \<in> carrier (Zp_res_ring (e+3*N))"
          have 0: "\<And>y x. y \<in> G t \<Longrightarrow> x \<in> G t \<Longrightarrow> val (\<xi> (take m y) \<ominus> c y) = val (\<xi> (take m x) \<ominus> c x)"
          proof-
              fix x y assume A1: "y \<in> G t" "x \<in> G t"
              then have 0: "y \<in> F s"
                using A0 G_partitions by blast 
              have 1: "x \<in> F s"
                using A0 G_partitions A1 by blast 
              have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using 0 Fs_closed by blast
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using 1 Fs_closed 
                by blast
              have y_in_S1: "y \<in> S1"
                using 0 A unfolding F_def using "0" F_partitions by blast
              have x_in_S1: "x \<in> S1"
                using A 1 unfolding F_def using "1" F_partitions by blast
              show "val (\<xi> (take m y) \<ominus> c y) = val (\<xi> (take m x) \<ominus> c x)"
                apply(rule fact_3[of _ _ N n])
                using le_add1 local.take_closed y_closed apply blast
                 using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2)
                      padic_fields_axioms y_closed apply blast
                  using N_def apply blast
                   using y_in_S1 unfolding S1_def  apply blast                
                    using y_in_S1 unfolding S1_def  apply blast
                     using le_add1 local.take_closed x_closed apply blast
                      using x_closed Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms apply blast
                       using N_def apply blast 
                        using x_in_S1 unfolding S1_def  apply blast                
                         using x_in_S1 unfolding S1_def  apply blast
                          using 0 1 A unfolding F_def apply (smt IntE mem_Collect_eq restrict_apply')
                           using A1 unfolding G_def 
                            apply (smt A0 mem_Collect_eq restrict_apply')
                             using assms N_def apply blast 
                              using assms n_def by blast 
          qed
          obtain \<alpha> where alpha_def: "\<And>y. y \<in> G t \<Longrightarrow> val (\<xi> (take m y) \<ominus> c y) = \<alpha>"
            using 0 by blast
          show "is_semialgebraic (m + k) (G t)"
          proof(cases "\<alpha> < e + N")
            case True
            obtain G0 where G0_def: "G0 = {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t}"
              by blast 
            obtain G1 where G1_def: "G1 = {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s}"
              by blast 
            obtain G2 where G2_def: "G2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). - N < val (c x)}"
              by blast 
            obtain G3 where G3_def: "G3 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). \<alpha> \<le> val (a x)}"
              by blast 
            obtain G4 where G4_def: "G4 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) = \<alpha>}"
              by blast 
         (* obtain G5 where G5_def: "G5 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < e + N}"
              by blast *)
            have P0:"- eint (int N) = eint (- int N)" 
              by (metis eint.simps(4) uminus_eint_def)                      
            have P1:" is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}"
              using pre_denef_lemma_2_3_0[of c k t N] assms(1) A0  
              unfolding add.commute[of k m] P0 G2_def G0_def by blast 
            have P2: "G0 \<inter> G2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t}"
              unfolding add.commute[of k m] G0_def G2_def by blast  
            have G0_SA: "is_semialgebraic (m+k) (G0 \<inter> G2)"
              using P1 unfolding P2 by blast  
            have G1_SA: "is_semialgebraic (m+k) G1"
              using pre_denef_lemma_2_3_1 unfolding G1_def 
              using N_def A assms(1) S_def by blast
            have G2_SA: "is_semialgebraic (m+k) G2"
              using pre_denef_lemma_2_3_2 unfolding G2_def 
              using assms(1) by blast
            have G3_SA: "is_semialgebraic (m+k) G3"
              using pre_denef_lemma_2_3_3 unfolding G3_def 
              using assms(1) assms(2) by blast              
            have G4_SA: "is_semialgebraic (m+k) G4"
              using pre_denef_lemma_2_3_4 unfolding G4_def 
              using True N_def assms(1) assms(2) by blast
         (* have G5_SA: "is_semialgebraic (m+k) G5"
              using pre_denef_lemma_2_3_5 unfolding G5_def 
              using assms(1) assms(2) by blast *)
            have "G t = G0 \<inter> G1 \<inter> G2 \<inter> G3 \<inter> G4"
            proof
              show "G t \<subseteq> G0 \<inter> G1 \<inter> G2 \<inter> G3 \<inter> G4"
              proof fix x assume A1: "x \<in> G t"
              then have 0: "x \<in> G0"
                unfolding G0_def G_def 
                by (smt A0 Fs_closed add.commute mem_Collect_eq restrict_apply' subset_iff)
              have 1: "x \<in> G1"
              proof-
                have 10: "x \<in> F s"
                  using A1 A0 G_partitions by blast
                hence "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + 2 * N) = s}"
                  using A unfolding F_def 
                  by (smt IntE mem_Collect_eq restrict_apply')
                then show ?thesis 
                  unfolding G1_def using Fs_closed 10 0 G0_def by blast
              qed
              have 2: "x \<in> S1"
                using A G_partitions A A1 A0  F_partitions by blast
              have 3: "x \<in> G2"
                using 2 unfolding G2_def S1_def by blast 
              have 4: "x \<in> G3"
              proof-
                have 30: "val (\<xi> (take m x) \<ominus> c x) = \<alpha>"
                  using alpha_def A1 by blast 
                have 31: "val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)"
                  using 2 assms S_def unfolding S1_def by blast 
                then show ?thesis using 30 unfolding G3_def 
                  using "0" G0_SA is_semialgebraic_closed unfolding G0_def 
                  using "1" G1_SA by blast                  
              qed
              have 5: "x \<in> G4"
                unfolding G4_def using A1 alpha_def 0 G0_SA is_semialgebraic_closed 
                using "1" G1_SA by blast
              show "x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G3 \<inter> G4 " using 0 1 3 4 5 by blast
              qed
              show "G0 \<inter> G1 \<inter> G2 \<inter> G3 \<inter> G4  \<subseteq> G t"
              proof fix x assume A1: "x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G3 \<inter> G4"
                then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)"
                unfolding G0_def by blast 
               have 0: " to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t"
                 using A1 unfolding G0_def by blast 
               have 1: "eint (- int N) < val (c x)"
                 using A1 unfolding G2_def by blast 
               have 2: "val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)"
                 using A1 alpha_def unfolding G3_def using G4_def by blast
               have 3: "val (\<xi> (take m x) \<ominus> c x) = \<alpha>"
                 using A1 unfolding G4_def by blast
               have 4: "x \<in> S"
                 using S_def x_closed 2  by (metis (no_types, lifting) add.commute mem_Collect_eq)
               have 5: "x \<in> S1"
                 using 3 4 x_closed 1 True alpha_def unfolding S1_def 
                 using A1  by (metis (no_types, lifting) Int_Collect add.commute)                
               have 6: "x \<in> F s"
                 using 4 A A0 A1 unfolding F_def G1_def 
                 by (metis (no_types, lifting) "5" Groups.add_ac(2) IntE IntI Int_Collect restrict_apply')
               show "x \<in> G t"
                 unfolding G_def using A A0 A1 unfolding G0_def 
                 by (smt "0" "6" mem_Collect_eq restrict_apply')
             qed
            qed
            then show ?thesis using G0_SA G1_SA G2_SA G3_SA G4_SA 
              intersection_is_semialg by (smt inf_assoc inf_left_commute)             
          next
            case False
            have "G t \<subseteq> F s"
              using A0 G_partitions by blast
            then have "G t \<subseteq> S1"
              using A F_partitions by blast
            hence "\<And>x. x \<in> G t \<Longrightarrow> val (\<xi> (take m x) \<ominus> c x) < e + N"
              unfolding S1_def by blast
            hence "G t = {}"
              using False alpha_def by blast            
            then show ?thesis 
              by (simp add: empty_is_semialgebraic)
          qed
        qed
        then have 1: "G ` carrier (residue_ring (p ^ (e + 3 * N))) \<subseteq> semialg_sets (m + k)"
          by (smt imageE is_semialgebraicE subsetI)
        have 2: "finite (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
          using residue_ring_card by blast 
        then show "is_semialgebraic (m + k) (F s)"
          using 1 2 G_partitions finite_union_is_semialgebraic[of "G ` carrier (residue_ring (p ^ (e + 3 * N)))" "m+k"] 
          by presburger
      qed
    qed
    have 1: "finite (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
      using residue_ring_card by blast 
    have 2: "F ` carrier (residue_ring (p ^ (e + 2 * N))) \<subseteq> semialg_sets (m + k)"
      using 0 by (smt imageE is_semialgebraic_def subsetI)
    show "is_semialgebraic (m + k) S1"
      using finite_union_is_semialgebraic[of "F `(carrier (Zp_res_ring (e+2*N)))" "m+k"] 1 2 F_partitions by blast
  qed
  have S2_semialg: "is_semialgebraic (m+k) S2"
  proof-
    obtain F where F_def: "F = (\<lambda> s \<in> carrier (Zp_res_ring (e+N)). {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+N) = s} \<inter> S2)"
      by blast 
    have F_partitions: "S2 = \<Union> (F `(carrier (Zp_res_ring (e+N))))"
    proof 
      show "S2 \<subseteq> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
      proof fix x assume A: "x \<in> S2"
        then have "\<xi> (take m x) \<in> \<O>\<^sub>p"
          using DL_2_3_5 unfolding S2_def 
          by (metis (no_types, lifting) Int_Collect PiE le_add1 local.take_closed)
        then have "to_Zp (\<xi> (take m x)) (e+N) \<in> carrier (Zp_res_ring (e+N))"
          using val_ring_memE residue_closed to_Zp_closed by blast
        then have "to_Zp (\<xi> (take m x)) (e+N) \<in> carrier (Zp_res_ring (e+N)) \<and> x \<in> F (to_Zp (\<xi> (take m x)) (e+N))"
          using A unfolding F_def S2_def 
          by (smt IntI Int_Collect mem_Collect_eq restrict_apply')
        then show "x \<in> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
          by blast
      qed
      show "\<Union> (F ` carrier (residue_ring (p ^ (e + N)))) \<subseteq> S2"
        unfolding F_def 
        by (smt IntE UN_iff restrict_apply' subsetI)        
    qed
    have 0:"\<And>s. s \<in> carrier (Zp_res_ring (e+N)) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
    proof- fix s assume A: "s \<in> carrier (Zp_res_ring (e+N))"
      show "is_semialgebraic (m+k) (F s)"
      proof(cases "F s = {}")
        case True
        then show ?thesis 
          by (simp add: empty_is_semialgebraic)        
      next
        case False
        have Fs_closed: "F s \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using A unfolding F_def 
          by (smt IntE mem_Collect_eq restrict_apply' subsetI)  
        have Fs_formula: "F s = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<inter>
        (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)})"
          unfolding F_def S2_def by (meson A restrict_apply')
        obtain G where G_def: "G = SA_poly_to_SA_fun m g"
          by blast 
        obtain G' where G'_def: "G' = SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g)"
          by blast 
        have G_closed: "G \<in> carrier (SA (Suc m ))"
          unfolding G_def using SA_poly_to_SA_fun_is_SA[of g m] DL_2_3_10 DL_2_3_3 SA_is_UP_cring[of m] 
          by blast
        have G'_closed: "G' \<in> carrier (SA (Suc m ))"
          unfolding G'_def using SA_poly_to_SA_fun_is_SA[of   "UP_cring.pderiv (SA m) g"] UP_cring.pderiv_closed[of "SA m"]
          using DL_2_3_10 DL_2_3_3 SA_is_UP_cring by blast
        have G_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> G (c x # (take m x)) = UPQ.to_fun (SA_poly_to_Qp_poly m (take m x) g) (c x)"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          then have cx_closed: "c x \<in> carrier Q\<^sub>p"
            using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms by blast
          thus "G (c x # (take m x)) = UPQ.to_fun (SA_poly_to_Qp_poly m (take m x) g) (c x)"
            unfolding G_def using SA_poly_to_SA_fun_formula[of  g] A 
            using DL_2_3_10 DL_2_3_3 le_add1 local.take_closed by blast
        qed
        have G'_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> G' (c x # (take m x)) = UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x)"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          then have cx_closed: "c x \<in> carrier Q\<^sub>p"
            using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms by blast
          thus "G' (c x # take m x) = UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x) "
            unfolding G'_def using SA_poly_to_SA_fun_formula[of  "UP_cring.pderiv (SA m) g"] A 
           by (metis DL_2_3_10 DL_2_3_3 SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_comm_pderiv UPQ.pderiv_eval_deriv UP_cring.pderiv_closed le_add1 local.take_closed padic_fields.SA_is_UP_cring padic_fields_axioms)
        qed
        obtain Nz where Nz_def: "Nz = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) \<noteq> \<zero>}"
          by blast 
        have 0: "is_semialg_map (m+k) (Suc m) (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x) )"
          using semialg_map_cons[of "m + k" m "take m"] take_is_semialg_map[of m "m+k"] 
                DL_2_3_10 assms(1) le_add1 by blast
        have 1: "is_semialg_function (m+k) (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
          using semialg_function_comp_closed[of "Suc m" G'  "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G'_closed assms 0 SA_imp_semialg  DL_2_3_10 by blast
        hence  2: "restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
          using restrict_in_SA_car by blast
        have 3: "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = \<zero>}"
          using 2 semialg_level_set_is_semialg[of  "restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))" "m+k" \<zero>] 
                DL_2_3_10 by blast
        have 4: " {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = \<zero>} = 
                      {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          unfolding restrict_def comp_def by (smt Collect_cong)
        hence 5: "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          using 3 by presburger
        have 6: "Nz = carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          unfolding Nz_def by blast
        hence Nz_semialg: "is_semialgebraic (m+k) Nz"
          by (metis (no_types, lifting) "3" "4" complement_is_semialg)
        have 7: "F s \<subseteq> Nz"
        proof fix x assume A0: "x \<in> F s"
          then have 70: "x \<in> S2"
          unfolding F_def using A A0 Fs_formula S2_def by blast
          have 71: "(UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x)) \<noteq> \<zero>"
            apply(rule fact_4[of _ "\<xi> (take m x)" _ N n])
            using A0 Fs_closed le_add1 local.take_closed apply blast
            using 70 unfolding S2_def apply blast 
             using N_def apply blast 
              using 70 unfolding S2_def apply blast 
                using N_def apply blast 
                using n_def by blast
          then show "x \<in> Nz" unfolding Nz_def using G'_def G'_eval SA_poly_to_SA_fun_formula  
            using A0 Fs_closed by blast
        qed
        obtain T where T_def: "T = fun_glue (m+k) Nz (restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))) \<one>\<^bsub>SA (m+k)\<^esub>"
          by blast 
        have T_closed: "T \<in> carrier (SA (m+k))"
        proof-
          have " \<one>\<^bsub>SA (m + k)\<^esub> \<in> carrier (SA (m + k))"
            using assms SA_is_cring cring.cring_simprules(6) 
            by (metis (no_types, lifting) DL_2_3_10 add_pos_nonneg)            
          thus ?thesis 
            unfolding T_def using assms fun_glue_closed[of _ _  "\<one>\<^bsub>SA (m+k)\<^esub>" Nz] Nz_semialg 2  DL_2_3_10 
            by blast            
        qed
        have Nz_closed: "Nz \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using 6 by blast 
        have T_eval: "\<And>x. x \<in> Nz \<Longrightarrow> T x =  G' (c x # (take m x))"
          using assms SA_is_cring[of "m+k"] cring.cring_simprules(6)[of "SA (m+k)"] Nz_closed
                fun_glueE[of "(restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)))" "m+k" "\<one>\<^bsub>SA (m+k)\<^esub>" Nz] 6 2 
          unfolding T_def restrict_def DL_2_3_10 add_pos_pos o_apply subsetD
          by (smt DL_2_3_10 add_gr_0 subsetD)
        have T_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> T x \<noteq>  \<zero>"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          show "T x \<noteq> \<zero>"
            apply(cases "x \<in> Nz") 
            using T_eval unfolding Nz_def  apply blast
            unfolding T_def using fun_glueE' 
            by (smt A function_one_eval Nz_def SA_one fun_glue_def local.one_neq_zero restrict_apply')
        qed
        have T_unit: "T \<in> Units (SA (m+k))"
          using T_closed T_nonzero  SA_Units_memI assms(1) DL_2_3_10 by blast          
        have T_eval_on_Fs: "\<And>x. x \<in> F s \<Longrightarrow> T x = G' (c x # (take m x))"
          using T_eval 7 by blast
        obtain T0 where T0_def: "T0 =  \<ominus>\<^bsub>SA (m+k)\<^esub> ((restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))))"
          by blast 
        have T0_closed: "T0 \<in> carrier (SA (m+k))"
        proof-
          have 1: "is_semialg_function (m+k) (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
            using semialg_function_comp_closed[of "Suc m" G "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G_closed assms 0 SA_imp_semialg DL_2_3_10  by blast
          hence  2: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
            using restrict_in_SA_car by blast
          thus ?thesis unfolding T0_def using SA_is_ring[of "m+k"] 
           abelian_group.a_inv_closed[of "SA (m+k)"] unfolding ring_def by blast             
        qed
        obtain F0 where F0_def: "F0 =T0 \<otimes>\<^bsub>SA (m+k)\<^esub> inv \<^bsub>SA (m+k)\<^esub>T"
          by blast 
        have F0_closed: "F0 \<in> carrier (SA (m+k))"
          unfolding F0_def using G_closed T0_closed T_unit SA_is_cring 
          by (meson DL_2_3_10 SA_Units_inv_closed cring.cring_simprules(5) trans_less_add1)
        have F0_eval: "\<And>x. x \<in> Nz \<Longrightarrow> F0 x = \<ominus> (G (c x # (take m x))) \<otimes> (inv (G' (c x # (take m x))))"
        proof- fix x assume A: "x \<in> Nz"
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
            using A Nz_closed by blast
          have "(inv\<^bsub>SA (m+k)\<^esub>T) x = inv (T x)"
          proof-
            have "(inv\<^bsub>SA (m+k)\<^esub>T) \<otimes>\<^bsub>SA (m+k)\<^esub>T = \<one>\<^bsub>SA (m+k)\<^esub>"
              by (simp add: DL_2_3_10  T_unit assms(1) padic_fields.SA_Units_memE(2) padic_fields_axioms)
            hence "(inv\<^bsub>SA (m+k)\<^esub>T) x \<otimes> T x = \<one>\<^bsub>SA (m+k)\<^esub> x"
              by (metis Q\<^sub>p_def Zp_def padic_fields.SA_mult padic_fields_axioms x_closed)
            hence "(inv\<^bsub>SA (m+k)\<^esub>T) x \<otimes> T x = \<one>"
              using function_one_eval SA_one x_closed by presburger
            then show ?thesis  
              by (meson DL_2_3_10 Qp.function_ring_car_memE Qp.invI(2) SA_Units_inv_closed SA_car_memE(2) T_closed T_unit trans_less_add1 x_closed)
          qed
          hence 00:"(inv\<^bsub>SA (m+k)\<^esub>T) x = inv (G' (c x # (take m x)))"
            using T_eval[of x] A by presburger
          have 1: "T0 x =  \<ominus> (G (c x # (take m x)))"
          proof-
            have 1: "is_semialg_function (m+k) (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
              using semialg_function_comp_closed[of "Suc m" G "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G_closed assms 0 SA_imp_semialg DL_2_3_10  by blast
            hence 2: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
              using restrict_in_SA_car by blast
            have 3: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = G (c x # (take m x))"
              using x_closed by (metis (no_types, lifting) o_apply restrict_apply')
            thus ?thesis unfolding T0_def using SA_is_cring[of "m+k"] x_closed 2 DL_2_3_10 SA_minus_eval add_gr_0 
              using SA_u_minus_eval by presburger
          qed
          then show "F0 x = \<ominus> (G (c x # (take m x))) \<otimes> (inv (G' (c x # (take m x))))"
            unfolding F0_def using 00 1 Q\<^sub>p_def Zp_def padic_fields.SA_mult padic_fields_axioms x_closed 
            by presburger
        qed
        have 8: "\<And>x. x \<in> Nz \<Longrightarrow> c x \<in> \<O>\<^sub>p \<Longrightarrow> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N) \<Longrightarrow> val (F0 x) = val (\<xi> (take m x) \<ominus> c x)"
        proof- fix x assume A8: "x \<in> Nz" " c x \<in> \<O>\<^sub>p" "to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)"
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
            using A8(1) Nz_closed by blast
          have 80: "F0 x = (\<ominus> (SA_poly_to_Qp_poly m (take m x) g \<bullet> c x) \<div> UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x))"
            using x_closed A8 F0_eval[of x] G'_def G'_eval G_def G_eval by presburger
          have 81: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> \<xi> (take m x) = \<xi> (take m x)"
            using le_add1 local.take_closed x_closed by blast
          have 82: "c x \<in> \<O>\<^sub>p"
            using A8 Fs_formula by blast
          show "val (F0 x) = val (\<xi> (take m x) \<ominus> c x)"
            using A8 80 81 82 fact_4(3)[of "take m x" "\<xi> (take m x)" "c x" N n] N_def n_def
            by presburger
        qed
        have Fs_alt_formula: 
            "F s = Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}
                    \<inter>  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (F0 x) \<le> val (a x)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+N) = s}"
        proof
          show "F s
    \<subseteq> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (F0 x) \<le> val (a x)} \<inter>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
          proof fix x assume A0: "x \<in> F s"
            have 00: "x \<in> Nz"
              using A0 "7" by blast
            have 01: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p}"
              using A0 Fs_formula by blast
            have 02: "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
              using A0 Fs_formula by blast
            have 03: "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (F0 x) \<le> val (a x)}"
            proof-
              have "val (F0 x) = val (\<xi> (take m x) \<ominus> c x)" using 00 01 02 8 by blast 
              then show ?thesis 
                using assms A0 "02" S_def by (metis (no_types, lifting) Fs_formula IntE mem_Collect_eq)
            qed
            show "x \<in> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (F0 x) \<le> val (a x)} \<inter>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
              using 00 01 02 03 A0 Fs_formula by blast
          qed
          show "Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (F0 x) \<le> val (a x)} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}
    \<subseteq> F s"
          proof fix x assume A0: "x \<in> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (F0 x) \<le> val (a x)} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
            then have 00: "c x \<in> \<O>\<^sub>p"
              by blast
            have 01: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
              using A0 by blast 
            have 02: "to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)"
              using A0 by blast 
            have 03: "to_Zp (\<xi> (take m x)) (e + N) = s"
              using A0 by blast
            have 04: "x \<in> Nz"
              using A0 by blast
            have 05: " val (F0 x) = val (\<xi> (take m x) \<ominus> c x)"
              using 8 00 01 02 03 04 by blast
            have 06: "val (\<xi> (take m x) \<ominus> c x)  \<le> val (a x)"
              using A0 05 
              by (metis (no_types, lifting) IntD1 Int_Collect)
            have 07: "x \<in> S"
              unfolding assms S_def using 01 06 by blast 
            have 08: "x \<in> S2"
              unfolding S2_def  using 01 07 03 00 02  by blast
            show " x \<in> F s"
              using Fs_formula  01 02 03 04 05 06 07 08 S2_def by blast
          qed
        qed
        show "is_semialgebraic (m + k) (F s)"
        proof-
          have 00: "is_semialgebraic (m+k)  ({x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)})"
          proof-
            have "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}
               = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
              by blast
            thus ?thesis 
              using N_def assms  xi_res_eq_set_is_semialg by presburger               
          qed
          have 11: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (F0 x) \<le> val (a x)}"
            using semialg_val_ineq_set_is_semialg[of F0 "m+k"  a] assms F0_closed DL_2_3_10 
            by blast
          have 22: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
          proof-
            have 00: "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p"
              by blast
            have 11: "([s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) (e+N) =  s"
              using A 
              by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
            then obtain a where a_def: "a \<in> carrier Z\<^sub>p \<and> a(e+N) = s"
              using 00 by blast 
            have 20: "0 < e + N"
              using assms  N_def by blast
            have 21: " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} = 
                  take m  \<inverse>\<^bsub>m+k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
            proof
              show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<subseteq> take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
                using a_def take_closed by (smt evimageI2 le_add1 mem_Collect_eq subsetI)
              show "take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
                unfolding evimage_def using a_def  by blast
            qed
            thus ?thesis
              using fact_1[of "e+N" a] add_pos_nonneg assms a_def 21 take_is_semialg_map 20 DL_2_3_10 add_pos_pos le_add1 semialg_map_evimage_is_semialg
              by smt              
          qed
          show "is_semialgebraic (m + k) (F s)"
            using 00 11  22  Nz_semialg Fs_alt_formula 
                intersection_is_semialg[of "m+k"]  
            by (metis (no_types, lifting) inf_assoc)
        qed
      qed
    qed
    have Fs_finite: "finite   (F `(carrier (Zp_res_ring (e+N))))"
      using padic_fields.prime padic_fields_axioms padic_integers.residue_ring_card padic_integers_def by blast
    show "is_semialgebraic (m + k) S2"
      using F_partitions 0 Fs_finite finite_union_is_semialgebraic 
      by (meson image_subset_iff is_semialgebraicE)
  qed
  have "is_semialgebraic (m+k) S"
    apply(rule helper_partition_lemma[of c _ _ N], rule assms)
    using S0_semialg S1_semialg S2_semialg S_def
    unfolding S0_def S1_def S2_def by auto 
  thus ?thesis unfolding S_def by auto 
qed


lemma pow_res_inv_im:
  assumes "c \<in> carrier (SA (m+k))"
  assumes "b \<in> carrier Q\<^sub>p" 
  assumes "n > 0"
  shows "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (\<xi> (take m x) \<ominus> c x) \<in>  pow_res n b}"
proof-
  obtain S where S_def: "S = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n b}"
    by blast 
  have trans_closed: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> (\<xi> (take m x) \<ominus> c x) \<in> carrier Q\<^sub>p"
  proof(intro Qp.ring_simprules)
    fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
    have 0: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A take_closed by (simp add: DL_2_3_10 take_closed')
    show "\<xi> (take m x)\<in> carrier Q\<^sub>p"
      apply(intro  Qp.function_ring_car_mem_closed[of \<xi> "carrier (Q\<^sub>p\<^bsup>m\<^esup>)"] 0) 
      using DL_2_3_5 by auto 
    show "c x \<in> carrier Q\<^sub>p"
      by(intro SA_car_closed[of _ "m+k"] A assms)
  qed
  have S_eq: "S =  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (\<xi> (take m x) \<ominus> c x) \<in>  pow_res n b}"
    unfolding S_def 
    by(intro equivalent_pow_res_sets[of _ "(\<lambda> x. (\<xi> (take m x) \<ominus> c x))"] assms trans_closed, auto)
  have mk_pos: "m + k > 0"
    using DL_2_3_10 by simp 
  have n_def: "n > 0"
    using assms by blast 
  obtain N where N_def: "N > 0 \<and> (\<forall> u \<in> carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
    using n_def nth_power_fact' by blast 
  obtain S0 where S0_def: "S0 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
    by blast 
  obtain S1 where S1_def: "S1 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) > -N \<and> val (\<xi> (take m x) \<ominus> c x) < e + N}"
    by blast 
  obtain S2 where S2_def: "S2 = S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). (c x) \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
    by blast 
  have S0_semialg: "is_semialgebraic (m+k) S0" 
  proof-
    have 0: "\<And>x. x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N} \<Longrightarrow>
          val (\<xi> (take m x) \<ominus> c x) = val (\<ominus> (c x)) \<and>  pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n (\<ominus> c x)"
    proof- fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
        using A by blast 
      have takemx_closed: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using le_add1 local.take_closed x_closed by blast
      have 00: "\<xi> (take m x) \<in> \<O>\<^sub>p "
        using takemx_closed DL_2_3_5 by blast
      have  01: "c x \<in> carrier  Q\<^sub>p"
        using x_closed assms Qp.function_ring_car_memE SA_car_memE(2) by blast
      have 02: "val (c x) \<le> -N"
        using A by blast 
      show "val (\<xi> (take m x) \<ominus> c x) = val (\<ominus> (c x))  \<and> pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n (\<ominus> c x)"
        using 00 01 02  N_def n_def  fact_2[of N n "c x" "\<xi> (take m x)"]          
        by blast 
    qed
    have S0_eq: "S0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  pow_res n (\<ominus> c x) = pow_res n b}"
    proof
      show "S0 \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
      proof fix x assume A: "x \<in> S0"
        then have 0: "pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n (\<ominus> c x)"
          unfolding S0_def using 0 by blast
        then show "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
          using A unfolding S_def S0_def assms by blast            
      qed
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b} \<subseteq> S0"
      proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (c x) \<le> eint (- int N)} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
        then have "pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n (\<ominus> c x)"
          using 0  by blast
        then show "x \<in> S0"  
          unfolding S0_def 
          using S_def assms semialg_val_ineq_set_is_semialg semialg_val_ineq_set_is_semialg'
          by (metis (no_types, lifting) A Int_Collect mem_Collect_eq)
      qed
    qed
    have 1: "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  pow_res n (\<ominus> c x) = pow_res n b} = (\<ominus>\<^bsub>SA (m+k)\<^esub> c)  \<inverse>\<^bsub>m+k\<^esub> pow_res n b"
    proof
      show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b} \<subseteq> (\<ominus>\<^bsub>SA (m + k)\<^esub> c) \<inverse>\<^bsub>m+k\<^esub> pow_res n b"
      proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
        have closed: "\<ominus> c x \<in> carrier  Q\<^sub>p "
          using A Qp.function_ring_car_memE SA_car_memE(2) assms(1) by blast
        then have 10: "(\<ominus> c x) \<in> pow_res n b"
          using assms pow_res_refl 
          by (metis (mono_tags, lifting) A mem_Collect_eq)  
        have 11: "(\<ominus>\<^bsub>SA (m+k)\<^esub> c) x = \<ominus> c x"
          using assms A SA_u_minus_eval by blast          
        show "x \<in> (\<ominus>\<^bsub>SA (m + k)\<^esub> c) \<inverse>\<^bsub>m+k\<^esub> pow_res n b"
          using A 10 11 by blast 
      qed
      show "(\<ominus>\<^bsub>SA (m + k)\<^esub> c) \<inverse>\<^bsub>m + k\<^esub> pow_res n b \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
      proof fix x assume A: "x \<in> (\<ominus>\<^bsub>SA (m + k)\<^esub> c) \<inverse>\<^bsub>m + k\<^esub> pow_res n b"
        then have 10: "(\<ominus>\<^bsub>SA (m + k)\<^esub> c) x \<in> pow_res n b"
          by blast
        have 11: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using A unfolding evimage_def by blast 
        have 12: "\<ominus> c x \<in> pow_res n b" using assms 11 10
          by (metis (no_types, lifting) SA_u_minus_eval mk_pos)
        have 13: "pow_res n (\<ominus> c x) = pow_res n b" 
        proof(cases "n = 1")
          case True
          then show ?thesis 
          proof(cases "b \<in> nonzero Q\<^sub>p")
            case T: True
            then have T0: "pow_res n b = nonzero Q\<^sub>p"
              using True pow_res_one by blast
            then have T1: "(\<ominus> c x) \<in> nonzero Q\<^sub>p"
              using 12 by blast
            then show ?thesis using True pow_res_one T0 by blast           
          next
            case False
            then have "b = \<zero>"
              by (meson assms(2) not_nonzero_Qp)
            then have "pow_res n b = {\<zero>}"
              using n_def pow_res_zero by blast
            then have "(\<ominus> c x) = \<zero>"
              using "12" by blast
            then show ?thesis using False 
              using \<open>b = \<zero>\<close> by presburger            
          qed
        next
          case False
          then show ?thesis 
          proof(cases "b \<in> nonzero Q\<^sub>p")
            case True
            then show ?thesis using False 
              by (metis (no_types, opaque_lifting) "12" Qp.nonzero_closed basic_trans_rules(31) n_def nonzero_pow_res equal_pow_resI)
          next
            case False
            then have "pow_res n b = {\<zero>}"
              by (metis assms(2) n_def not_nonzero_Qp pow_res_zero)
            then show ?thesis 
              by (metis "12" n_def pow_res_zero singletonD)            
          qed
        qed
        thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (\<ominus> c x) = pow_res n b}"
          using "11" by blast
      qed    
    qed
    have 2: "is_univ_semialgebraic (pow_res n b)"
      using assms pow_res_is_univ_semialgebraic by blast
    have 3: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (c x) \<le> -N}"
      using assms semialg_val_ineq_set_is_semialg'[of  c "m+k" "-N" ] mk_pos by blast
    have 4: "(\<ominus>\<^bsub>SA (m+k)\<^esub> c) \<in> carrier (SA (m+k))"
      using SA_is_cring 
      by (meson assms(1) cring.cring_simprules(3) mk_pos)
    have 5: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>).  pow_res n (\<ominus> c x) = pow_res n b}"
      using S0_eq 3 4 1 2 evimage_is_semialg by presburger
    show ?thesis 
      using S0_eq 5 3 intersection_is_semialg by blast
  qed
  have S1_semialg: "is_semialgebraic (m+k) S1"
  proof-
    obtain F where F_def: "F = (\<lambda> s \<in> carrier (Zp_res_ring (e+2*N)). {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s} \<inter> S1)"
      by blast 
    have F_partitions: "S1 = \<Union> (F `(carrier (Zp_res_ring (e+2*N))))"
    proof 
      show "S1 \<subseteq> \<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
      proof fix x assume A: "x \<in> S1"
        then have "\<xi> (take m x) \<in> \<O>\<^sub>p"
          using DL_2_3_5 unfolding S1_def 
          by (metis (no_types, lifting) Int_Collect PiE le_add1 local.take_closed)
        then have "to_Zp (\<xi> (take m x)) (e+2*N) \<in> carrier (Zp_res_ring (e+2*N))"
          using val_ring_memE residue_closed to_Zp_closed by blast
        then have "to_Zp (\<xi> (take m x)) (e+2*N) \<in> carrier (Zp_res_ring (e+2*N)) \<and> x \<in> F (to_Zp (\<xi> (take m x)) (e+2*N))"
          using A unfolding F_def S1_def
        proof -
          assume a1: "x \<in> S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c x) \<and> val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))}"
          have "\<forall>i I f. (i::int) \<notin> I \<or> restrict f I i = (f i::((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list set)"
            by (meson restrict_apply')
          then show "to_Zp (\<xi> (take m x)) (e + 2 * N) \<in> carrier (residue_ring (p ^ (e + 2 * N))) \<and> x \<in> (\<lambda>i\<in>carrier (residue_ring (p ^ (e + 2 * N))). {rs \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m rs)) (e + 2 * N) = i} \<inter> (S \<inter> {rs \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). eint (- int N) < val (c rs) \<and> val (\<xi> (take m rs) \<ominus> c rs) < eint (int (e + N))})) (to_Zp (\<xi> (take m x)) (e + 2 * N))"
            using a1 \<open>to_Zp (\<xi> (take m x)) (e + 2 * N) \<in> carrier (residue_ring (p ^ (e + 2 * N)))\<close> by blast
        qed  
        then show "x \<in> \<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
          by blast
      qed
      show "\<Union> (F ` carrier (residue_ring (p ^ (e + 2 * N)))) \<subseteq> S1"
        unfolding F_def 
        by (smt Collect_mem_eq Int_Collect UN_ball_bex_simps(2) image_restrict_eq semiring_normalization_rules(7) subset_iff)
    qed
    have 0:"\<And>s. s \<in> carrier (Zp_res_ring (e+2*N)) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
    proof- fix s assume A: "s \<in> carrier (Zp_res_ring (e+2*N))"
      show "is_semialgebraic (m+k) (F s)"
      proof(cases "F s = {}")
        case True
        then show ?thesis 
          by (simp add: empty_is_semialgebraic)        
      next
        case False
        have Fs_closed: "F s \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using A unfolding F_def 
          by (smt IntE mem_Collect_eq restrict_apply' subsetI)            
        obtain G where G_def: "G = (\<lambda> t \<in> carrier (Zp_res_ring (e + 3*N)). {x \<in> F s. to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t})"
          by blast 
        have G_partitions: "F s = \<Union> (G ` (carrier (Zp_res_ring (e + 3*N))))"
        proof 
            show "F s \<subseteq> \<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
            proof fix x assume A0: "x \<in> F s"
              then have "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using Fs_closed by blast 
              have "x \<in> S1" using A0 A unfolding F_def 
                by (metis (no_types, lifting) IntE restrict_apply')
              then have 0: "val (c x) \<ge> eint (-N)"
                by (metis (no_types, lifting) Int_Collect S1_def le_cases linorder_not_less)
              have cx_closed: "c x \<in> carrier Q\<^sub>p"
                by (metis (no_types, lifting) Int_Collect Q\<^sub>p_def Qp.function_ring_car_memE 
                    S1_def Zp_def \<open>x \<in> S1\<close> assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms)
              have 1: "val (\<pp>[^]N \<otimes> c x) \<ge> N + eint (-N)"
                using DL_2_3_5 Fs_closed cx_closed 0 val_mult[of "\<pp>[^]N" "c x"]
                by (metis eint_add_left_cancel_less linorder_not_less ord_p_pow_nat p_natpow_closed(1) p_natpow_closed(2) val_ord)  
              then have 2: "\<pp>[^]N \<otimes> c x \<in> \<O>\<^sub>p"
                by (metis Qp.int_inc_closed Qp.int_nat_pow_rep Qp.m_closed cx_closed p_intpow_closed(1)
                    p_intpow_inv' times_p_pow_val val_one val_p_int_pow val_ringI)
              then have 3: "to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) \<in> carrier (Zp_res_ring (e+3*N))"
                using val_ring_memE residue_closed to_Zp_closed by blast
              then have "x \<in> G (to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N))"
                unfolding G_def using A by (smt A0 mem_Collect_eq restrict_apply')
              then show "x \<in> \<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
                using 3 by blast
            qed
            show "\<Union> (G ` carrier (residue_ring (p ^ (e + 3 * N)))) \<subseteq> F s"
              unfolding G_def by (smt UN_iff mem_Collect_eq restrict_apply' subsetI)
        qed
        have 0: "\<And>t. t \<in> carrier (Zp_res_ring (e+3*N)) \<Longrightarrow> is_semialgebraic (m+k) (G t)"
        proof- fix t assume A0: "t \<in> carrier (Zp_res_ring (e+3*N))"
          have 0: "\<And>y x. y \<in> G t \<Longrightarrow> x \<in> G t \<Longrightarrow>val (\<xi> (take m y) \<ominus> c y) = val (\<xi> (take m x) \<ominus> c x) \<and>
                                   pow_res n (\<xi> (take m y) \<ominus> c y) = pow_res n (\<xi> (take m x) \<ominus> c x)"
          proof-
              fix x y assume A1: "y \<in> G t" "x \<in> G t"
              then have 0: "y \<in> F s"
                using A0 G_partitions by blast 
              have 1: "x \<in> F s"
                using A0 G_partitions A1 by blast 
              have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using 0 Fs_closed by blast
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                using 1 Fs_closed 
                by blast
              have y_in_S1: "y \<in> S1"
                using 0 A unfolding F_def using "0" F_partitions by blast
              have x_in_S1: "x \<in> S1"
                using A 1 unfolding F_def using "1" F_partitions by blast
              have 2: "(pow_res n (\<xi> (take m y) \<ominus> c y) = pow_res n (\<xi> (take m x) \<ominus> c x))"
                apply(rule fact_3[of _ _ N n])
                using le_add1 local.take_closed y_closed apply blast
                 using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2)
                      padic_fields_axioms y_closed apply blast
                  using N_def apply blast
                   using y_in_S1 unfolding S1_def  apply blast                
                    using y_in_S1 unfolding S1_def  apply blast
                     using le_add1 local.take_closed x_closed apply blast
                      using x_closed Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms apply blast
                       using N_def apply blast 
                        using x_in_S1 unfolding S1_def  apply blast                
                         using x_in_S1 unfolding S1_def  apply blast
                          using 0 1 A unfolding F_def apply (smt IntE mem_Collect_eq restrict_apply')
                           using A1 unfolding G_def 
                            apply (smt A0 mem_Collect_eq restrict_apply')
                             using assms N_def apply blast 
                             using assms n_def by blast

               have 3: "(val (\<xi> (take m y) \<ominus> c y) = val (\<xi> (take m x) \<ominus> c x))"                apply(rule fact_3[of _ _ N n])
                using le_add1 local.take_closed y_closed apply blast
                 using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2)
                      padic_fields_axioms y_closed apply blast
                  using N_def apply blast
                   using y_in_S1 unfolding S1_def  apply blast                
                    using y_in_S1 unfolding S1_def  apply blast
                     using le_add1 local.take_closed x_closed apply blast
                      using x_closed Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms apply blast
                       using N_def apply blast 
                        using x_in_S1 unfolding S1_def  apply blast                
                         using x_in_S1 unfolding S1_def  apply blast
                          using 0 1 A unfolding F_def apply (smt IntE mem_Collect_eq restrict_apply')
                           using A1 unfolding G_def 
                            apply (smt A0 mem_Collect_eq restrict_apply')
                             using assms N_def apply blast 
                             using assms n_def by blast
         show "val (\<xi> (take m y) \<ominus> c y) = val (\<xi> (take m x) \<ominus> c x) \<and>
                                   pow_res n (\<xi> (take m y) \<ominus> c y) = pow_res n (\<xi> (take m x) \<ominus> c x)"
           using 2 3 by blast 
          qed
          obtain a where a_def: "\<And>y. y \<in> G t \<Longrightarrow> pow_res n (\<xi> (take m y) \<ominus> c y) = a"
            using 0 by meson
          obtain \<alpha> where alpha_def: "\<And>y. y \<in> G t \<Longrightarrow> val (\<xi> (take m y) \<ominus> c y) = \<alpha>"
            using 0 by meson
          show "is_semialgebraic (m + k) (G t)"
          proof(cases "\<alpha> < e + N")
            case True
            obtain G0 where G0_def: "G0 = {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<pp>[^]N \<otimes> c x) (e+3*N) = t}"
              by blast 
            obtain G1 where G1_def: "G1 = {x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>). to_Zp (\<xi> (take m x) ) (e+2*N) = s}"
              by blast 
            obtain G2 where G2_def: "G2 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). - N < val (c x)}"
              by blast 
            obtain G5 where G5_def: "G5 = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). val (\<xi> (take m x) \<ominus> c x) < e + N}"
              by blast 
            have G0_SA: "is_semialgebraic (m+k) (G0 \<inter>G2)"
            proof-
              have 00:"- eint N = eint (- N)"
                using Q\<^sub>p_def Zp_def padic_fields.val_p_int_pow padic_fields_axioms val_p_int_pow_neg by presburger
              have " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). - eint (int N) < val (c x) \<and> to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t} = 
                  G0 \<inter> G2"
                unfolding 00 add.commute[of k m] G0_def G2_def by blast 
              thus ?thesis using 00 pre_denef_lemma_2_3_0[of c k t N] assms A0
                unfolding add.commute[of k m] using le0 by metis 
            qed 
            have G1_SA: "is_semialgebraic (m+k) G1"
              using pre_denef_lemma_2_3_1 unfolding G1_def 
              using A mk_pos assms(1) N_def by blast
            have G2_SA: "is_semialgebraic (m+k) G2"
              using pre_denef_lemma_2_3_2 unfolding G2_def 
              using mk_pos assms(1) by blast
            have G5_SA: "is_semialgebraic (m+k) G5"
              using pre_denef_lemma_2_3_5 unfolding G5_def 
              using mk_pos assms(1) by blast
            show ?thesis 
            proof(cases "G t =  {}")
              case True
              then show ?thesis 
                by (simp add: empty_is_semialgebraic)
            next
              case False
              have "G t = G0 \<inter> G1 \<inter> G2 \<inter> G5"
              proof
                show C0:"G t \<subseteq> G0 \<inter> G1 \<inter> G2 \<inter> G5"
                proof fix x assume A1: "x \<in> G t"
                  then have 0: "x \<in> G0"
                    unfolding G0_def G_def 
                    by (smt A0 Fs_closed add.commute mem_Collect_eq restrict_apply' subset_iff)
                  have 1: "x \<in> G1"
                  proof-
                    have 10: "x \<in> F s"
                      using A1 A0 G_partitions by blast
                    hence "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + 2 * N) = s}"
                      using A unfolding F_def 
                      by (smt IntE mem_Collect_eq restrict_apply')
                    then show ?thesis 
                      unfolding G1_def using Fs_closed 10 0 G0_def by blast
                  qed
                  have 2: "x \<in> S1"
                    using A G_partitions A A1 A0  F_partitions by blast
                  have 3: "x \<in> G2"
                    using 2 unfolding G2_def S1_def by blast 
                  have 6: "x \<in> G5"
                    unfolding G5_def using G_partitions S1_def A0 A A1 alpha_def 0 G0_SA is_semialgebraic_closed 2 by blast
                  show "x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5" using 0 1 3 6 by blast
                qed
                show "G0 \<inter> G1 \<inter> G2 \<inter> G5 \<subseteq> G t"
                proof fix x assume A1: "x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5"
                  then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>k+m\<^esup>)"
                    unfolding G0_def by blast 
                  have 0: " to_Zp (\<pp> [^] N \<otimes> c x) (e + 3 * N) = t"
                    using A1 unfolding G0_def by blast 
                  have 00: "to_Zp (\<xi> (take m x)) (e + 2 * N) = s"
                    using A1 unfolding G1_def by blast 
                  have 1: "eint (- int N) < val (c x)"
                    using A1 unfolding G2_def by blast 
                  have 2: "val (\<xi> (take m x) \<ominus> c x) < e + N"
                    using A1 unfolding G5_def by blast 
                  have 3: "\<And>y x. y \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5 \<Longrightarrow> x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5 \<Longrightarrow>pow_res n (\<xi> (take m y) \<ominus> c y) = pow_res n (\<xi> (take m x) \<ominus> c x)"
                  proof-
                    fix x y assume A1: "y \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5" "x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5"
                    have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                      using A1 G5_def by blast
                    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                      using A1 G5_def by blast
                    have 30: "eint (- int N) < val (c x)"
                      using A1 unfolding G2_def by blast  
                    have 31: "eint (- int N) < val (c y)"
                      using 0 A1 unfolding G2_def by blast  
                    have 32: "val (\<xi> (take m y) \<ominus> c y) < eint (int (e + N))"
                      using A1 unfolding G5_def by blast  
                    have 33: "val (\<xi> (take m x) \<ominus> c x) < eint (int (e + N))"
                      using A1 unfolding G5_def by blast  
                    show "(pow_res n (\<xi> (take m y) \<ominus> c y) = pow_res n (\<xi> (take m x) \<ominus> c x))"
                      apply(rule fact_3[of _ _ N n])
                      using le_add1 local.take_closed y_closed apply blast
                      using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2)
                      padic_fields_axioms y_closed apply blast
                      using N_def apply blast
                      using 31 apply blast 
                      using 32 apply blast 
                      using x_closed le_add1 local.take_closed apply blast
                      using Qp.function_ring_car_memE SA_car_memE(2) assms(1) x_closed apply blast
                      using N_def apply blast
                      using "30" apply blast
                      using "33" apply blast
                      using A1 unfolding G1_def apply (metis (mono_tags, lifting) IntD1 Int_Collect)
                      using A1 unfolding G0_def apply (metis (mono_tags, lifting) Int_iff mem_Collect_eq)
                      using N_def apply blast 
                      using assms by blast 
                  qed   
                  obtain w where w_def: "w \<in> G t"
                    using False by blast 
                  then have w_in: "w \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5"
                    using C0 by blast 
                  have "w \<in> S"
                    using w_def A A0 F_partitions G_partitions S1_def by blast
                  hence "pow_res n (\<xi> (take m w) \<ominus> c w) = pow_res n b"
                    unfolding assms S_def by blast
                  hence 4: "\<And>x. x \<in> G0 \<inter> G1 \<inter> G2 \<inter> G5 \<Longrightarrow>pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n b"
                    using 3[of w] w_in by blast 
                  hence "G0 \<inter> G1 \<inter> G2 \<inter> G5  \<subseteq> S"
                    using assms S_def unfolding G1_def   
                    by (smt G5_SA IntE is_semialgebraic_closed mem_Collect_eq subsetD subsetI)
                  have "x \<in> S"
                    using 4 A1 x_closed unfolding assms using \<open>G0 \<inter> G1 \<inter> G2 \<inter> G5 \<subseteq> S\<close> assms(3) by blast
                  hence "x \<in>  S1"
                    unfolding S1_def using A1 unfolding G2_def G5_def 
                    by blast
                  hence "x \<in> F s"
                    using A1 unfolding F_def G1_def 
                    by (smt "00" A IntI add.commute mem_Collect_eq restrict_apply' x_closed)                    
                  thus "x \<in> G t"
                    using A1 unfolding G_def G0_def 
                    by (smt "0" A0 mem_Collect_eq restrict_apply')
                qed
              qed
              thus " is_semialgebraic (m + k) (G t)"
                using G0_SA G1_SA G2_SA G5_SA 
                by (metis (full_types) inf_assoc inf_left_commute intersection_is_semialg)                
            qed
          next
            case False
            have "G t \<subseteq> F s"
              using A0 G_partitions by blast
            then have "G t \<subseteq> S1"
              using A F_partitions by blast
            hence "\<And>x. x \<in> G t \<Longrightarrow> val (\<xi> (take m x) \<ominus> c x) < e + N"
              unfolding S1_def by blast
            hence "G t = {}"
              using False alpha_def by blast            
            then show ?thesis 
              by (simp add: empty_is_semialgebraic)
          qed
        qed
        have 1: "G ` carrier (residue_ring (p ^ (e + 3 * N))) \<subseteq> semialg_sets (m + k)"
          apply(intro subsetI is_semialgebraicE)
          using 0 by auto  
        have 2: "finite (G ` carrier (residue_ring (p ^ (e + 3 * N))))"
          using residue_ring_card by blast 
        then show "is_semialgebraic (m + k) (F s)"
          using 1 2 G_partitions finite_union_is_semialgebraic[of "G ` carrier (residue_ring (p ^ (e + 3 * N)))" "m+k"] 
          by presburger
      qed
    qed
    have 1: "finite (F ` carrier (residue_ring (p ^ (e + 2 * N))))"
      using residue_ring_card by blast 
    have 2: "F ` carrier (residue_ring (p ^ (e + 2 * N))) \<subseteq> semialg_sets (m + k)"
      using 0 by (smt imageE is_semialgebraic_def subsetI)
    show "is_semialgebraic (m + k) S1"
      using finite_union_is_semialgebraic[of "F `(carrier (Zp_res_ring (e+2*N)))" "m+k"] 1 2 F_partitions by blast
  qed
  have S2_semialg: "is_semialgebraic (m+k) S2"
  proof-
    obtain F where F_def: "F = (\<lambda> s \<in> carrier (Zp_res_ring (e+N)). {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+N) = s} \<inter> S2)"
      by blast 
    have F_partitions: "S2 = \<Union> (F `(carrier (Zp_res_ring (e+N))))"
    proof 
      show "S2 \<subseteq> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
      proof fix x assume A: "x \<in> S2"
        then have "\<xi> (take m x) \<in> \<O>\<^sub>p"
          using DL_2_3_5 unfolding S2_def 
          by (metis (no_types, lifting) Int_Collect PiE le_add1 local.take_closed)
        then have "to_Zp (\<xi> (take m x)) (e+N) \<in> carrier (Zp_res_ring (e+N))"
          using val_ring_memE residue_closed to_Zp_closed by blast
        then have "to_Zp (\<xi> (take m x)) (e+N) \<in> carrier (Zp_res_ring (e+N)) \<and> x \<in> F (to_Zp (\<xi> (take m x)) (e+N))"
          using A unfolding F_def S2_def 
          by (smt IntI Int_Collect mem_Collect_eq restrict_apply')
        then show "x \<in> \<Union> (F ` carrier (residue_ring (p ^ (e + N))))"
          by blast
      qed
      show "\<Union> (F ` carrier (residue_ring (p ^ (e + N)))) \<subseteq> S2"
        unfolding F_def 
        by (smt IntE Union_iff imageE image_restrict_eq subsetI)        
    qed
    have 0:"\<And>s. s \<in> carrier (Zp_res_ring (e+N)) \<Longrightarrow> is_semialgebraic (m+k) (F s)"
    proof- fix s assume A: "s \<in> carrier (Zp_res_ring (e+N))"
      show "is_semialgebraic (m+k) (F s)"
      proof(cases "F s = {}")
        case True
        then show ?thesis 
          by (simp add: empty_is_semialgebraic)        
      next
        case False
        have Fs_closed: "F s \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using A unfolding F_def 
          by (smt IntE mem_Collect_eq restrict_apply' subsetI)  
        have Fs_formula: "F s = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<inter>
        (S \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)})"
          unfolding F_def S2_def by (meson A restrict_apply')
        obtain G where G_def: "G = SA_poly_to_SA_fun m g"
          by blast 
        obtain G' where G'_def: "G' = SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g)"
          by blast 
        have G_closed: "G \<in> carrier (SA (Suc m ))"
          unfolding G_def using SA_poly_to_SA_fun_is_SA[of g m] DL_2_3_10 DL_2_3_3 SA_is_UP_cring[of m] 
          by blast
        have G'_closed: "G' \<in> carrier (SA (Suc m ))"
          unfolding G'_def using SA_poly_to_SA_fun_is_SA[of "UP_cring.pderiv (SA m) g"] UP_cring.pderiv_closed[of "SA m"]
          using DL_2_3_10 DL_2_3_3 SA_is_UP_cring by blast
        have G_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> G (c x # (take m x)) = UPQ.to_fun (SA_poly_to_Qp_poly m (take m x) g) (c x)"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          then have cx_closed: "c x \<in> carrier Q\<^sub>p"
            using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms by blast
          thus "G (c x # (take m x)) = UPQ.to_fun (SA_poly_to_Qp_poly m (take m x) g) (c x)"
            unfolding G_def using SA_poly_to_SA_fun_formula[of g] A 
            using DL_2_3_10 DL_2_3_3 le_add1 local.take_closed by blast
        qed
        have G'_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> G' (c x # (take m x)) = UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x)"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          then have cx_closed: "c x \<in> carrier Q\<^sub>p"
            using Q\<^sub>p_def Qp.function_ring_car_memE Zp_def assms(1) padic_fields.SA_car_memE(2) padic_fields_axioms by blast
          thus "G' (c x # take m x) = UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x) "
            unfolding G'_def using SA_poly_to_SA_fun_formula[of "UP_cring.pderiv (SA m) g"] A 
           by (metis DL_2_3_10 DL_2_3_3 SA_poly_to_Qp_poly_closed SA_poly_to_Qp_poly_comm_pderiv UPQ.pderiv_eval_deriv UP_cring.pderiv_closed le_add1 local.take_closed padic_fields.SA_is_UP_cring padic_fields_axioms)
        qed
        obtain Nz where Nz_def: "Nz = {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) \<noteq> \<zero>}"
          by blast 
        have 0: "is_semialg_map (m+k) (Suc m) (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x) )"
          using semialg_map_cons[of "m + k" m "take m"] take_is_semialg_map[of m "m+k"] 
                DL_2_3_10 assms(1) le_add1 by blast
        have 1: "is_semialg_function (m+k) (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
          using semialg_function_comp_closed[of "Suc m" G'  "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G'_closed assms 0 SA_imp_semialg  DL_2_3_10 by blast
        hence  2: "restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
          using restrict_in_SA_car by blast
        have 3: "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = \<zero>}"
          using 2 semialg_level_set_is_semialg[of "restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))""m+k"  \<zero>] 
                DL_2_3_10 by blast
        have 4: " {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = \<zero>} = 
                      {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          unfolding restrict_def comp_def by (smt Collect_cong)
        hence 5: "is_semialgebraic (m+k)  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          using 3 by presburger
        have 6: "Nz = carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). G' (c x # (take m x)) = \<zero>}"
          unfolding Nz_def by blast
        hence Nz_semialg: "is_semialgebraic (m+k) Nz"
          by (metis (no_types, lifting) "3" "4" complement_is_semialg)
        have 7: "F s \<subseteq> Nz"
        proof fix x assume A0: "x \<in> F s"
          then have 70: "x \<in> S2"
          unfolding F_def using A A0 Fs_formula S2_def by blast
          have 71: "(UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x)) \<noteq> \<zero>"
            apply(rule fact_4[of _ "\<xi> (take m x)" _ N n])
            using A0 Fs_closed le_add1 local.take_closed apply blast
            using 70 unfolding S2_def apply blast 
             using N_def apply blast 
              using 70 unfolding S2_def apply blast 
                using N_def apply blast 
                using n_def by blast
          then show "x \<in> Nz" unfolding Nz_def using G'_def G'_eval SA_poly_to_SA_fun_formula  
            using A0 Fs_closed by blast
        qed
        obtain T where T_def: "T = fun_glue (m+k) Nz (restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))) \<one>\<^bsub>SA (m+k)\<^esub>"
          by blast 
        have T_closed: "T \<in> carrier (SA (m+k))"
        proof-
          have " \<one>\<^bsub>SA (m + k)\<^esub> \<in> carrier (SA (m + k))"
            using assms SA_is_cring cring.cring_simprules(6) mk_pos by (metis (no_types, lifting))                                  
          thus ?thesis 
            unfolding T_def using assms fun_glue_closed[of  _ "m+k" "\<one>\<^bsub>SA (m+k)\<^esub>" Nz] Nz_semialg 2  DL_2_3_10 
            by blast            
        qed
        have Nz_closed: "Nz \<subseteq> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          using 6 by blast 
        have T_eval: "\<And>x. x \<in> Nz \<Longrightarrow> T x =  G' (c x # (take m x))"
          using assms SA_is_cring[of "m+k"] cring.cring_simprules(6)[of "SA (m+k)"] Nz_closed
                fun_glueE[of "(restrict (G' \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)))" "m+k" "\<one>\<^bsub>SA (m+k)\<^esub>" Nz] 6 2 
          unfolding T_def restrict_def DL_2_3_10 add_pos_pos o_apply subsetD
          by (smt DL_2_3_10 add_gr_0 subsetD)
        have T_nonzero: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>) \<Longrightarrow> T x \<noteq>  \<zero>"
        proof- fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
          show "T x \<noteq> \<zero>"
            apply(cases "x \<in> Nz") 
            using T_eval unfolding Nz_def  apply blast
            unfolding T_def using fun_glueE' 
            by (smt A function_one_eval Nz_def SA_one fun_glue_def local.one_neq_zero restrict_apply')
        qed
        have T_unit: "T \<in> Units (SA (m+k))"
          using T_closed T_nonzero  SA_Units_memI mk_pos DL_2_3_10 by blast          
        have T_eval_on_Fs: "\<And>x. x \<in> F s \<Longrightarrow> T x = G' (c x # (take m x))"
          using T_eval 7 by blast
        obtain T0 where T0_def: "T0 =  \<ominus>\<^bsub>SA (m+k)\<^esub> ((restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))))"
          by blast 
        have T0_closed: "T0 \<in> carrier (SA (m+k))"
        proof-
          have 1: "is_semialg_function (m+k) (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
            using semialg_function_comp_closed[of "Suc m" G "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G_closed assms 0 SA_imp_semialg DL_2_3_10  by blast
          hence  2: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
            using restrict_in_SA_car by blast
          thus ?thesis unfolding T0_def using SA_is_cring[of "m+k"] 
            by (meson DL_2_3_10  add_gr_0 cring.cring_simprules(3))
        qed
        obtain F0 where F0_def: "F0 =T0 \<otimes>\<^bsub>SA (m+k)\<^esub> inv \<^bsub>SA (m+k)\<^esub>T"
          by blast 
        have F0_closed: "F0 \<in> carrier (SA (m+k))"
          unfolding F0_def using G_closed T0_closed T_unit SA_is_cring 
          by (meson DL_2_3_10 SA_Units_inv_closed cring.cring_simprules(5) trans_less_add1)
        have F0_eval: "\<And>x. x \<in> Nz \<Longrightarrow> F0 x = \<ominus> (G (c x # (take m x))) \<otimes> (inv (G' (c x # (take m x))))"
        proof- fix x assume A: "x \<in> Nz"
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
            using A Nz_closed by blast
          have "(inv\<^bsub>SA (m+k)\<^esub>T) x = inv (T x)"
          proof-
            have "(inv\<^bsub>SA (m+k)\<^esub>T) \<otimes>\<^bsub>SA (m+k)\<^esub>T = \<one>\<^bsub>SA (m+k)\<^esub>"
              by (simp add: DL_2_3_10  T_unit mk_pos padic_fields.SA_Units_memE(2) padic_fields_axioms)
            hence "(inv\<^bsub>SA (m+k)\<^esub>T) x \<otimes> T x = \<one>\<^bsub>SA (m+k)\<^esub> x"
              by (metis Q\<^sub>p_def Zp_def padic_fields.SA_mult padic_fields_axioms x_closed)
            hence "(inv\<^bsub>SA (m+k)\<^esub>T) x \<otimes> T x = \<one>"
              using function_one_eval SA_one x_closed by presburger
            then show ?thesis  
              by (meson DL_2_3_10 Qp.function_ring_car_memE Qp.invI(2) SA_Units_inv_closed SA_car_memE(2) T_closed T_unit trans_less_add1 x_closed)
          qed
          hence 00:"(inv\<^bsub>SA (m+k)\<^esub>T) x = inv (G' (c x # (take m x)))"
            using T_eval[of x] A by presburger
          have 1: "T0 x =  \<ominus> (G (c x # (take m x)))"
          proof-
            have 1: "is_semialg_function (m+k) (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)))"
              using semialg_function_comp_closed[of "Suc m" G "m+k" "\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x)"]
                G_closed assms 0 SA_imp_semialg DL_2_3_10  by blast
            hence 2: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>))  \<in> carrier (SA (m+k))"
              using restrict_in_SA_car by blast
            have 3: "restrict (G \<circ> (\<lambda>x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x # (take m x))) (carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)) x = G (c x # (take m x))"
              using x_closed by (metis (no_types, lifting) o_apply restrict_apply')
            thus ?thesis unfolding T0_def using SA_is_cring[of "m+k"] x_closed 2 DL_2_3_10 SA_u_minus_eval add_gr_0 
              by presburger
          qed
          then show "F0 x = \<ominus> (G (c x # (take m x))) \<otimes> (inv (G' (c x # (take m x))))"
            unfolding F0_def using 00 1 Q\<^sub>p_def Zp_def padic_fields.SA_mult padic_fields_axioms x_closed 
            by presburger
        qed
        have 8: "\<And>x. x \<in> Nz \<Longrightarrow> c x \<in> \<O>\<^sub>p \<Longrightarrow> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N) \<Longrightarrow> pow_res n (F0 x) = pow_res n (\<xi> (take m x) \<ominus> c x)"
        proof- fix x assume A8: "x \<in> Nz" " c x \<in> \<O>\<^sub>p" "to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)"
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
            using A8(1) Nz_closed by blast
          have 80: "F0 x = (\<ominus> (SA_poly_to_Qp_poly m (take m x) g \<bullet> c x) \<div> UPQ.deriv (SA_poly_to_Qp_poly m (take m x) g) (c x))"
            using x_closed A8 F0_eval[of x] G'_def G'_eval G_def G_eval by presburger
          have 81: "take m x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<and> \<xi> (take m x) = \<xi> (take m x)"
            using le_add1 local.take_closed x_closed by blast
          have 82: "c x \<in> \<O>\<^sub>p"
            using A8 Fs_formula by blast
          show "pow_res n (F0 x) = pow_res n (\<xi> (take m x) \<ominus> c x)"
            using A8 80 81 82 fact_4(2)[of "take m x" "\<xi> (take m x)" "c x" N n] N_def n_def
            by presburger
        qed
        have Fs_alt_formula: 
            "F s = Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}
                    \<inter>  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). pow_res n (F0 x) = pow_res n b} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x) ) (e+N) = s}"
        proof
          show "F s \<subseteq> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} \<inter>
       {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
          proof fix x assume A0: "x \<in> F s"
            have 00: "x \<in> Nz"
              using A0 "7" by blast
            have 01: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p}"
              using A0 Fs_formula by blast
            have 02: "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
              using A0 Fs_formula by blast
            have 03: "x \<in>  {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). pow_res n (F0 x) = pow_res n (\<xi> (take m x) \<ominus> c x)}"
            proof-
              have "pow_res n (F0 x) = pow_res n (\<xi> (take m x) \<ominus> c x)" using 00 01 02 8 by blast 
              then show ?thesis 
                using assms A0 "02" by blast            
            qed
            have "x \<in> S"
              using A0 A unfolding F_def S2_def using A0 Fs_formula by blast
            hence 04: "pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n b"
              unfolding assms S_def by blast              
            show "x \<in> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} \<inter>
              {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
              using 00 01 02 03 A0 Fs_formula "04" by blast             
          qed
          show "Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} \<inter>
    {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}
    \<subseteq> F s"
          proof fix x assume A0: "x \<in> Nz \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} \<inter>
             {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
            then have 00: "c x \<in> \<O>\<^sub>p"
              by blast
            have 01: "x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>)"
              using A0 by blast 
            have 02: "to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)"
              using A0 by blast 
            have 03: "to_Zp (\<xi> (take m x)) (e + N) = s"
              using A0 by blast
            have 04: "x \<in> Nz"
              using A0 by blast
            have 05: "pow_res n (F0 x) = pow_res n (\<xi> (take m x) \<ominus> c x)"
              using 8 00 01 02 03 04 by blast
            have 06: "pow_res n (\<xi> (take m x) \<ominus> c x) = pow_res n b"
              using 05 A0 by blast 
            hence 07: "x \<in> S"
              unfolding assms S_def using 01 05 by blast 
            have 08: "x \<in> S2"
              unfolding S2_def  using 01 07 03 00 02  by blast
            show " x \<in> F s"
              using Fs_formula  01 02 03 04 05 06 07 08 S2_def by blast
          qed
        qed
        show "is_semialgebraic (m + k) (F s)"
        proof-
          have 00: "is_semialgebraic (m+k)  ({x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)})"
          proof-
            have "{x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). c x \<in> \<O>\<^sub>p} \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}
               = {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). c x \<in> \<O>\<^sub>p \<and> to_Zp (\<xi> (take m x)) (e + N) = to_Zp (c x) (e + N)}"
              by blast
            thus ?thesis 
              using xi_res_eq_set_is_semialg[of c k N] N_def assms le0 by presburger              
          qed
          have 11: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b}"
          proof-
            have  "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} = F0  \<inverse>\<^bsub>m+k\<^esub> (pow_res n b)"
            proof show "{x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} \<subseteq> F0 \<inverse>\<^bsub>m + k\<^esub> pow_res n b"
              proof fix x assume A: "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b}"
                then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                  by blast 
                have " pow_res n (F0 x) = pow_res n b"
                  using A by blast 
                hence "F0 x \<in> pow_res n b"
                  using pow_res_refl
                  by (metis F0_closed Qp.function_ring_car_memE SA_car_memE(2) n_def x_closed)
                thus "x \<in> F0 \<inverse>\<^bsub>m + k\<^esub> pow_res n b"
                  using x_closed by blast 
              qed
              show "F0 \<inverse>\<^bsub>m + k\<^esub> pow_res n b \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b}"
              proof fix x assume A: " x \<in> F0 \<inverse>\<^bsub>m + k\<^esub> pow_res n b"
                then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m+k\<^esup>)"
                  by (meson evimage_eq)
                have "F0 x \<in> pow_res n b"
                  using A by blast
                hence "pow_res n (F0 x) = pow_res n b"
                  by (metis F0_closed Qp.function_ring_car_memE SA_car_memE(2) assms(2) n_def not_nonzero_Qp equal_pow_resI pow_res_zero singletonD x_closed)
                thus "x \<in> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). pow_res n (F0 x) = pow_res n b} "
                  using x_closed by blast 
              qed
            qed
            then show ?thesis 
              using F0_closed assms(2) evimage_is_semialg n_def pow_res_is_univ_semialgebraic by presburger
          qed
          have 22: "is_semialgebraic (m+k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
          proof-
            have 00: "[s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub> \<in> carrier Z\<^sub>p"
              by blast
            have 11: "([s]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) (e+N) =  s"
              using A 
              by (metis Zp_int_inc_res mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
            then obtain a where a_def: "a \<in> carrier Z\<^sub>p \<and> a(e+N) = s"
              using 00 by blast 
            have 20: "0 < e + N"
              using assms  N_def by blast
            have 21: " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} = 
                  take m  \<inverse>\<^bsub>m+k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
            proof
              show " {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s} \<subseteq> take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)}"
                using a_def take_closed by (smt evimageI2 le_add1 mem_Collect_eq subsetI)
              show "take m \<inverse>\<^bsub>m + k\<^esub> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (e + N) = a (e + N)} \<subseteq> {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). to_Zp (\<xi> (take m x)) (e + N) = s}"
                unfolding evimage_def using a_def  by blast
            qed
            thus ?thesis
              using mk_pos fact_1[of "e+N" a] add_pos_nonneg assms a_def 21 take_is_semialg_map 20 
                    DL_2_3_10 add_pos_pos le_add1 semialg_map_evimage_is_semialg
              by smt                                 
          qed
          show "is_semialgebraic (m + k) (F s)"
            using 00 11  22  Nz_semialg Fs_alt_formula 
                intersection_is_semialg[of "m+k"]  
            by (metis (no_types, lifting) inf_assoc)
        qed
      qed
    qed
    have Fs_finite: "finite   (F `(carrier (Zp_res_ring (e+N))))"
      using padic_fields.prime padic_fields_axioms padic_integers.residue_ring_card padic_integers_def by blast
    show "is_semialgebraic (m + k) S2"
      using F_partitions 0 Fs_finite finite_union_is_semialgebraic 
      by (meson image_subset_iff is_semialgebraicE)
  qed
  have "is_semialgebraic (m+k) S"
    apply(rule helper_partition_lemma[of c _ _ N], rule assms)
    using S0_semialg S1_semialg S2_semialg S_def
    unfolding S0_def S1_def S2_def by auto 
  thus ?thesis unfolding S_eq by auto 
qed

lemma denef_lemma_2_3:
"\<xi> \<in> carrier (SA m)"
proof(rule SA_fun_test[of _ g]) 
  show "deg (SA m) g \<le> Suc d" 
        "0 < deg (SA m) g" 
        "g \<in> carrier (UP (SA m))"
        "\<xi> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
         "g (deg (SA m) g) \<in> Units (SA m)"
         " \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). SA_poly_to_SA_fun m g (\<xi> x # x) = \<zero>"
    using DL_2_3_7 DL_2_3_1 DL_2_3_2 DL_2_3_3 \<xi>_closed DL_2_3_6 by(auto)
  show "\<And>k c a.
       c \<in> carrier (SA (m + k)) \<Longrightarrow>
       a \<in> carrier (SA (m + k)) \<Longrightarrow>
       is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). val (\<xi> (take m x) \<ominus> c x) \<le> val (a x)}"
    by(rule val_leq_inv_im, auto)
  show "\<And>k c \<alpha> n.
       c \<in> carrier (SA (m + k)) \<Longrightarrow>
       \<alpha> \<in> carrier Q\<^sub>p \<Longrightarrow>
       0 < n \<Longrightarrow> is_semialgebraic (m + k) {x \<in> carrier (Q\<^sub>p\<^bsup>m + k\<^esup>). \<xi> (take m x) \<ominus> c x \<in> pow_res n \<alpha>}"
    by(rule pow_res_inv_im, auto)
qed
    
end

context denef_II
begin

lemma denef_lemma_2_3: 
  assumes  "m > 0"
  assumes "deg (SA m) g \<le> Suc d"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "\<And>j. g j \<in> carrier  (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
  assumes "\<xi> \<in> carrier (Fun\<^bsub>m\<^esub> Q\<^sub>p)"
  assumes "\<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
  assumes "UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<xi> x) (Suc e) = l"
  assumes "\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x#x)) \<le> e"
  shows "\<xi> \<in> carrier (SA m)" 
proof-
    have F1: "deg (SA m) g \<noteq> 0"
    proof assume C: "deg (SA m) g = 0"
      then have C0: "UP_cring.pderiv (SA m) g = \<zero>\<^bsub>UP (SA m)\<^esub>"
        using  assms UP_cring.pderiv_deg_0[of "SA m" g] SA_is_UP_cring by blast
      have "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>  (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x#x)) = \<zero>"
      proof-
        fix x assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        then have A0: "\<xi> x \<in> carrier Q\<^sub>p"
          using assms Qp.function_ring_car_memE by blast
        have A1: " SA_poly_to_Qp_poly m x (UP_cring.pderiv (SA m) g) = \<zero>\<^bsub>Q\<^sub>p_x\<^esub>"
          using assms(2) A SA_poly_to_Qp_poly_is_hom[of x] ring_hom_zero unfolding C0 
          using  UPQ.UP_ring padic_fields.UP_SA_n_is_ring padic_fields_axioms by blast
        have A2: " SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x # x) = \<zero>\<^bsub>Q\<^sub>p_x\<^esub> \<bullet> \<xi> x"
          using SA_poly_to_SA_fun_formula[of "(UP_cring.pderiv (SA m) g)" m x "\<xi> x"] assms A A0 C0
          unfolding A1 by (metis C less_nat_zero_code multivar_poly_factor'') 
        show "SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x # x) = \<zero>"
          unfolding A2 using A0 UPQ.to_fun_zero by blast
      qed
      hence C1: " \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x # x)) = \<infinity>"
        using val_zero by metis 
      hence C2: " \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x # x)) > e"
        by (metis eint_ord_code(4))
      obtain a where a_def: "a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        by (meson Qp_n_nonempty all_not_in_conv)
      then have "val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> a#a)) \<le> e"
        using assms(10) by blast 
      then show False using C1 by (metis a_def infinity_ileE)
    qed 
    show ?thesis
      apply(intro denef_lemma_2_3.denef_lemma_2_3[of p d g \<xi> e l m] 
                  denef_lemma_2_3.intro denef_II_axioms denef_lemma_2_3_axioms.intro)
      using assms apply blast       
      using F1 apply blast 
      using assms apply blast 
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms unfolding Q\<^sub>p_def Zp_def \<iota>_def apply blast
      using assms by blast
qed

text\<open>We can also specialize lemma 2.3 to the cases where $\xi$ is a root of $g$ on only a subset 
      of $\mathbb{Q}_p^m$.\<close>
lemma(in denef_II) denef_lemma_2_3_on_subset: 
  assumes "deg (SA m) g \<le> Suc d"
  assumes "g \<in> carrier (UP (SA m))"
  assumes "is_semialgebraic m B"
  assumes "\<And>j. g j \<in> B \<rightarrow> \<O>\<^sub>p"
  assumes "\<And> x. x \<in> B \<Longrightarrow> \<xi> x \<in> \<O>\<^sub>p"
  assumes "UP_ring.lcf (SA m) g \<in> Units (SA m)"
  assumes "\<forall>x \<in> B. (SA_poly_to_SA_fun m g) (\<xi> x#x) = \<zero>"
  assumes "\<forall>x \<in> B. to_Zp (\<xi> x) (Suc e) = l"
  assumes "\<forall>x \<in> B. val (SA_poly_to_SA_fun m (UP_cring.pderiv (SA m) g) (\<xi> x#x)) \<le> e"
  shows "\<exists> \<eta> \<in> carrier (SA m). \<forall>x \<in> B. \<eta> x = \<xi> x" 
proof(cases "m > 0")
  case m_pos: True
  show ?thesis 
  proof(cases "B = {}")
    case True
    then show ?thesis by blast 
  next
    case False
    then obtain x where x_def: "x \<in> B"
      by blast
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using assms 
      by (meson Set.basic_monos(7) is_semialgebraic_closed x_def)
    have \<xi>_closed: "\<And> x. x \<in> B \<Longrightarrow> \<xi> x \<in> carrier Q\<^sub>p"
      using assms val_ring_memE(2) by presburger
    obtain g0 where g0_def: "g0 = SA_poly_to_Qp_poly m x g"
      by blast 
    have g0_closed: "g0 \<in> carrier Q\<^sub>p_x"
      using g0_def assms x_closed SA_poly_to_Qp_poly_closed by presburger
    obtain g1 where g1_def: "g1 = (\<lambda>n. (g0 n)\<odot>\<^bsub>SA m\<^esub>\<one>\<^bsub>SA m\<^esub>)"
      by blast 
    have g1_closed: "g1 \<in> carrier (UP (SA m))"
    proof(rule UP_car_memI[of "deg Q\<^sub>p g0"])
      show "\<And>n. deg Q\<^sub>p g0 < n \<Longrightarrow> g1 n = \<zero>\<^bsub>SA m\<^esub>"
        unfolding g1_def 
        by (simp add: SA_is_module UPQ.UP_car_memE(2) g0_closed module.smult_l_null)
      show "\<And>n. g1 n \<in> carrier (SA m)"
        unfolding g1_def 
        apply(rule SA_smult_closed, auto)
        by (simp add: UPQ.UP_car_memE(1) g0_closed)
    qed
    have g1_deg_bound: "deg (SA m) g1 \<le> Suc d"
      apply(intro deg_leqI g1_closed)
      unfolding g1_def using assms 
      by (smt (verit) R.cring_simprules(6) SA_is_module SA_poly_to_Qp_poly_coeff
          SA_zero UPSA.deg_leE basic_trans_rules(23) g0_def local.function_zero_eval 
          module.smult_l_null not_less x_closed)    
    obtain h where h_def: "h = SA_poly_glue m B g g1"
      by blast 
    have h_closed: "h \<in> carrier (UP (SA m))"
      unfolding h_def 
      by(intro SA_poly_glue_closed assms g1_closed)
    obtain \<gamma> where \<gamma>_def: "\<gamma> = (\<xi> x) \<odot>\<^bsub>SA m\<^esub> \<one>\<^bsub>SA m\<^esub>"
      by blast 
    have \<gamma>_closed: "\<gamma> \<in> carrier (SA m)"
      by(unfold \<gamma>_def, intro SA_smult_closed  \<xi>_closed x_closed x_def,
            auto)
    obtain \<eta> where \<eta>_def: "\<eta> = fun_glue m B \<xi> \<gamma>"
      by blast 
    have h_deg: "deg (SA m) h \<le> Suc d"
      unfolding h_def 
      apply(intro SA_poly_glue_deg)
      using assms apply blast
         apply (simp add: g1_closed)
      apply (simp add: assms)
       apply (simp add: assms)
      using g1_deg_bound 
      by auto
    have h_cfs1: "\<And> j x. x \<in> B \<Longrightarrow> h j x = g j x"
      unfolding h_def 
      by (simp add: SA_poly_glue_cfs1 assms g1_closed)
    have h_cfs2: "\<And> j x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> x \<notin> B \<Longrightarrow> h j x = g0 j"
      using assms SA_poly_glue_cfs2 unfolding h_def 
      using SA_oneE SA_smult_formula UPQ.cfs_closed g0_closed g1_closed g1_def by force
    have h_cfs2': "\<And> j y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> y \<notin> B \<Longrightarrow> h j y = g j x"
      using assms h_cfs2 unfolding h_def 
      using SA_poly_to_Qp_poly_coeff g0_def x_closed by presburger
    have \<eta>_eval1: "\<And> y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> y \<in> B \<Longrightarrow> \<eta> y = \<xi> y"
      unfolding \<eta>_def  fun_glue_def by simp
    have \<eta>_eval2: "\<And> y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> y \<notin> B \<Longrightarrow> \<eta> y = \<xi> x"
      unfolding \<eta>_def  fun_glue_def 
      by (simp add: SA_oneE SA_smult_formula \<gamma>_def \<xi>_closed x_def)
    have \<eta>_closed: "\<And>a. a \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<eta> a \<in> carrier Q\<^sub>p"
      using \<eta>_eval1 \<eta>_eval2 by (metis \<xi>_closed x_def)
    have \<eta>_function_ring: "\<eta> \<in> carrier (function_ring (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) Q\<^sub>p)"
      apply(intro Qp.function_ring_car_memI \<eta>_closed)
      unfolding \<eta>_def fun_glue_def by auto
    have \<eta>_integral: "\<eta> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
      apply(auto)
      using \<eta>_eval1 \<eta>_eval2 assms x_def by metis
    have \<eta>_res: " \<forall>x\<in>carrier (Q\<^sub>p\<^bsup>m\<^esup>). to_Zp (\<eta> x) (Suc e) = l"
      using \<eta>_eval1 \<eta>_eval2 assms x_def by metis
    have to_Qp_h1: "\<And> y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)  \<Longrightarrow> y \<in> B 
                              \<Longrightarrow> SA_poly_to_Qp_poly m y h = SA_poly_to_Qp_poly m y g"
      by (simp add: assms g1_closed h_def padic_fields.SA_poly_glue_to_Qp_poly1 padic_fields_axioms)
    have to_Qp_h2: "\<And> y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)  \<Longrightarrow> y \<notin> B
                              \<Longrightarrow> SA_poly_to_Qp_poly m y h = SA_poly_to_Qp_poly m x g"
    proof- fix y assume A: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "y \<notin> B"
      have F0: "\<eta> y = \<xi> x"
        using A(1) A(2) \<eta>_eval2 by presburger
      have F4: "SA_poly_to_Qp_poly m y g1 = g0"
      proof(rule ext)
        fix n
        show "SA_poly_to_Qp_poly m y g1 n = g0 n"
          using SA_poly_to_Qp_poly_coeff[of y m g1 n] g1_closed unfolding g1_def 
          by (simp add: A SA_oneE SA_smult_formula UPQ.cfs_closed g0_closed)
      qed    
      show "SA_poly_to_Qp_poly m y h = SA_poly_to_Qp_poly m x g"
        unfolding F0  \<gamma>_def F4 unfolding g0_def
        using \<xi>_closed x_def x_closed assms 
        using A(1) A(2) F4 SA_poly_glue_to_Qp_poly2 g0_def g1_closed h_def by presburger
    qed
    have h_integral: "\<And> j x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> h j x \<in> \<O>\<^sub>p"
      using h_cfs1 h_cfs2' assms x_def 
      by (metis (no_types, lifting) PiE)
    hence h_integral': " \<And>j. h j \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> \<O>\<^sub>p"
      by auto 
    have \<eta>_root: "\<And> y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> SA_poly_to_Qp_poly m y h \<bullet> (\<eta> y) = \<zero>"
    proof- 
      fix y assume Ay: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      show "SA_poly_to_Qp_poly m y h \<bullet> (\<eta> y) = \<zero>"
        apply(cases "y \<in> B")
        using assms to_Qp_h1 
         apply (metis Ay SA_poly_to_SA_fun_formula \<eta>_eval1 \<xi>_closed)
        using assms to_Qp_h2
        by (metis Ay SA_poly_to_SA_fun_formula \<eta>_closed \<eta>_eval2 x_closed x_def)
    qed
    have g_eval_deg: "\<And> x. x \<in> B \<Longrightarrow> deg Q\<^sub>p (SA_poly_to_Qp_poly m x g) = deg (SA m) g"
    proof- 
      fix x assume A: "x \<in> B"
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using m_pos A assms is_semialgebraic_closed 
        by (meson basic_trans_rules(31))        
      have 0: "(SA_poly_to_Qp_poly m x g) \<in> carrier (UP Q\<^sub>p)"
        by(intro SA_poly_to_Qp_poly_closed x_closed assms) 
      show "deg Q\<^sub>p (SA_poly_to_Qp_poly m x g) = deg (SA m) g"
        using assms x_closed A 
        by (metis "0" Q\<^sub>p_def SA_Units_memE' SA_poly_to_Qp_poly_deg_bound UPQ.deg_eqI Z\<^sub>p_def 
            padic_fields.SA_poly_to_Qp_poly_coeff padic_fields_axioms)
    qed
    have g1_lcf: "g1 (deg (SA m) g) x = g (deg (SA m) g) x"
      using g1_def x_def x_closed assms   Qp.r_one R.cring_simprules(6) SA_Units_closed_fun 
          SA_oneE SA_poly_to_Qp_poly_coeff SA_smult_formula g0_def 
      by presburger
    have g1_deg_le: "deg (SA m) g1 \<le> deg (SA m) g"
        apply(intro deg_leqI g1_closed)
        by (metis (no_types, opaque_lifting) R.cring_simprules(6) SA_is_module UPQ.UP_car_memE(2) 
            g0_closed g0_def g1_def g_eval_deg module.smult_l_null x_def)
    have g1_lcf': "\<And>y. y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> g1 (deg (SA m) g) y = g (deg (SA m) g) x"
      using g1_def 
      by (metis R.one_closed SA_oneE SA_smult_formula UPQ.cfs_closed g0_closed g1_lcf x_closed)
    have g1_lcf_Unit: "g1 (deg (SA m) g) \<in> Units (SA m)"
      apply(rule SA_Units_memI) 
      using UPSA.UP_car_memE(1) g1_closed apply presburger
      unfolding g1_lcf' using assms 
      using SA_Units_memE' x_closed by presburger
    have h_lcf_fact: "h (deg (SA m) g) x = g (deg (SA m) g) x"
      using h_def x_def h_cfs1 by presburger
    have h_deg: "deg (SA m) h = deg (SA m) g"
      apply(intro deg_eqI h_closed)
      using g1_deg_le h_def apply (simp add: SA_poly_glue_deg assms  g1_closed)
      using h_lcf_fact unfolding h_def SA_poly_glue_def 
      using SA_Units_memE' SA_zero g1_lcf g1_lcf_Unit local.function_zero_eval x_closed by force
    have h_Unit: "h (deg (SA m) h) \<in> Units (SA m)"
    proof(rule SA_Units_memI)
      show " h (deg (SA m) h) \<in> carrier (SA m)"
        using h_closed  UPSA.lcf_closed by auto
      show "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> h (deg (SA m) h) x \<noteq> \<zero>"
        unfolding h_deg unfolding h_def SA_poly_glue_def
        by (metis (no_types, opaque_lifting) SA_Units_memE' SA_poly_glue_def assms(6) h_cfs1 h_cfs2' h_def x_closed)
    qed
    have \<eta>_semialg: "\<eta> \<in> carrier (SA m)"
      apply(intro denef_lemma_2_3[of _ h _ e l] m_pos assms(1) h_deg h_closed h_integral' h_Unit
                  \<eta>_function_ring \<eta>_integral, unfold h_deg, intro assms)
        apply (simp add: \<eta>_closed SA_poly_to_SA_fun_formula \<eta>_root h_closed)
       apply(rule \<eta>_res)
    proof
      fix y assume A: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      have 0: "SA_poly_to_SA_fun m (UPSA.pderiv m h) (\<eta> y # y) = 
            SA_poly_to_Qp_poly m y (UPSA.pderiv m h) \<bullet> (\<eta> y)"
        using A SA_poly_to_SA_fun_formula UPSA.pderiv_closed \<eta>_closed h_closed by presburger
      have 1: "SA_poly_to_Qp_poly m y (UPSA.pderiv m h) = 
                UPQ.pderiv (SA_poly_to_Qp_poly m y h)"
        using A SA_poly_to_Qp_poly_pderiv h_closed by presburger
      have "val (UPQ.pderiv (SA_poly_to_Qp_poly m y h) \<bullet> \<eta> y) \<le> eint (int e)"
      proof(cases "y \<in> B")
        case True
        show ?thesis using  A True 
          using SA_poly_to_Qp_poly_pderiv SA_poly_to_SA_fun_formula UPSA.pderiv_closed \<eta>_eval1
            \<xi>_closed assms to_Qp_h1 by fastforce
      next
        case False
        have F0: "SA_poly_to_Qp_poly m y h = SA_poly_to_Qp_poly m x g"
          using A False to_Qp_h2 by blast
        have F1: "\<eta> y = \<xi> x"
          using A False \<eta>_eval2 by auto
        show ?thesis
          unfolding F0 F1 using assms x_def 
          by (metis SA_poly_to_Qp_poly_pderiv SA_poly_to_SA_fun_formula UPSA.pderiv_closed \<xi>_closed x_closed)
      qed
      thus "val (SA_poly_to_SA_fun m (UPSA.pderiv m h) (\<eta> y # y)) \<le> eint (int e)"
        unfolding 0 1 by auto 
    qed
    show "\<exists>\<eta>\<in>carrier (SA m). \<forall>x\<in>B. \<eta> x = \<xi> x"
      using \<eta>_semialg \<eta>_eval1 
      by (meson assms  in_mono is_semialgebraic_closed)
  qed
next
  case F: False
  show ?thesis 
  proof(cases "B = {}")
    case True
    thus ?thesis by blast 
  next
    case False
    have m_eq: "m = 0"
      using F by auto 
    have b_car: "B = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using assms(3) is_semialgebraic_closed[of 0 B] False 
      unfolding m_eq Qp_zero_carrier   by auto 
    obtain \<eta> where \<eta>_def: "\<eta> = restrict \<xi> (carrier (Q\<^sub>p\<^bsup>m\<^esup>))"
      by blast
    have \<eta>_semialg: "\<eta> \<in> carrier (SA m)"
      unfolding m_eq 
    proof(rule SA_0_car_memI)
      have \<xi>_closed: "\<xi> \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
        apply(auto) using assms unfolding b_car 
        using val_ring_memE(2) by presburger
      show " \<eta> \<in> carrier (Q\<^sub>p\<^bsup>0\<^esup>) \<rightarrow> carrier Q\<^sub>p"
        using \<xi>_closed unfolding \<eta>_def m_eq by auto 
      show "\<And>x. x \<notin> carrier (Q\<^sub>p\<^bsup>0\<^esup>) \<Longrightarrow> \<eta> x = undefined"
        unfolding \<eta>_def m_eq by auto 
    qed
    have "\<forall>x\<in>B. \<eta> x = \<xi> x"
      unfolding \<eta>_def b_car by auto 
    thus ?thesis using \<eta>_semialg by auto 
  qed
qed

end 
end