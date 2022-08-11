theory Locales_For_Macintyre
  imports Padic_Cells
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Defining Locales for Proving Macintyre's Theorem\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Many of the lemmas required for Macintyre's Theorem have complex proof contexts which are 
interrelated to each other. This section defines various locales to provide these contexts and make 
their relationships to one another explicit.\<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>\<open>Locales for the Cell Decomposition Theorem Conclusions\<close>\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Denef's Cell Decomposition Theorems $I$ and $II$ both assert that the set $\mathbb{Q}_p^{m+1}$ 
can be decomposed into $p$-adic cells such that one or more $p$-adic polynomials are well-behaved on
each cell. The locales \texttt{SA\_poly\_ubounded} and \texttt{SA\_poly\_factors} express these 
notions of well-behavedness. \texttt{SA\_poly\_ubounded} formalizes the conclusion of Denef's cell
decomposition theorem $I$, while \texttt{SA\_poly\_factors} expresses the conclusion of theorem $II$. 
\<close>

locale SA_poly_ubounded = padic_fields + 
  fixes n P c A N
  assumes P_closed: "P \<in> carrier (UP (SA n))"
  assumes c_closed: "c \<in> carrier (SA n)" 
  assumes A_closed: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes ubounded: "\<And> x t. t#x \<in> A \<Longrightarrow>val ((SA_poly_to_Qp_poly n x P)\<bullet> t) \<le> 
                           val ((UPQ.taylor_term (c x) (SA_poly_to_Qp_poly n x P) i)\<bullet>t) + eint N"

locale SA_poly_factors  = padic_fields + 
  fixes n::nat and  m::nat and  P::padic_nary_function_poly and  
        c:: padic_nary_function and  A::"padic_tuple set" and 
        u:: padic_nary_function and  h:: padic_nary_function  and  k::nat
  assumes h_closed: "h \<in> carrier (SA n)"
  assumes c_closed: "c \<in> carrier (SA n)"
  assumes u_closed: "u \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)" 
  assumes A_closed: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes u_val: "\<And> x t. \<lbrakk> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>); t \<in> carrier Q\<^sub>p; t#x \<in> A\<rbrakk> 
                               \<Longrightarrow>   val (u (t#x)) = 0"
  assumes factors: "\<And> x t. \<lbrakk> x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>); t \<in> carrier Q\<^sub>p; t#x \<in> A\<rbrakk> \<Longrightarrow>               
    (SA_poly_to_Qp_poly n x P)\<bullet> t = ((u (t#x))[^] m)\<otimes>(h x)\<otimes> (t \<ominus> (c x))[^] k"

context padic_fields
begin  

lemma SA_poly_uboundedI:
  assumes "f \<in> carrier (UP (SA n))"
  assumes "c \<in> carrier (SA n)"
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "\<And> x t i. t#x \<in> A \<Longrightarrow>  
              val ( (SA_poly_to_Qp_poly n x f)\<bullet> t) \<le>  val ((UPQ.taylor_term (c x) (SA_poly_to_Qp_poly n x f) i)\<bullet>t) + eint N"
  shows "SA_poly_ubounded p n f c A N "
  apply(intro SA_poly_ubounded.intro, intro padic_fields_axioms)
  using assms unfolding SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def by auto 
 
lemma SA_poly_uboundedE:
  assumes "P \<in> carrier (UP (SA n))"
  assumes "c \<in> carrier (SA n)"
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "t#x \<in> A"
  assumes "\<exists> N. SA_poly_ubounded p n P c A N"
  shows "\<exists>N. val ( (SA_poly_to_Qp_poly n x P)\<bullet> t) \<le>  val ((UPQ.taylor_term (c x) (SA_poly_to_Qp_poly n x P) i)\<bullet>t) + eint N"
  using assms   
  unfolding SA_poly_ubounded_def SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
  by blast

text\<open>When A is a cell with center c, whether Ps are bounded on A is independent of the choice of c\<close>

text\<open>Boundedness of a semialgebraic polynomial on a cell decomposition\<close>
definition is_compatible_decomp where
"is_compatible_decomp n S P \<equiv> is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) \<and> 
                              (\<forall>s \<in> S.  \<exists>N. SA_poly_ubounded p n P (center s) (condition_to_set s) N)"

lemma is_compatible_decompI:
  assumes "P \<in> carrier (UP (SA n))"
  assumes "is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>))"
  assumes "\<And>s. s \<in> S \<Longrightarrow>  \<exists>N. SA_poly_ubounded p n P (center s) (condition_to_set s) N"
  shows "is_compatible_decomp n S P"
  using assms is_compatible_decomp_def 
  by blast

text\<open>Factoring a semialgebraic polynomial by a semialgebraic power\<close>

lemma SA_poly_factors_closure:
  assumes "SA_poly_factors p n m P c A u h k"
  shows "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
        "u \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
        "c \<in> carrier (SA n)"
        "h \<in> carrier (SA n)"
        "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<Longrightarrow> u x \<in> carrier Q\<^sub>p"
  using assms 
  unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
  by auto 

lemma SA_poly_factorsE:
  assumes "SA_poly_factors p n m P c A u h k"
  assumes "t#x \<in> A"
  shows "val (u (t#x)) = 0"
        "(SA_poly_to_Qp_poly n x P)\<bullet> t = (((u (t#x))[^] m)\<otimes>(h x)\<otimes> (t \<ominus> (c x)) [^] k)"
        "(u (t#x)) \<in> carrier Q\<^sub>p"
        "(u (t#x)) \<noteq> \<zero>"
        "(u (t#x)) \<in> nonzero Q\<^sub>p"
proof-
  have 0: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
    using assms SA_poly_factors_closure(1)
    by blast 
  have 1:"x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
    using 0 assms cartesian_power_tail[of "t#x" Q\<^sub>p n ] 
    by (metis list.sel(3))      
  have 2: "t \<in> carrier Q\<^sub>p"
    using 0 cartesian_power_head[of "t#x" Q\<^sub>p n]
    by (metis list.sel(1))
  show 3: "val (u (t#x)) = 0"
    apply(intro SA_poly_factors.u_val[of p n m P c A u h k] assms(1))
    using 1 2 assms unfolding Q\<^sub>p_def  Z\<^sub>p_def  by auto 
  show "(SA_poly_to_Qp_poly n x P)\<bullet> t = (((u (t#x)) [^] m)\<otimes>(h x)\<otimes> (t \<ominus> (c x)) [^] k)"
    using assms 0 1 2 
    unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def  Z\<^sub>p_def  
    by auto 
  show 4: "u (t # x) \<in> carrier Q\<^sub>p"
    using assms SA_poly_factors_closure by blast 
  show 5: "u (t # x) \<noteq> \<zero>" 
    using 3 val_def infinity_ne_i0 by metis
  show " u (t # x) \<in> nonzero Q\<^sub>p"
    by(rule nonzero_memI, rule 4, rule 5)
qed

lemma SA_poly_factorsI:
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "u \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
  assumes "c \<in> carrier (SA n)"
  assumes "h \<in> carrier (SA n)"
  assumes "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> t#x \<in> A \<Longrightarrow> val (u (t#x)) = 0 \<and> 
                                       (SA_poly_to_Qp_poly n x P)\<bullet> t = (((u (t#x))[^] m)\<otimes>(h x)\<otimes> (t \<ominus> (c x))[^] k)"
  shows "SA_poly_factors p n m P c A u h k"
  apply(intro SA_poly_factors.intro padic_fields_axioms SA_poly_factors_axioms.intro)
  using assms unfolding Q\<^sub>p_def Z\<^sub>p_def by auto 

lemma SA_poly_factorsI':
  assumes "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)"
  assumes "u \<in> (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
  assumes "c \<in> carrier (SA n)"
  assumes "h \<in> carrier (SA n)"
  assumes "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> t#x \<in> A \<Longrightarrow> val (u (t#x)) = 0"
  assumes "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>) \<Longrightarrow> t \<in> carrier Q\<^sub>p \<Longrightarrow> t#x \<in> A \<Longrightarrow> (SA_poly_to_Qp_poly n x P)\<bullet> t = (((u (t#x))[^] m)\<otimes>(h x)\<otimes> (t \<ominus> (c x))[^] k)"
  shows "SA_poly_factors p n m P c A u h k"
  by(intro SA_poly_factorsI assms conjI, auto) 


lemma SA_poly_ubounded_facts:
  assumes "\<exists>N. SA_poly_ubounded p m f c A N"
  shows "f \<in> carrier (UP (SA m))"
        "c \<in> carrier (SA m)"
        "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  using assms  unfolding SA_poly_ubounded_def SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def by auto 

lemma SA_poly_ubounded_facts':
  assumes "SA_poly_ubounded p m f c A N"
  shows "f \<in> carrier (UP (SA m))"
        "c \<in> carrier (SA m)"
        "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
  using assms unfolding SA_poly_ubounded_def SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def by auto

lemma SA_poly_uboundedE': 
  assumes "SA_poly_ubounded p m f c A N"
  shows " \<forall>x t i.
            t # x \<in> A \<longrightarrow>
            val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N"
  using assms  unfolding SA_poly_ubounded_def unfolding SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
  by blast

lemma SA_poly_uboundedE'': 
  assumes "\<exists>N. SA_poly_ubounded p m f c A N"
  shows " \<exists>N. \<forall>x t i.
            t # x \<in> A \<longrightarrow>
            val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N"
  using assms SA_poly_uboundedE  unfolding SA_poly_ubounded_def SA_poly_ubounded_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
  by metis

lemma SA_poly_uboundedE''':
  assumes "\<exists>N. SA_poly_ubounded p m f c A N"
  shows "\<exists>N::nat. (\<forall>x t i. t # x \<in> A \<longrightarrow> val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + N)"
proof(cases "A = {}")
  case True
  then show ?thesis by blast 
next
  case False
  obtain N::int where N_def: "(\<forall>x t i. t # x \<in> A \<longrightarrow> val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N)"
    using assms SA_poly_uboundedE' by blast 
  obtain k::nat where k_def: "k \<ge> N"
    apply(cases "N < 0")
     apply force
    by (metis verit_comp_simplify(2) verit_comp_simplify(3) zero_le_imp_eq_int)
  then have "eint k \<ge> eint N"
    by simp
  hence 0: "\<And> x t i. val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint N \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint k"
    by (meson add_left_mono)
  hence 1: "(\<forall>x t i. t # x \<in> A \<longrightarrow> val (SA_poly_to_Qp_poly m x f \<bullet> t) \<le> val (UPQ.taylor_term (c x) (SA_poly_to_Qp_poly m x f) i \<bullet> t) + eint k)"
    using N_def 
    by (meson eint_ord_trans)
  thus ?thesis by blast
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>Denef's Facts $I_d$ and $II_d$\<close>  
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)

locale denef_I = padic_fields + 
  fixes d::nat
  assumes cell_decomp: "\<And>m P.\<lbrakk> P \<in> carrier (UP (SA m)); deg (SA m) P \<le> d \<rbrakk> \<Longrightarrow> 
                      \<exists> S. (is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
                      (\<forall>A \<in> S. \<exists>N. SA_poly_ubounded p m P (center A) (condition_to_set A) N))"

locale denef_II = padic_fields + 
  fixes d::nat
  assumes cell_decomp: "\<And>n m Ps.\<lbrakk> finite Ps \<and> 
                                  (\<forall>P \<in> Ps. P \<in> carrier (UP (SA n)) \<and>  deg (SA n) P \<le> d) \<and> m > 0 \<rbrakk> \<Longrightarrow> 
              
                            (\<exists> S. (is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>)) \<and> 
                           (\<forall>A \<in> S. \<forall>P \<in> Ps. \<exists>u h k. SA_poly_factors p n m P (center A) (condition_to_set A) u h k)))"

end
