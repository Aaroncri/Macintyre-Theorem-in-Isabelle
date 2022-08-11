theory Denef_Cell_Decomp_Theorem_II_Induct
  imports Denef_Cell_Decomp_Theorem_II_Base
begin

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Setting up the reduction from  $r=1$ to the General Case \<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>This section shows how to pass to the $r>1$ case of theorem $II_{d+1}$. We introduce the 
concept of a set $A \subseteq \mathbb{Q}_p^{m+1}$ being $r$-prepared relative to a finite set 
of polynomials $Fs$. This means that the set $A$ is an intersection of cells indexed by the 
set $Fs$, such that these cells have at most $r$ distinct center functions. Furthemore, the 
cell indexed by function $f$ will be as in the conclusion of theorem $II_{d+1}$. A set will be
$r$-preparable if it can be partitioned into $r$-prepared sets. Given a set $Fs$ of $r$ different 
functions, we can easily show that $\mathbb{Q}_p^{m+1}$ is $r$-preparable relative to this set. In
this section, we will first show that if a set if $2$-preparable, then it is also $1$-preparable, 
then use this to easily deduce that if a set if $r$-preparable, then it is $1$-preparable. Showing 
that $\mathbb{Q}_p^{m+1}$ is $1$-preparable relative to any finite set of semialgebraic polynomials 
of degree $\leq d$ will be enough to prove theorem $II_{d+1}$.\<close>

context common_decomp_proof_context 
begin

definition is_r_prepared where 
"is_r_prepared m n r Fs A  \<equiv> 
    finite Fs \<and> 
    
    Fs \<subseteq> carrier (UP (SA m)) \<and> (\<exists>Cs \<C>. \<C> \<in> Fs \<rightarrow> Cs \<and> card (center ` \<C> ` Fs) \<le> r \<and> 
    
    A = (\<Inter>f \<in> Fs. condition_to_set (\<C> f)) \<and> 
    
    (\<forall> f \<in> Fs. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> 
        (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))) "

lemma is_r_preparedI:
  assumes "finite Fs"
  assumes "Fs \<subseteq> carrier (UP (SA m))"
  assumes "\<C> \<in> Fs \<rightarrow> Cs"
  assumes "card (center ` \<C> ` Fs) \<le> r"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> is_cell_condition (\<C> f)"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> arity (\<C> f) = m" 
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k)"
  assumes "A = (\<Inter>f \<in> Fs. condition_to_set (\<C> f))"
  shows "is_r_prepared m n r Fs A "
  unfolding is_r_prepared_def using assms by blast 

lemma is_r_preparedE: 
  assumes "is_r_prepared m n r Fs A "
  shows "finite Fs"
        "Fs \<subseteq> carrier (UP (SA m))"
        " (\<exists>Cs \<C>. \<C> \<in> Fs \<rightarrow> Cs \<and> card (center ` \<C> ` Fs) \<le> r \<and> A = (\<Inter>f \<in> Fs. condition_to_set (\<C> f)) \<and> (\<forall> f \<in> Fs. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> 
                               (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k)))"
  using assms  unfolding is_r_prepared_def apply blast
  using assms  unfolding is_r_prepared_def apply blast
  using assms  unfolding is_r_prepared_def by blast

definition is_r_preparable where 
"is_r_preparable m n r Fs A = (\<exists>Ps. finite Ps \<and> Ps partitions A \<and> (\<forall>S \<in> Ps. is_r_prepared m n r Fs S ))"

lemma is_r_preparableI:
  assumes "finite Ps"
  assumes "Ps partitions A"
  assumes "\<And>S. S \<in> Ps \<Longrightarrow> is_r_prepared m n r Fs S"
  shows "is_r_preparable m n r Fs A"
  using assms unfolding is_r_preparable_def by blast 

lemma is_r_prepared_imp_semialg:
  assumes "is_r_prepared m n r Fs A"
  assumes "Fs \<noteq> {}" 
  shows "is_semialgebraic (Suc m) A"
proof- 
  obtain Cs \<C> where a0: "\<C> \<in> Fs \<rightarrow> Cs \<and> card (center ` \<C> ` Fs) \<le> r \<and> A = (\<Inter>f \<in> Fs. condition_to_set (\<C> f)) \<and> (\<forall> f \<in> Fs. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> 
                               (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
    using assms is_r_preparedE(3)[of m n r Fs A] by blast 
  have 0: "A = (\<Inter>f \<in> Fs. condition_to_set (\<C> f))"
    using a0 by force 
  have 1: "\<And>f. f \<in> Fs \<Longrightarrow> is_cell_condition (\<C> f)"
    using a0 by blast 
  have 2: "\<And>f. f \<in> Fs \<Longrightarrow> arity (\<C> f) = m" 
    using a0 by blast 
  have 3: "\<And>f. f \<in> Fs \<Longrightarrow> is_semialgebraic (Suc m) (condition_to_set (\<C> f))"
  proof- fix f assume a1: " f \<in> Fs"
    show " is_semialgebraic (Suc m) (condition_to_set (\<C> f))"
    using a1 condition_to_set_is_semialgebraic[of "\<C> f"] 1[of f] 2[of f] 
    by blast 
  qed
  show ?thesis unfolding 0
    apply(rule finite_intersection_is_semialg, rule is_r_preparedE[of m n r Fs A], rule assms, rule assms)
    using 3 unfolding is_semialgebraic_def by blast
qed

lemma is_r_preparable_imp_semialg:
  assumes "is_r_preparable m n r Fs A"
  assumes "Fs \<noteq> {}" 
  shows "is_semialgebraic (Suc m) A"
proof- 
  obtain Ps where Ps_def: "finite Ps \<and> Ps partitions A \<and> (\<forall>S \<in> Ps. is_r_prepared m n r Fs S )"
    using assms unfolding is_r_preparable_def by blast 
  have 0: "A = \<Union> Ps"
    using Ps_def is_partitionE by blast 
  have 1: "\<And>S. S \<in> Ps \<Longrightarrow> is_semialgebraic (Suc m) S"
    apply(rule is_r_prepared_imp_semialg[of m n r Fs])
    using Ps_def apply blast
    using assms by blast 
  show ?thesis unfolding 0 apply(rule finite_union_is_semialgebraic')
    using Ps_def apply blast
    using 1 unfolding is_semialgebraic_def by blast 
qed

lemma is_r_prepared_intersect: 
  assumes "is_r_prepared m n r Fs A"
  assumes "Fs \<noteq> {}"
  assumes "is_r_prepared m n k Gs B"
  assumes "Fs \<inter> Gs = {}"
  shows "is_r_prepared m n (r+k) (Fs \<union> Gs) (A \<inter> B)"
proof- 
  obtain \<A> As where a0: "\<A>\<in> Fs \<rightarrow> As \<and> card (center ` \<A> ` Fs) \<le> r \<and> A = (\<Inter>f \<in> Fs. condition_to_set (\<A> f)) \<and> (\<forall> f \<in> Fs. is_cell_condition (\<A> f) \<and> arity (\<A> f) = m \<and> 
                               (\<exists>u h k. SA_poly_factors p m n f (center (\<A> f)) (condition_to_set (\<A> f)) u h k))"
    using assms is_r_preparedE[of m n r Fs A] by blast 

  obtain \<B> Bs  where a1: "\<B> \<in> Gs \<rightarrow> Bs \<and> card (center ` \<B> ` Gs) \<le> k \<and> B = (\<Inter>f \<in> Gs. condition_to_set (\<B> f)) \<and> (\<forall> f \<in> Gs. is_cell_condition (\<B> f) \<and> arity (\<B> f) = m \<and> 
                               (\<exists>u h k. SA_poly_factors p m n f (center (\<B> f)) (condition_to_set (\<B> f)) u h k))"
    using assms is_r_preparedE[of m n k Gs B] by blast 

  obtain \<C> where \<C>_def: "\<C> = (\<lambda>f. if f \<in> Fs then \<A> f else \<B> f)"
    by blast 

  have \<C>_Fs: "\<And>f. f \<in> Fs \<Longrightarrow> \<C> f = \<A> f"
    using \<C>_def by metis 

  have \<C>_Gs: "\<And>f. f \<in> Gs \<Longrightarrow> \<C> f = \<B> f"
    using \<C>_def assms  by (metis Int_iff empty_iff)

  obtain Cs where Cs_def: "Cs = As \<union> Bs"
    by blast 

  have \<C>_range: "\<C> \<in> Fs \<union> Gs \<rightarrow> Cs"
    apply(rule, rule conjI, rule)
    unfolding \<C>_Fs Cs_def using a0 apply blast 
    apply(rule )
    unfolding \<C>_Gs Cs_def using a1 by blast 

  have 0: "center ` \<C> ` (Fs \<union> Gs) = center ` \<A>` Fs \<union> center ` \<B> ` Gs"
  apply(rule equalityI')
    using \<C>_Fs \<C>_Gs is_r_preparedE(1) assms apply blast
    unfolding Un_iff apply(erule disjE)
    using \<C>_Fs is_r_preparedE(1) assms  image_iff 
    apply (smt mem_simps(3))
       using \<C>_Gs is_r_preparedE(1) assms  image_iff 
       by (smt mem_simps(3))

  have R: "\<And> a b. finite a \<Longrightarrow> finite b \<Longrightarrow> card a \<le> r \<Longrightarrow> card b \<le> k \<Longrightarrow> card (a \<union> b) \<le> r + k"
    by (smt add.assoc add.commute card_Un_le le_iff_add)

  have 1: "\<And> f. f \<in> Fs \<union> Gs \<Longrightarrow> is_cell_condition (\<C> f)"
  proof- fix f assume A: "f \<in> Fs \<union> Gs"
    show "is_cell_condition (\<C> f)"
      apply(cases "f \<in> Fs")
      unfolding \<C>_Fs using a0 apply blast
      using A \<C>_Gs[of f] a1 by (metis UnE \<C>_def)
  qed
  have 2: "\<And> f. f \<in> Fs \<union> Gs \<Longrightarrow> arity (\<C> f) = m"
  proof- fix f assume A: "f \<in> Fs \<union> Gs"
    show "arity (\<C> f) = m"
      apply(cases "f \<in> Fs")
      unfolding \<C>_Fs using a0 apply blast
      using A \<C>_Gs[of f] a1 by (metis UnE \<C>_def)
  qed
  have 3: "\<And>f. f \<in> Fs \<union> Gs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k"
  proof- fix f assume A: "f \<in> Fs \<union> Gs"
    show "\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k"
      apply(cases "f \<in> Fs")
      unfolding \<C>_Fs using a0 apply blast
      using A \<C>_Gs[of f] a1 by (metis UnE \<C>_def)
  qed
  have 4: "(\<Inter>f\<in>Fs. condition_to_set (\<A> f)) = (\<Inter>f\<in>Fs. condition_to_set (\<C> f))"
    using \<C>_Fs 
    by (smt Sup.SUP_cong)
  have 5: "(\<Inter>f\<in>Gs. condition_to_set (\<B> f)) = (\<Inter>f\<in>Gs. condition_to_set (\<C> f))"
    using \<C>_Gs 
    by (smt Sup.SUP_cong)
  show ?thesis
    apply(rule is_r_preparedI[of _ _ \<C> Cs])
    using assms is_r_preparedE apply blast
    using assms is_r_preparedE apply blast
         apply(rule \<C>_range)
    unfolding 0 apply(rule R)
    using assms is_r_preparedE apply blast
    using assms is_r_preparedE apply blast
    using a0 apply blast
    using a1 apply blast
    apply(rule 1, blast, rule 2, blast, rule 3, blast)
    using a0 a1 unfolding 4 5 by blast
qed

definition pairwise_intersect where 
"pairwise_intersect As Bs = {c. \<exists>a \<in> As. \<exists>b \<in> Bs. c = a \<inter> b}"

lemma partition_intersection:
  assumes "As partitions A"
  assumes "Bs partitions B"
  shows "(pairwise_intersect As Bs) partitions (A \<inter> B)"
proof(rule is_partitionI, rule disjointI)
  fix a b assume a0: "a \<in> pairwise_intersect As Bs" "b \<in> pairwise_intersect As Bs" "a \<noteq> b"
  obtain a1 b1 where def1: "a1 \<in> As \<and> b1 \<in> Bs \<and> a = a1 \<inter> b1"
    using a0 unfolding pairwise_intersect_def by blast 
  obtain a2 b2 where def2: "a2 \<in> As \<and> b2 \<in> Bs \<and> b = a2 \<inter> b2"
    using a0 unfolding pairwise_intersect_def by blast 
  have 0: "a \<inter> b = (a1 \<inter> a2) \<inter> (b1 \<inter> b2)"
    using def1 def2 by blast 
  show " a \<inter> b= {}"
  proof(cases "a1 \<noteq> a2")
    case True
    have T0: "a1 \<inter> a2 = {}"
      apply(rule disjointE[of As a1 a2] )
      using def1 def2 assms(1) True is_partitionE(1)[of As A] apply blast
      using def1 apply blast using def2 apply blast by(rule True)
    thus ?thesis unfolding 0 by blast      
  next
    case False
    then have F0: "b1 \<noteq> b2"
      using a0 def1 def2 by blast 
    have F1: "b1 \<inter> b2 = {}"
      apply(rule disjointE[of Bs b1 b2])
      using def1 def2 assms(2) F0  is_partitionE(1)[of Bs B] apply blast
      using def1 apply blast using def2 apply blast by(rule F0)
    thus ?thesis unfolding 0 by blast      
  qed
next 
  show "\<Union> (pairwise_intersect As Bs) = A \<inter> B"
  proof(rule equalityI')
    fix x assume A: "x \<in> \<Union> (pairwise_intersect As Bs)"
    then obtain a b where def1: "a \<in> As \<and> b \<in> Bs \<and> x \<in> a \<inter> b"
      unfolding pairwise_intersect_def by blast 
    have 0: "a \<subseteq> A"
      using def1 assms is_partitionE by blast 
    have 1: "b \<subseteq> B"
      using def1 assms is_partitionE by blast 
    show " x \<in> A \<inter> B"
      using 0 1 def1 by blast 
  next 
    fix x assume A: "x \<in> A \<inter> B"
    obtain a where a_def: "a \<in> As \<and> x \<in> a"
      using A assms is_partitionE by blast 
    obtain b where b_def: "b \<in> Bs \<and> x \<in> b"
      using A assms is_partitionE by blast 
    have 0: "x \<in> a \<inter> b"
      using a_def b_def by blast 
    show "x \<in> \<Union> (pairwise_intersect As Bs)"
      using a_def b_def 0 unfolding pairwise_intersect_def 
      by blast 
  qed
qed

lemma pairwise_intersect_finite: 
  assumes "finite As"
  assumes "finite Bs"
  shows "finite (pairwise_intersect As Bs)"
proof- 
  have 0: "(pairwise_intersect As Bs) = (\<Union> a \<in> As. (\<inter>) a ` Bs)"
    unfolding pairwise_intersect_def
    apply(rule equalityI')
    unfolding mem_Collect_eq apply blast
    by blast
  have 1: "\<And>a. a \<in> As \<Longrightarrow> finite ((\<inter>) a ` Bs)"
    using assms by blast 
  show ?thesis unfolding 0 using assms(1) 1 by blast 
qed

lemma is_r_preparable_intersect: 
  assumes "is_r_preparable m n r Fs A"
  assumes "Fs \<noteq> {}"
  assumes "is_r_preparable m n k Gs B"
  assumes "Gs \<noteq> {}"
  assumes "Fs \<inter> Gs = {}"
  shows "is_r_preparable m n (r+k) (Fs \<union> Gs) (A \<inter> B)"
proof- 
  obtain As where As_def: "finite As \<and> As partitions A \<and> (\<forall>S \<in> As. is_r_prepared m n r Fs S )"
    using assms unfolding is_r_preparable_def by blast 
  obtain Bs where Bs_def: "finite Bs \<and> Bs partitions B \<and> (\<forall>S \<in> Bs. is_r_prepared m n k Gs S )"
    using assms unfolding is_r_preparable_def by blast 
  obtain Cs where Cs_def: "Cs = pairwise_intersect As Bs"
    by blast 
  show "is_r_preparable m n (r+k) (Fs \<union> Gs) (A \<inter> B)"
    apply(rule is_r_preparableI[of Cs])
    unfolding Cs_def apply(rule pairwise_intersect_finite)
    using As_def apply blast
    using Bs_def apply blast
     apply(rule partition_intersection)
    using As_def apply blast
    using Bs_def apply blast
  proof- 
    fix S assume A: "S \<in> pairwise_intersect As Bs"
    obtain a b where def1: "a \<in> As \<and> b \<in> Bs \<and> S = a \<inter> b"
      using A unfolding pairwise_intersect_def by blast 
    have 0: "S = a \<inter> b"
      using def1 by blast 
    show "is_r_prepared m n (r + k) (Fs \<union> Gs) S"
      unfolding 0 
      apply(rule is_r_prepared_intersect)
      using def1 As_def apply blast
      using assms apply blast
      using def1 Bs_def apply blast
      using assms by blast
  qed
qed

lemma iter_partition:
  assumes "As partitions A"
  assumes "finite As"
  assumes "\<And>a. a \<in> As \<Longrightarrow> \<exists>Bs. finite Bs \<and> Bs partitions a \<and> (\<forall>b \<in> Bs. P b)"
  shows "\<exists>Bs. finite Bs \<and> Bs partitions A \<and> (\<forall>b \<in> Bs. P b)"
proof- 
  obtain F where F_def: "F = (\<lambda>a. (SOME Bs.  finite Bs \<and> Bs partitions a \<and> (\<forall>b \<in> Bs. P b)))"
    by blast 
  have FE: "\<And>a. a \<in> As \<Longrightarrow> finite (F a) \<and> (F a) partitions a \<and> (\<forall>b \<in> (F a). P b)"
  proof- fix a assume A: "a \<in> As"
    show "finite (F a) \<and> (F a) partitions a \<and> (\<forall>b \<in> (F a). P b)"
      using verit_sko_ex_indirect[of "F a"] unfolding F_def using assms(3) A by blast  
  qed
  obtain Bs where Bs_def: "Bs = (\<Union> a \<in> As. F a)"
    by blast 
  have 0: "finite Bs"
    unfolding Bs_def using FE assms by blast 
  have 1: "disjoint Bs"
  proof(rule disjointI)
    fix a b assume A: "a \<in> Bs" "b \<in> Bs" "a \<noteq> b"
    obtain c where c_def: "c \<in> As \<and> a \<in>  F c"
      using Bs_def A by blast 
    obtain d where d_def: "d \<in> As \<and> b \<in>  F d"
      using Bs_def A by blast 
    have 0: "a \<subseteq> c"
      using c_def FE[of c] is_partitionE(2)[of "F c" c] by blast 
    have 1: "b \<subseteq> d"
      using d_def FE[of d] is_partitionE(2)[of "F d" d] by blast 
    show "a \<inter> b = {}"
    proof(cases "c = d")
      case True
      show ?thesis apply(rule disjointE[of "F c"])
        unfolding True using FE is_partitionE d_def apply blast
        using c_def unfolding True apply blast
        using d_def apply blast
        by(rule A)
    next
      case False
      have "c \<inter> d = {}"
        apply(rule disjointE[of As])
        using assms is_partitionE apply blast
        using c_def apply blast
        using d_def apply blast
        using False by blast 
      then show ?thesis using 0 1 by blast  
    qed
  qed
  have 2: "(\<forall>b \<in> Bs. P b)"
    apply(rule )
    unfolding Bs_def using FE 
    by blast
  have FE': "\<And>a. a \<in> As \<Longrightarrow> (\<Union> (F a)) = a "
    apply(rule is_partitionE)
    using FE by blast 
  have 3: "Bs partitions A"
    apply(rule is_partitionI, rule 1)
apply(rule equalityI')
    unfolding Bs_def using assms is_partitionE(2)[of As A]
      FE' is_partitionE(2) apply blast
  proof- 
    fix x assume A: "x \<in> A"
    then obtain a where a_def: "a \<in> As \<and> x \<in> a"
      using assms is_partitionE by blast 
    then have "x \<in> (\<Union> (F a))"
      using a_def FE' by blast 
    thus " x \<in> \<Union> (\<Union> (F ` As))"
      using a_def A by blast 
  qed
  show "\<exists>Bs. finite Bs \<and> Bs partitions A \<and> (\<forall>b\<in>Bs. P b)"
    using 0 2 3 by blast 
qed

lemma is_r_preparable_partition: 
  assumes "finite As"
  assumes "As partitions A"
  assumes "\<And>a. a \<in> As \<Longrightarrow> is_r_preparable m n r Fs a"
  shows "is_r_preparable m n r Fs A"
proof- 
  have 0: "\<exists>Bs. finite Bs \<and> Bs partitions A \<and> (\<forall>b \<in> Bs. is_r_prepared m n r Fs b)"
    apply(rule iter_partition[of As], rule assms, rule assms)
    using assms(3) unfolding is_r_preparable_def by blast 
  then show ?thesis 
    unfolding is_r_preparable_def by blast 
qed

lemma is_r_preparable_cell_decomp: 
  assumes "is_cell_decomp m S A"
  assumes "\<And>\<C>. \<C> \<in> S \<Longrightarrow> is_r_preparable m n r Fs (condition_to_set \<C>)"
  shows "is_r_preparable m n r Fs A"
  apply(rule is_r_preparable_partition[of "condition_to_set ` S"])
  using assms is_cell_decompE by auto 

lemma is_r_prepared_imp_is_r_preparable: 
  assumes "is_r_prepared m n r Fs A"
  shows "is_r_preparable m n r Fs A"
  apply(rule is_r_preparableI[of "{A}"], blast)
   apply(rule is_partitionI, rule disjointI, blast, blast)
  using assms by blast 

lemma common_decomp: 
  assumes f_closed: "f \<in> carrier (UP (SA m))"
  assumes f_deg: "deg (SA m) f \<le> Suc d"
  assumes "is_cell_condition \<C>"
  assumes "\<C> = Cond m C c a1 a2 I" 
  assumes "\<exists>N. SA_poly_ubounded p m f c (condition_to_set \<C>) N"
  assumes "n > 0"
  shows "\<exists> S. is_cell_decomp m S (condition_to_set \<C>) 
              \<and> (\<forall> \<B> \<in> S. (\<exists>g \<in> carrier (UP (SA m)).  
                         center \<B> = c 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f) 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f))
                      \<and> common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m 
                      \<and> ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) 
                           \<or> (denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n))))"
proof-                             
  have 0: "\<exists>S. is_cell_decomp m S (condition_to_set \<C>) \<and>
           (\<forall>\<B>\<in>S. \<B> = Cond m (fibre_set \<B>) c a1 a2 I \<and>
                   (\<exists>g\<in>carrier (UP (SA m)).
                       deg (SA m) g \<le> Suc d \<and>
                       (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                              SA_poly_to_Qp_poly m x g =
                              SA_poly_to_Qp_poly m x f) \<and>
                       (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                       (\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                            taylor_expansion (SA m) c g i
                            \<in> Units (SA m))))"
    apply(rule refine_each_cell[of m "decomp_by_cfs m (taylor_expansion (SA m) c f) \<C>"]
              , intro decomp_by_cfs_is_decomp)
  proof- 
    obtain a where a_def: "a = taylor_expansion (SA m) c f"
      by auto 
    have c_closed: "c \<in> carrier (SA m)"
      using assms is_cell_conditionE(2)[of m C c a1 a2 I] by auto 
    have a_closed: "a \<in> carrier (UP (SA m))"
      using assms a_def taylor_expansion_closed c_closed by auto 
    show 0: "taylor_expansion (SA m) c f \<in> carrier (UP (SA m))"
            "is_cell_condition \<C>" "arity \<C> = m"
      using a_closed assms unfolding a_def assms arity.simps by auto 
    fix \<B> assume A: "\<B> \<in> decomp_by_cfs m (taylor_expansion (SA m) c f) \<C>"
    then obtain b where b_def: "b \<in> poly_cfs_part m a C \<and> \<B> = refine_fibres \<C> b"
      unfolding a_def decomp_by_cfs_def assms fibre_set.simps by auto 
    have b_eq: "b \<in> poly_cfs_part m a C"
      using b_def by auto 
    have B_eq: "\<B> = Cond m b c a1 a2 I"
      using b_def unfolding assms refine_fibres_def arity.simps l_bound.simps u_bound.simps 
                boundary_condition.simps center.simps by auto 
    obtain g where g_def: "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) 
              (poly_unit_replacement m a b)"
      by blast 
    have prems: "is_semialgebraic m C"
                "f \<in> carrier (UP (SA m))"
                "c \<in> carrier (SA m)"
                "b \<in> poly_cfs_part m a C"
                "g = taylor_expansion (SA m) (\<ominus>\<^bsub>SA m\<^esub> c) (poly_unit_replacement m a b)"
      using assms b_def a_closed a_def A g_def  unfolding assms by auto 
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
    have 0: " deg (SA m) g \<le> Suc d"
      using g_def a_closed taylor_expansion_closed c_closed poly_unit_replacement_deg assms 
      using a_def poly_unit_replacement_deg_lemma prems(4) by fastforce
    have 1: "\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f"
      using g_props unfolding B_eq condition_to_set.simps by (meson cell_formula(2))
    have 2: "\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f)"
      using g_props unfolding B_eq condition_to_set.simps by (meson cell_formula(2))
    have 3: "\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                 taylor_expansion (SA m) c g i \<in> Units (SA m)"
      using g_props unfolding B_eq condition_to_set.simps by (meson cell_formula(2))
    have "is_cell_condition \<B>"
      using assms a_closed A decomp_by_cfs_is_decomp is_cell_decompE(3) arity.simps
      unfolding a_def by metis 
    hence 4: "is_cell_decomp m {\<B>} (condition_to_set \<B>)"
      using singleton_cell_decomp B_eq arity.simps by smt 
    have 5: "is_cell_decomp m {\<B>} (condition_to_set \<B>) \<and>
             (\<forall>\<B>\<in>{\<B>}. \<B> = Cond m (fibre_set \<B>) c a1 a2 I  \<and>
                     (\<exists>g\<in>carrier (UP (SA m)).
                         deg (SA m) g \<le> Suc d \<and>
                         (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f) \<and>
                         (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                         (\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                              taylor_expansion (SA m) c g i
                              \<in> Units (SA m))))"
      using 0 1 2 3 4 B_eq center.simps g_props  by auto 
    thus "\<exists>S. is_cell_decomp m S (condition_to_set \<B>) \<and>
             (\<forall>\<B>\<in>S. \<B> = Cond m (fibre_set \<B>) c a1 a2 I \<and>
                     (\<exists>g\<in>carrier (UP (SA m)).
                         deg (SA m) g \<le> Suc d \<and>
                         (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f) \<and>
                         (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                         (\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                              taylor_expansion (SA m) c g i
                              \<in> Units (SA m))))"
      by auto 
  qed
  then obtain S0 where S0_def: "is_cell_decomp m S0 (condition_to_set \<C>) \<and>
           (\<forall>\<B>\<in>S0. \<B> = Cond m (fibre_set \<B>) c a1 a2 I \<and>
                   (\<exists>g\<in>carrier (UP (SA m)).
                       deg (SA m) g \<le> Suc d \<and>
                       (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                              SA_poly_to_Qp_poly m x g =
                              SA_poly_to_Qp_poly m x f) \<and>
                       (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                       (\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                            taylor_expansion (SA m) c g i
                            \<in> Units (SA m))))"
    by blast 
  show ?thesis 
  proof(rule refine_each_cell[of m S0]) 
    show "is_cell_decomp m S0 (condition_to_set \<C>)"
      using S0_def by auto 
    fix C assume A: "C \<in> S0"
    show "\<exists>S. is_cell_decomp m S (condition_to_set C) \<and>
             (\<forall>\<B>\<in>S. \<exists>g\<in>carrier (UP (SA m)).
                        center \<B> = c \<and>
                        (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f) \<and>
                        (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                               SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                        common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m \<and>
                        ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) \<or>
                         denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n))"
    proof- 
      obtain g where g_def: "g\<in>carrier (UP (SA m)) \<and>
                       deg (SA m) g \<le> Suc d \<and>
                       (\<forall>x t. t # x \<in> condition_to_set C \<longrightarrow>
                              SA_poly_to_Qp_poly m x g =
                              SA_poly_to_Qp_poly m x f) \<and>
                       (\<forall>x t. t # x \<in> condition_to_set C \<longrightarrow>
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                              SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                       (\<forall>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                            taylor_expansion (SA m) c g i
                            \<in> Units (SA m))"
        using A S0_def by auto 
      have  "\<exists>N. SA_poly_ubounded p m f c (condition_to_set C) N"
        using assms A S0_def SA_poly_ubounded_mono  by (meson is_cell_decomp_subset)
      hence C_bounded: "\<exists>N. SA_poly_ubounded p m g c (condition_to_set C) N"
        using g_def SA_poly_uboundedI SA_poly_uboundedE 
        by (metis SA_poly_uboundedE' SA_poly_ubounded_facts(2) SA_poly_ubounded_facts(3))
      interpret A: common_refinement_locale _ _ _ _ _ C "fibre_set C" c a1 a2 I g
        using g_def A S0_def 
           apply (metis common_decomp_proof_context_axioms common_refinement_locale.intro 
            common_refinement_locale_axioms_def is_cell_decompE(3))
        unfolding \<iota>_def Z\<^sub>p_def Q\<^sub>p_def by auto 
      obtain S2 where S2_def: "is_cell_decomp m S2 (condition_to_set C) \<and> (\<forall> \<B> \<in> S2. center \<B> = c \<and> A.has_minimal_i \<B>)"
        using A.\<C>_comp_minimal_i_decomp by auto
      obtain S where S_def0: "S = S2 - {\<B> \<in> S2. condition_to_set \<B> = {}}"
        by auto 
      have f: "\<Union> (condition_to_set ` S2) = \<Union> (condition_to_set ` S)"
        unfolding S_def0 by auto 
      have "is_cell_decomp m S (condition_to_set C)"
        unfolding S_def0
        apply(intro is_cell_decompI is_partitionI disjointI)
        using S2_def 
        apply (meson finite_Diff is_cell_decompE(1))
        using S2_def is_cell_decompE(5) apply fastforce
        using S2_def is_cell_decompE(2)[of m S2 "condition_to_set C"] 
              is_partitionE(2)[of "condition_to_set ` S2" "condition_to_set C"]
        unfolding f S_def0 apply auto[1] 
        using S2_def is_cell_decompE apply auto[1]
        using A S0_def is_cell_decompE apply (metis cell_subset condition_to_set.simps)
        using A S2_def is_cell_decomp_def[of m S2 "condition_to_set C"] by blast
      hence  S_def: "is_cell_decomp m S (condition_to_set C) \<and> (\<forall> \<B> \<in> S. center \<B> = c \<and> A.has_minimal_i \<B>)"
        using S2_def S_def0 by auto 
      have " (\<forall>\<B>\<in>S. \<exists>g\<in>carrier (UP (SA m)).
                   center \<B> = c \<and>
                   (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f) \<and>
                   (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                          SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
                   common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m \<and>
                   ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) \<or>
                    denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n))"
      proof
        fix \<B> assume A: "\<B> \<in> S"
        have subset: "condition_to_set \<B> \<subseteq> condition_to_set C" 
          using A S_def is_cell_decomp_subset by blast
        hence a: "(\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f) \<and>
            (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                   SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f))"
          using g_def by auto 
        have c: "center \<B> = c"
          using A S_def by simp
        have b:  "g \<in> carrier (UP (SA m))"
                "deg (SA m) g \<le> Suc d"
                "\<B> = Cond m (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>)"
                "is_cell_condition \<B>"
                "\<And>i. taylor_expansion (SA m) c g i = \<zero>\<^bsub>SA m\<^esub> \<or>
                       taylor_expansion (SA m) c g i \<in> Units (SA m)"
            using g_def apply auto[1]  using g_def apply auto[1]
            using g_def c S_def A is_cell_decompE   apply (metis equal_CondI)
            using c S_def A is_cell_decompE  apply (metis )
            using g_def by auto 
        interpret  
            common_refinement_locale  _ _ _ _ _  \<B> "fibre_set \<B>" c "l_bound \<B>" 
                      "u_bound \<B>" "boundary_condition \<B>" g m
          using b common_decomp_proof_context_axioms common_refinement_locale.intro 
                common_refinement_locale_axioms_def                 
            apply presburger
            unfolding Q\<^sub>p_def Z\<^sub>p_def \<iota>_def Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
        have e: "((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) \<or>
             denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n)"
        proof(cases "(\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>)")
          case True
          then show ?thesis by auto 
        next
          case False
          have F0: "inds = {} \<Longrightarrow> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>)"
          proof-
            assume A: "inds = {}"
            show "(\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>)"
            proof(rule, rule, rule)
              fix x t assume A': "t#x \<in> condition_to_set \<B>"

              have a0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"
                using A' b 
                 apply (metis carrier_is_cell cell_condition_set_memE(1) condition_to_set_memE'(1))
                using A' b   by (simp add: cell_cond_head_closure)
              have a1: " SA_poly_to_SA_fun m g (t#x) = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
                apply(rule f_eval_formula) using a0 by auto 
              hence a2: "SA_poly_to_Qp_poly m x g \<bullet> t = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
                using SA_poly_to_SA_fun_formula g_def a0 by auto 
              have a3: "(\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i) = \<zero>"
                unfolding A by auto 
              show "SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>"
                unfolding a3 a2 by auto 
            qed
          qed
          hence F1: "inds \<noteq> {}"
            using False by auto 
          have F2: "\<exists>N. SA_poly_ubounded p m g c (condition_to_set \<B>) N"
            using SA_poly_ubounded_mono assms C_bounded subset by meson
          have F3: "has_minimal_i \<B>"
            using A S_def by auto 
          have "denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n"
          proof
            show "0 < n" " inds \<noteq> {}" "\<exists>N. SA_poly_ubounded p m g c (condition_to_set \<B>) N"
                  "has_minimal_i \<B>" "condition_to_set \<B> \<noteq> {}"
              using assms(6) F1 F2 F3 A S_def0 by auto 
          qed
          thus ?thesis by auto 
        qed
        thus "\<exists>g\<in>carrier (UP (SA m)).
            center \<B> = c \<and>
            (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f) \<and>
            (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                   SA_poly_to_Qp_poly m x (UPSA.pderiv m g) = SA_poly_to_Qp_poly m x (UPSA.pderiv m f)) \<and>
            common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m \<and>
            ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) \<or>
             denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n)"
          using g_def a c common_refinement_locale_axioms by blast
      qed
      thus ?thesis 
        using \<open>is_cell_decomp m S (condition_to_set C)\<close> by blast
    qed
  qed
qed
            
lemma is_1_preparable_singelton:
  assumes closed: "f \<in> carrier (UP (SA m))"
  assumes deg: "deg (SA m) f \<le> Suc d"
  assumes "n > 0" 
  shows "is_r_preparable m n 1 {f} (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
proof- 
  obtain S where S_def: 
        "is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
        "\<And>\<C>.  \<C> \<in> S \<Longrightarrow> \<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N"
    using denef_I assms unfolding denef_I_def denef_I_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast 
  show ?thesis
    apply(intro is_r_preparable_cell_decomp[of m S "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"]
                S_def)
  proof- 
    fix \<C> assume A: "\<C> \<in> S"
    obtain A0 c a10 a20 I0 where params: "\<C> = Cond m A0 c a10 a20 I0"
      using A S_def A condition_decomp' is_cell_decompE(4) by blast
    have \<C>_cell_cond: "is_cell_condition \<C>"
      using A S_def is_cell_decompE(3) by simp
    have c_closed: "c \<in> carrier (SA m)"
      using \<C>_cell_cond is_cell_conditionE''(5) params by blast
    obtain S' where S'_def: "is_cell_decomp m S' (condition_to_set \<C>) 
              \<and> (\<forall> \<B> \<in> S'. (\<exists>g \<in> carrier (UP (SA m)).  
                         center \<B> = c 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f) 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f))
                      \<and> common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m 
                      \<and> ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) 
                           \<or> (denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n))))"
      using common_decomp[of f m \<C> A0 c a10 a20 I0] assms \<C>_cell_cond params 
      using A S_def(2) by fastforce
    hence S'_decomp: "is_cell_decomp m S' (condition_to_set \<C>) "
      by auto 
    show "is_r_preparable m n 1 {f} (condition_to_set \<C>)"
    proof(rule is_r_preparable_cell_decomp[of _ S'], rule S'_decomp)
      fix \<B> assume B: "\<B> \<in> S'"
      obtain b where  b_def: "b = fibre_set \<B>"
        by blast 
      have \<B>_cell: "is_cell_condition \<B>"
        using B S'_def is_cell_decompE(3) by auto 
      obtain a1 a2 I where \<B>_eq: "\<B> = Cond m b c a1 a2 I"
        using B S'_def unfolding b_def 
        by (metis equal_CondI is_cell_decompE(4))
      obtain g where g_def: "g \<in> carrier (UP (SA m)) \<and> 
                         center \<B> = c 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f) 
                      \<and> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m g) =
                                SA_poly_to_Qp_poly m x (UPSA.pderiv m f))
                      \<and> common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m 
                      \<and> ((\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>) 
                           \<or> (denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n))"
        using B S'_def 
        by blast
      have l: "common_refinement_locale p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m"          
        using g_def by auto 
      have 0: "condition_to_set \<B> \<subseteq> condition_to_set \<C>"
        using A B is_cell_decomp_subset S'_decomp by auto 
      have ubounded: "\<exists>N. SA_poly_ubounded p m f (center \<B>) (condition_to_set \<B>) N"
      proof- 
        have "\<exists>N. SA_poly_ubounded p m f (center \<C>) (condition_to_set \<C>) N"
          using S_def A B  by auto 
        thus ?thesis 
          using SA_poly_ubounded_mono[of ]  0 
          unfolding params center.simps \<B>_eq by blast
      qed
      interpret common_refinement_locale _ _ _ _ _ \<B> b c a1 a2 I g
          using l unfolding \<B>_eq Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
      show "is_r_preparable m n 1 {f} (condition_to_set \<B>)"
      proof(cases "\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>")
        case True
        have T0: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow>
           t # x \<in> condition_to_set \<B> \<Longrightarrow>
           SA_poly_to_Qp_poly m x f \<bullet> t = \<zero>"
        proof- fix x t 
          assume A: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"  "t # x \<in> condition_to_set \<B>"
          have 0: "SA_poly_to_Qp_poly m x f \<bullet> t = SA_poly_to_Qp_poly m x g \<bullet> t"
            using A g_def by auto 
          have 1: "SA_poly_to_Qp_poly m x g \<bullet> t = (\<Oplus> i \<in> inds. a i x \<otimes> (t \<ominus> c x)[^]i)"
            using f_eval_formula[of x t] SA_poly_to_SA_fun_formula A by (simp add: f_closed)
          have "SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>"
            using True A by simp
          thus "SA_poly_to_Qp_poly m x f \<bullet> t = \<zero>" using 0 by auto 
        qed
        have "is_r_prepared m n 1 {f} (condition_to_set \<B>)"
        proof(rule is_r_preparedI[of _ _ "\<lambda>x. \<B>" "{\<B>}"])
          show "finite {f}"
                "{f} \<subseteq> carrier (UP (SA m))"
                "(\<lambda>x. \<B>) \<in> {f} \<rightarrow> {\<B>}"
                "card (center ` (\<lambda>x. \<B>) ` {f}) \<le> 1"
                "\<And>fa. fa \<in> {f} \<Longrightarrow> is_cell_condition \<B>"
                "\<And>fa. fa \<in> {f} \<Longrightarrow> arity \<B> = m" 
                "condition_to_set \<B> = (\<Inter>f\<in>{f}. condition_to_set \<B>)"
            using assms \<B>_cell \<B>_eq arity.simps by auto 
          have 0: "SA_poly_factors p m n f (center \<B>) (condition_to_set \<B>) \<one>\<^bsub>SA (Suc m)\<^esub> \<zero>\<^bsub>SA m\<^esub> 0"
            apply(rule SA_poly_factorsI, unfold T0) 
            using SA_oneE c_closed SA_zeroE
            unfolding \<B>_eq condition_to_set.simps cell_def by auto 
          thus "\<And>g. g \<in> {f} \<Longrightarrow>
          \<exists>u h k.
             SA_poly_factors p m n g (center \<B>) (condition_to_set \<B>) u h k"
            by auto 
        qed
        thus "is_r_preparable m n 1 {f} (condition_to_set \<B>)"
          by (simp add: is_r_prepared_imp_is_r_preparable)
      next
        case False
        have F1: "\<And> t x i. t # x \<in> condition_to_set \<B> \<longrightarrow>
                                SA_poly_to_Qp_poly m x g =
                                SA_poly_to_Qp_poly m x f"
          using g_def by auto 
        obtain N where N_def: "SA_poly_ubounded p m f (center \<B>) (condition_to_set \<B>) N"
            using ubounded by auto 
        have b: "SA_poly_ubounded p m g c (condition_to_set \<B>) N"
          apply(rule SA_poly_uboundedI)
          using g_def apply auto[1]
          using \<B>_eq center.simps c_closed apply auto[1]
          unfolding F1 using N_def g_def
            SA_poly_uboundedE'[of m f c "condition_to_set \<B>" N]
          unfolding \<B>_eq condition_to_set.simps cell_def mem_Collect_eq 
          by auto 
        have c: "inds \<noteq> {}"
        proof- 
          have F0: "inds = {} \<Longrightarrow> (\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>)"
          proof-
            assume A: "inds = {}"
            show "(\<forall>x t. t # x \<in> condition_to_set \<B> \<longrightarrow> SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>)"
            proof(rule, rule, rule)
              fix x t assume A': "t#x \<in> condition_to_set \<B>"
              have a0: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p"
                using A' \<B>_eq 
                apply (metis \<B>_cell carrier_is_cell cell_condition_set_memE(1) condition_to_set_memE'(1))                
                using A' b   by (simp add: cell_cond_head_closure)
              have a1: " SA_poly_to_SA_fun m g (t#x) = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
                apply(rule f_eval_formula) using a0 by auto 
              hence a2: "SA_poly_to_Qp_poly m x g \<bullet> t = (\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i)"
                using SA_poly_to_SA_fun_formula g_def a0 by auto 
              have a3: "(\<Oplus>i\<in>inds. (a i x)\<otimes>(t \<ominus> c x)[^]i) = \<zero>"
                unfolding A by auto 
              show "SA_poly_to_Qp_poly m x g \<bullet> t = \<zero>"
                unfolding a3 a2 by auto 
            qed
          qed
          thus ?thesis using False by auto 
        qed
        have "denef_II_base p d \<B> (fibre_set \<B>) c (l_bound \<B>) (u_bound \<B>) (boundary_condition \<B>) g m n"
          using g_def False by auto 
        then interpret denef_II_base _ _ _ _ _ \<B> b c a1 a2 I g
          using S'_def B \<B>_eq False Q\<^sub>p_def Z\<^sub>p_def \<iota>_def by auto 
        obtain S where S_def: "is_cell_decomp m S (condition_to_set \<B>)"
     "\<forall> \<D> \<in> S. \<exists>u h k. SA_poly_factors p m n g (center \<D>) (condition_to_set \<D>) u h k"
          using denef_II_base_cell_decomp by auto 
        have F2: "(\<forall> \<D> \<in> S. \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k)"
        proof- 
          have a0: "\<forall>\<D> \<in> S. condition_to_set \<D> \<subseteq> condition_to_set \<B>"
            using is_cell_decomp_subset S_def by blast 
          have a1: "\<And> \<D>. \<And> t x. t#x \<in> condition_to_set \<D> \<Longrightarrow> \<D> \<in> S \<Longrightarrow>  
                      SA_poly_to_Qp_poly m x g = SA_poly_to_Qp_poly m x f"
            using a0 g_def by auto 
          have a2: "\<And> \<D>. \<D> \<in> S \<Longrightarrow>
                   \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k"
          proof- 
            fix \<D> assume A: "\<D> \<in> S"
            obtain u h k where  defs: "SA_poly_factors p m n g(center \<D>) (condition_to_set \<D>) u h k"
              using S_def A by blast 
            have 1: " \<And> t x. t#x \<in> condition_to_set \<D> \<Longrightarrow>   
                      SA_poly_to_Qp_poly m x f = SA_poly_to_Qp_poly m x g"
              using a1 A by auto 
            have 2: "condition_to_set \<D> \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
              using A S_def is_cell_decompE 
              by (meson SA_poly_factors_closure(1))              
            have "SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k"
              apply(rule SA_poly_factorsI)
              using defs  a1   2 SA_poly_factors_closure
                      SA_poly_factorsE[of m n g "center \<D>" "condition_to_set \<D>" u h k ]
               unfolding 1 by  auto 
             thus " \<exists>u h k. SA_poly_factors p m n f (center \<D>) (condition_to_set \<D>) u h k"
               by auto 
          qed
          thus ?thesis by auto 
        qed
        show "is_r_preparable m n 1 {f} (condition_to_set \<B>)"
        proof(rule is_r_preparable_cell_decomp[of m S], rule S_def, 
              rule is_r_prepared_imp_is_r_preparable)
          fix \<C> assume A: "\<C> \<in> S"
          show "is_r_prepared m n 1 {f} (condition_to_set \<C>)"
            apply(rule is_r_preparedI[of _ _ "\<lambda> f. \<C>" "{\<C>}"])
            using A closed F2 is_cell_decompE S_def by auto 
        qed
      qed
    qed
  qed
qed

definition refine_fibres_2 where 
"refine_fibres_2 \<C> A = refine_fibres \<C> (A \<inter> fibre_set \<C>)"

lemma refine_fibres_2_is_cell:
  assumes "\<C> = Cond m C c a1 a2 I"
  assumes "is_cell_condition \<C>"
  assumes "is_semialgebraic m A"
  shows "is_cell_condition (refine_fibres_2 \<C> A)"
  unfolding refine_fibres_2_def  
  using assms  
  by (metis fibre_set.simps intersection_is_semialg is_cell_conditionE(1) mem_simps(4) refine_fibres_is_cell subsetI)

lemma refine_fibres_2_is_cell':
  assumes "arity \<C> = m"
  assumes "is_cell_condition \<C>"
  assumes "is_semialgebraic m A"
  shows "is_cell_condition (refine_fibres_2 \<C> A)"
  apply(rule refine_fibres_2_is_cell[of _ "arity \<C>" "fibre_set \<C>" "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>"])
    apply(rule condition_decomp', rule assms)
  unfolding assms by(rule assms)

lemma refine_fibres_2_subset: 
"condition_to_set (refine_fibres_2 \<C> A) \<subseteq> condition_to_set \<C>"
proof-
  obtain m C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using  arity.simps condition_decomp' by blast
  show ?thesis
    unfolding refine_fibres_def refine_fibres_2_def params condition_to_set.simps cell_def 
      arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
  apply(rule subsetI) unfolding mem_Collect_eq by blast
qed

lemma refine_fibres_2_partition: 
  assumes "A \<inter> B = {}"
  shows "condition_to_set (refine_fibres_2 \<C> A) \<inter> condition_to_set (refine_fibres_2 \<C> B) = {}"
proof- 
  have "fibre_set (refine_fibres_2 \<C> A) \<inter> fibre_set (refine_fibres_2 \<C> B) = {}"
    unfolding refine_fibres_2_def using assms 
    by auto
  then show ?thesis 
    by (metis disj_fibres_imp_disj_cells equal_CondI)
qed

lemma refine_fibres_2E: 
  assumes "\<C> = Cond m C c a1 a2 I"
  shows "refine_fibres_2 \<C> A = Cond m (C \<inter> A) c a1 a2 I"
  unfolding refine_fibres_2_def refine_fibres_def assms 
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
  by blast 

lemma refine_fibres_2_covers: 
  assumes "A \<union> B = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  assumes "arity \<C> = m"
  assumes "is_cell_condition \<C>"
  shows "condition_to_set (refine_fibres_2 \<C> A) \<union> condition_to_set (refine_fibres_2 \<C> B) = condition_to_set \<C>"
proof- 
  obtain C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  have 0: "C = (A \<inter> C) \<union> (B \<inter> C)"
    using assms is_cell_conditionE(1)[of m C c a1 a2 I] is_semialgebraic_closed[of m C]
    unfolding params by blast 
  show ?thesis 
  unfolding params refine_fibres_2_def refine_fibres_def assms 
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    condition_to_set.simps cell_def using 0 by blast 
qed

lemma refine_fibres_2_inter:
  shows "condition_to_set (refine_fibres_2 \<C> A) \<inter> condition_to_set (refine_fibres_2 \<C> B) = condition_to_set (refine_fibres_2 \<C> (A \<inter> B)) "
proof-
  obtain m C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using  arity.simps condition_decomp' by blast
  show ?thesis 
  unfolding params refine_fibres_2_def refine_fibres_def  
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    condition_to_set.simps cell_def by blast 
qed

lemma refine_fibres_2_diff:
  shows "condition_to_set (refine_fibres_2 \<C> A) - condition_to_set (refine_fibres_2 \<C> B) = condition_to_set (refine_fibres_2 \<C> (A - B)) "
proof-
  obtain m C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using  arity.simps condition_decomp' by blast
  show ?thesis 
  unfolding params refine_fibres_2_def refine_fibres_def  
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    condition_to_set.simps cell_def by blast 
qed

lemma refine_fibres_2_union:
  shows "condition_to_set (refine_fibres_2 \<C> A) \<union> condition_to_set (refine_fibres_2 \<C> B) = condition_to_set (refine_fibres_2 \<C> (A \<union> B)) "
proof-
  obtain m C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using  arity.simps condition_decomp' by blast
  show ?thesis 
  unfolding params refine_fibres_2_def refine_fibres_def  
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    condition_to_set.simps cell_def by blast 
qed

lemma refine_fibres_2_params:
"arity (refine_fibres_2 \<C> A) = arity \<C>"
"center (refine_fibres_2 \<C> A) = center \<C>"
"u_bound (refine_fibres_2 \<C> A) = u_bound \<C>"
"l_bound (refine_fibres_2 \<C> A) = l_bound \<C>"
"boundary_condition (refine_fibres_2 \<C> A) = boundary_condition \<C>" 
"fibre_set  (refine_fibres_2 \<C> A) = A \<inter>fibre_set \<C>"
  unfolding  refine_fibres_2_def refine_fibres_def  
    arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    condition_to_set.simps cell_def 
     apply blast 
    apply blast
   apply blast
  apply blast
 apply blast
by blast 

lemma SA_eq_set_is_semialg:
  assumes "a \<in> carrier (SA m)"
  assumes "b \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = b x}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = b x} = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (a \<ominus>\<^bsub>SA m\<^esub> b) x = \<zero>}"
    apply(rule equalityI')
    unfolding mem_Collect_eq using assms Qp.r_right_minus_eq SA_car_closed SA_minus_eval apply presburger
    using assms Qp.r_right_minus_eq SA_car_closed SA_minus_eval 
    by metis
  have 1: "(a \<ominus>\<^bsub>SA m\<^esub> b) \<in> carrier (SA m)"
    by(rule R.ring_simprules, rule assms, rule assms)
  show ?thesis unfolding 0 
    using  1 SA_zero_set_is_semialg by presburger
qed

lemma SA_ineq_set_is_semialg:
  assumes "a \<in> carrier (SA m)"
  assumes "b \<in> carrier (SA m)"
  shows "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x \<noteq> b x}"
proof-
  have 0: "{x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x \<noteq> b x} = carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). a x = b x}"
    by blast 
  show ?thesis unfolding 0 
  using SA_eq_set_is_semialg assms complement_is_semialg by blast 
qed

lemma refine_fibres_2_disjoint:
  assumes "A \<inter> B = {}"
  shows "condition_to_set (refine_fibres_2 \<A> A) \<inter> condition_to_set (refine_fibres_2 \<B> B) = {}"
  apply(rule equalityI')
  unfolding refine_fibres_def refine_fibres_2_def  condition_to_set.simps cell_def mem_Collect_eq Int_iff
  using assms apply blast
  by blast 

lemma refine_fibres_2_memI:
  assumes "x \<in> condition_to_set \<C>"
  assumes "tl x \<in> A"
  shows "x \<in> condition_to_set (refine_fibres_2 \<C> A)"
proof-
  obtain m C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using  arity.simps condition_decomp' by blast
  have 0: "refine_fibres_2 \<C> A = Cond m (C \<inter> A) c a1 a2 I"
    using refine_fibres_2E[of \<C> m C c a1 a2 I A] params by blast 
  show ?thesis 
    using assms unfolding 0 unfolding params condition_to_set.simps cell_def mem_Collect_eq by blast 
qed

lemma condition_to_set_memE:
  assumes "x \<in> condition_to_set \<C>"
  assumes "arity \<C> = m"
  shows "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
proof-
  obtain C c a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  show 0: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using assms unfolding params condition_to_set.simps cell_def by blast 
  show 1: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using 0 Qp_pow_ConsE(1) by blast
qed

definition change_center where 
"change_center c \<C>  = Cond (arity \<C>) (fibre_set \<C>) c (l_bound \<C>) (u_bound \<C>) (boundary_condition \<C>)"

lemma change_centerE: 
"change_center c (Cond m C c0 a1 a2 I) = Cond m C c a1 a2 I"
  unfolding change_center_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
  by blast 

lemma change_center_params: 
"arity (change_center c \<C> ) = arity \<C>"
"fibre_set (change_center c \<C> ) = fibre_set  \<C>"
"center (change_center c \<C> ) = c"
"l_bound (change_center c \<C> ) = l_bound  \<C>"
"u_bound  (change_center c \<C> ) = u_bound  \<C>"
"boundary_condition (change_center c \<C> ) = boundary_condition \<C>"
  unfolding change_center_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
       apply blast
      apply blast
     apply blast
    apply blast
  apply blast
  by blast 

lemma change_center_equal_set: 
  assumes "\<And>x. x \<in> (fibre_set \<C>) \<Longrightarrow> c x = center \<C> x"
  shows "condition_to_set (change_center c \<C> ) = condition_to_set \<C>"
proof- 
 obtain m C c' a1 a2 I where params: "\<C> = Cond m C c' a1 a2 I"
    using assms arity.simps condition_decomp' by blast
  show "condition_to_set (change_center c \<C> ) = condition_to_set \<C>"

    apply(rule equalityI')
    using assms 
    unfolding params change_center_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    unfolding condition_to_set.simps cell_def mem_Collect_eq apply metis
    using assms 
    unfolding params change_center_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
    unfolding condition_to_set.simps cell_def mem_Collect_eq by metis
qed

lemma change_center_cell_cond:
  assumes "is_cell_condition \<C>"
  assumes "arity \<C> = m"
  assumes "c \<in> carrier (SA m)"
  shows "is_cell_condition (change_center c \<C> )"
  unfolding change_center_def apply(rule is_cell_conditionI)
  unfolding arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
  using assms is_cell_conditionE' apply blast
  using assms is_cell_conditionE apply blast
  using assms condition_decomp'[of \<C>] 
        is_cell_conditionE(3)[of "arity \<C>" "fibre_set \<C>" "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>"] 
  using is_cell_conditionE''(6) apply blast
    using assms condition_decomp'[of \<C>] 
        is_cell_conditionE(3)[of "arity \<C>" "fibre_set \<C>" "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>"] 
  using is_cell_conditionE''(7) apply blast
      using assms condition_decomp'[of \<C>] 
        is_cell_conditionE(3)[of "arity \<C>" "fibre_set \<C>" "center \<C>" "l_bound \<C>" "u_bound \<C>" "boundary_condition \<C>"] 
  using is_cell_conditionE''(8) by blast

lemma SA_poly_factors_subset: 
  assumes "(\<exists>u h k. SA_poly_factors p m n f c A u h k)"
  assumes "B \<subseteq> A"
  shows "(\<exists>u h k. SA_poly_factors p m n f c B u h k)"
proof-
  obtain u h k where def: "SA_poly_factors p m n f c A u h k"
    using assms by blast 
  have "SA_poly_factors p m n f c B u h k"
    using def assms(2) unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def by blast 
  thus ?thesis by blast 
qed

lemma SA_poly_factors_center_eq: 
  assumes "(\<exists>u h k. SA_poly_factors p m n f c A u h k)"
  assumes "\<And>t x. t#x \<in> A \<Longrightarrow> c' x = c x"
  assumes "c' \<in> carrier (SA m)"
  shows  "(\<exists>u h k. SA_poly_factors p m n f c' A u h k)"
proof-
  obtain u h k where def: "SA_poly_factors p m n f c A u h k"
    using assms by blast 
  have "SA_poly_factors p m n f c' A u h k"
    apply(rule SA_poly_factorsI)

    using def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  apply blast
    using def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  apply blast
    using assms apply blast
    using def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  apply blast
    using def assms unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  assms 
    by presburger   
  thus ?thesis by blast 
qed

lemma equal_val_quotient:
  assumes "val a = val b"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "val (a\<div>b) = 0"
  using assms val_ord ord_mult 
  by (smt (verit, ccfv_threshold) Qp.nonzero_memE(1) eint_diff_imp_eint equal_val_imp_equal_ord(1) 
      fract_closed local.fract_cancel_left val_mult zero_eint_def)

lemma val_root: 
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a = 0"
  assumes "u \<in> carrier Q\<^sub>p"
  assumes "a = u[^](n::nat)"
  assumes "n > 0"
  shows "val u = 0"
proof- 
  have 0: "u \<in> nonzero Q\<^sub>p"
    apply(rule nonzero_memI, rule assms)
    using assms 
    by (metis Qp.cring_simprules(6) Qp.one_not_zero Qp.pow_zero eint_ord_simps(3) local.val_zero val_ineq val_one)
  have 1: "ord a = 0"
    using assms val_ord Qp.nonzero_one_closed equal_val_imp_equal_ord(1) ord_one val_one 
    by metis
  have 2: "ord a = n*ord u"
    using 0 1 val_ord 
    using assms(4) nonzero_nat_pow_ord by blast
  have 3: "ord u = 0"
    using 2 unfolding 1 using assms 
    by (metis less_numeral_extra(3) no_zero_divisors of_nat_0_eq_iff)
  then show ?thesis
    using 0 val_ord eint_defs(1) by presburger
qed

lemma Case_i: 
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes " t \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  assumes " c2 \<in> carrier Q\<^sub>p" 
  assumes "c1 \<noteq> c2"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<ge> N"
  assumes " n> 0"
  shows "\<exists>u \<in> carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c2 = \<ominus>(c2 \<ominus> c1)\<otimes>(u[^]n)"
proof-
  have N_pos: "N > 1"
    using assms by blast 
  have N_fact: "\<And>u. u \<in> carrier Q\<^sub>p \<Longrightarrow> ac N u = 1 \<Longrightarrow> val u = 0 \<Longrightarrow> u \<in> P_set n"
    using assms by blast 
  have 0: "t \<ominus> c2 = t \<ominus> c1 \<ominus> (c2 \<ominus> c1)"
    using assms unfolding a_minus_def 
    using Qp.minus_eq Qp_diff_diff by presburger
  have diff_nonzero: "c2 \<ominus> c1 \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 1: "t \<ominus> c2 = (c2 \<ominus> c1) \<otimes> (((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<ominus> \<one>)"
    unfolding 0  using diff_nonzero assms 
    by (metis (no_types, lifting) Qp.cring_simprules(4) Qp.one_closed Qp.r_minus_distr Qp.r_one fract_closed local.fract_cancel_right)
  have c0: "((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<in> carrier Q\<^sub>p"
    using diff_nonzero assms 
    by (meson Qp.cring_simprules(4) fract_closed)
  have R0: "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> val x \<ge> N \<Longrightarrow> \<exists>u \<in> carrier Q\<^sub>p. val u = 0 \<and> (x \<ominus> \<one>) = \<ominus> (u[^]n)"
  proof- fix x assume a: "x \<in> carrier Q\<^sub>p" " val x \<ge> N"
    have 0: "(\<one> \<ominus> x) \<ominus> \<one> = \<ominus> x"
      using a unfolding a_minus_def 
      using Qp.a_ac(2) Qp.add.m_closed Qp.cring_simprules(19) Qp.cring_simprules(3) Qp.one_closed by presburger
    have 1: "val (\<ominus>x) = val x"
      using a val_minus by presburger
    have 2: "val ((\<one> \<ominus> x) \<ominus> \<one>) \<ge> N"
      unfolding 0 1 by(rule a) 
    have 3: "val \<one> < val x"
      unfolding val_one using a N_pos 
      by (metis (mono_tags, opaque_lifting) Suc_le_lessD dec_induct eint_ord_trans eint_pow_int_is_pos less_nat_zero_code not_less_eq_eq notin_closed of_nat_0_less_iff rel_simps(69) val_of_nat_inc val_ring_int_inc_closed val_val_ring_prod)
    have 4: "val (\<one> \<ominus> x) = val \<one>"
      using a 3 val_ultrametric_noteq'' by blast
    have 5: "ac N (\<one> \<ominus> x) = ac N \<one>"
      apply(rule ac_val)
      using a 4  Qp.cring_simprules(4) Qp.cring_simprules(6) Qp.nonzero_one_closed equal_val_imp_equal_ord(2) apply presburger
      using Qp.nonzero_one_closed apply linarith
       apply(rule 4)
      unfolding 4 val_one  0 1 using a 
      by (metis add.left_neutral)
    have 6: "\<one> \<ominus> x \<in> P_set n"
      apply(rule N_fact)
      using a apply blast
      using 5 ac_one N_pos less_imp_le_nat apply presburger
      unfolding 4 val_one by blast 
    then obtain u where u_def: "u \<in> carrier Q\<^sub>p \<and> \<one>\<ominus>x = u[^]n"
      unfolding P_set_def mem_Collect_eq by blast 
    have 7: "val u = 0"
      apply(rule val_root[of "\<one> \<ominus> x" _ n])
      using a apply blast
      unfolding 4 val_one apply blast
      using u_def apply blast
      using u_def apply blast
      by(rule assms)
    have 8: "x \<ominus> \<one> = \<ominus> (\<one> \<ominus> x)"
      using a Qp.minus_a_inv by blast
    have 9: "\<one>\<ominus>x = u[^]n"
      using u_def by blast 
    have 10: "x \<ominus> \<one> = \<ominus> (u [^] n)"
      unfolding 8 9 by blast 
    show " \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> x \<ominus> \<one> = \<ominus> (u [^] n)"
      using u_def 7 10 by blast 
  qed
  have " \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> (t \<ominus> c1 \<div> c2 \<ominus> c1) \<ominus> \<one> = \<ominus> (u [^] n)"
    by(rule R0[of "(t \<ominus> c1) \<div> (c2 \<ominus> c1)" ], rule c0, rule assms )
  then obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (t \<ominus> c1 \<div> c2 \<ominus> c1) \<ominus> \<one> = \<ominus> (u [^] n)"
    by blast 
  have 2: "(t \<ominus> c1 \<div> c2 \<ominus> c1) \<ominus> \<one> = \<ominus> (u [^] n)"
    using u_def by blast 
  have 3: " t \<ominus> c2 = (c2 \<ominus> c1) \<otimes> \<ominus>( u [^] n)"
    unfolding 1 2  by blast 
  have R1: "\<And>a b. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> a \<otimes> (\<ominus> b) = (\<ominus> a)\<otimes>b"
    using Qp.cring_simprules(28) Qp.cring_simprules(29) by presburger
  have 4: "(c2 \<ominus> c1) \<otimes> (\<ominus>  (u [^] n)) = (\<ominus>(c2 \<ominus> c1)) \<otimes> (u [^] n)"
    apply(rule R1) using assms apply blast
    using u_def by blast 
  have 5: "t \<ominus> c2 = \<ominus> (c2 \<ominus> c1) \<otimes> u [^] n"
    unfolding 3 4 by blast 
  show " \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c2 = \<ominus> (c2 \<ominus> c1) \<otimes> u [^] n"
    using u_def 5 by blast 
qed

lemma Case_ii: 
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes " t \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  assumes " c2 \<in> carrier Q\<^sub>p" 
  assumes "c1 \<noteq> c2"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) < eint (-N)"
  assumes " n> 0"
  shows "\<exists>u \<in> carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c2 = (t \<ominus> c1) \<otimes> u [^] n" 
proof- 
  have 0: "(c2 \<ominus> c1) \<in> nonzero Q\<^sub>p"
    using assms  Qp.not_eq_diff_nonzero by blast
  have 1: "(t \<ominus> c1) \<in> nonzero Q\<^sub>p"
    using assms 0 
    by (metis P_set_mult_closed P_set_of_one Qp.cring_simprules(4) fract_closed less_irrefl_nat less_one local.fract_cancel_left val_nonzero)
  have 2: "ord ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) = ord (t \<ominus> c1) - ord (c2 \<ominus> c1 )"
    using 0 1 ord_fract by presburger
  have 3: "ord ((c2 \<ominus> c1)\<div>(t \<ominus> c1)) = ord (c2 \<ominus> c1) - ord (t \<ominus> c1)"
    using 0 1 ord_fract 2 by presburger
  have 4: "t \<ominus> c2 = t \<ominus> c1 \<ominus> (c2 \<ominus> c1)"
    using assms Qp_diff_diff by presburger
  have 5: "ord ((c2 \<ominus> c1)\<div>(t \<ominus> c1)) > N"
  proof-
    have "ord ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) < -N"
      using 0 1 assms 
      by (metis Qp.nonzero_mult_closed eint_ord_code(2) nonzero_inverse_Qp val_nonzero val_ord)
    then show ?thesis 
      using assms val_ord 2 3 
      by linarith
  qed
  have 6: "val ((c2 \<ominus> c1)\<div>(t \<ominus> c1)) > N"
    using 5 0 1 3 Qp.nonzero_closed eint_ord_simps(2) idiff_eint_eint val_fract val_ord by presburger
  have 7: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> c2 \<ominus> t = \<ominus> (t \<ominus> c1) \<otimes> u [^] n" 
    apply(rule Case_i[of N n c2 c1 t])
    using assms apply blast
    using assms apply blast
    using assms apply blast
    using assms apply blast
    using assms(2) assms(3) 1 unfolding mem_Collect_eq nonzero_def 
    using Qp.r_right_minus_eq apply blast
    using 5 
    apply (metis (mono_tags, opaque_lifting) "6" diff_gt_0_iff_gt diff_less_0_iff_less eint_ord_simps(2) less_eintE not_less0 notin_closed of_nat_0 of_nat_less_iff pos_int_cases)
    by(rule assms)
  then obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> c2 \<ominus> t = \<ominus> (t \<ominus> c1) \<otimes> u [^] n" 
    by blast 
  have 8: "t \<ominus> c2 = (t \<ominus> c1) \<otimes> u [^] n" 
    using u_def assms 
    by (smt Qp.cring_simprules(28) Qp.cring_simprules(4) Qp.minus_a_inv Qp.nat_pow_closed)
  show ?thesis using 8 u_def by blast 
qed

lemma equation_6: 
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "b \<noteq> a"
  shows "(\<pp>[^](N::nat) \<div> (b \<ominus> a)) \<otimes> (t \<ominus> a) = (\<pp>[^]N \<div> (b \<ominus> a)) \<otimes> (t \<ominus> b) \<oplus> \<pp>[^]N"
proof- 
  have 0: "b \<ominus> a \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 1: "\<pp> [^] N = ((\<pp> [^] N \<otimes> (b \<ominus> a)) \<div> (b \<ominus> a))"
    using 0 assms Qp.cring_simprules(11) Qp.cring_simprules(24) Qp.nonzero_memE(1) local.fract_cancel_right nonzero_inverse_Qp p_natpow_closed(1) 
    by presburger
  have 2: "(\<pp> [^] N \<div> b \<ominus> a) \<otimes> (t \<ominus> b) = (((\<pp> [^] N) \<otimes> (t \<ominus> b))  \<div> (b \<ominus> a)) "
    using 0 assms Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.cring_simprules(4) Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1)
    by (metis (no_types, lifting))
  have 3: "(\<pp> [^] N \<div> b \<ominus> a) \<otimes> (t \<ominus> b) \<oplus> \<pp> [^] N = (((\<pp> [^] N) \<otimes> (t \<ominus> b))  \<div> (b \<ominus> a)) \<oplus>  ((\<pp> [^] N \<otimes> (b \<ominus> a)) \<div> (b \<ominus> a))"
    using assms 1 unfolding 2 by presburger
  have 4: "(\<pp> [^] N \<div> b \<ominus> a) \<otimes> (t \<ominus> b) \<oplus> \<pp> [^] N = (((\<pp> [^] N) \<otimes> (t \<ominus> b) \<oplus> (\<pp> [^] N \<otimes> (b \<ominus> a))) \<div> (b \<ominus> a))"
    unfolding 3 
    using assms 0 1  Qp.cring_simprules(13) Qp.cring_simprules(4) Qp.m_closed Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1)
    by presburger
  have 5: "((\<pp> [^] N) \<otimes> (t \<ominus> b) \<oplus> (\<pp> [^] N \<otimes> (b \<ominus> a))) = ((\<pp> [^] N) \<otimes> ((t \<ominus> b) \<oplus> (b \<ominus> a)))"
    using assms Qp.cring_simprules(25) Qp.minus_closed p_natpow_closed(1) by presburger
  have 6: "((\<pp> [^] N) \<otimes> (t \<ominus> b) \<oplus> (\<pp> [^] N \<otimes> (b \<ominus> a))) = (\<pp> [^] N) \<otimes> (t \<ominus> a)"
    unfolding 5 using assms Qp.a_ac(2) Qp.minus_closed Qp.plus_diff_simp by presburger
  show "(\<pp> [^] N \<div> b \<ominus> a) \<otimes> (t \<ominus> a) = (\<pp> [^] N \<div> b \<ominus> a) \<otimes> (t \<ominus> b) \<oplus> \<pp> [^] N"
    unfolding 4 6 using assms 0 
    by (smt Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.minus_closed Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1))
qed

lemma equation_6_alt:
  assumes "t \<in> carrier Q\<^sub>p"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "b \<noteq> a"
  shows "(\<pp>[^](N::nat) \<div> (b \<ominus> a)) \<otimes> (t \<ominus> c) = \<pp>[^](N::nat) \<otimes> ((t \<ominus> c) \<div> (b \<ominus> a))"
proof-
  have 0: "b \<ominus> a \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 1: "t \<ominus> c \<in> carrier Q\<^sub>p"
    using assms by blast 
  show ?thesis 
    using Qp.m_comm[of "inv (b \<ominus> a)" "t \<ominus> c" ] Qp.m_assoc[of "\<pp>[^]N" "inv (b \<ominus> a)" "t \<ominus> c"] 0 1 
    using Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1) by presburger
qed

lemma ac_div_1: 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "N > 0"
  assumes "ac N a = ac N b"
  shows "ac N (a \<div> b) = 1"
  using assms ac_inv[of b N] ac_units[of a N]
  by (metis ac_inv'''(1) ac_of_fraction)

lemma Case_iii: 
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes " t \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  assumes " c2 \<in> carrier Q\<^sub>p" 
  assumes "c1 \<noteq> c2"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<ge> eint (-N)" 
  assumes "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (2*N) = 0"
  assumes " n> 0"
  shows "\<exists>u \<in> carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 = (c2 \<ominus> c1) \<otimes> u [^] n" 
proof-
  have n: "(c2 \<ominus> c1) \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 0: "((t \<ominus> c1)\<div> (c2 \<ominus> c1)) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 00: "(t \<ominus> c2 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 1: "val ((\<pp>[^]N)\<otimes>((t \<ominus> c1)\<div> (c2 \<ominus> c1))) = val (\<pp>[^]N) + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
    using val_mult 0  p_natpow_closed(1) by blast
  have 2: "val (\<pp>[^]N) = N"
    by (metis int_pow_int val_p_int_pow)
  obtain A where A_def: "A = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c1)"
    by blast 
  have A_closed: "A \<in> carrier Q\<^sub>p"
    unfolding A_def using assms 0  Qp.cring_simprules(5) equation_6_alt p_natpow_closed(1) by presburger
  obtain B where B_def: "B = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c2)"
    by blast 
  have B_closed: "B \<in> carrier Q\<^sub>p"
    unfolding B_def 
    using assms Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.r_right_minus_eq field_inv(3) p_natpow_closed(1) by presburger
  have D_dlt: "A = (\<pp> [^] N ) \<otimes> (t \<ominus> c1 \<div> c2 \<ominus> c1)"
    unfolding A_def using equation_6_alt assms by presburger
  have B_alt: "B = (\<pp> [^] N ) \<otimes> (t \<ominus> c2\<div> c2 \<ominus> c1)"
    unfolding B_def using equation_6_alt assms by presburger
  obtain C where C_def: "C = \<pp>[^]N"
    by blast 
  have val_C: "val C = N"
    unfolding C_def using "2" by blast
  have C_closed: "C \<in> carrier Q\<^sub>p"
    unfolding C_def by blast 
  have 3: "A = B \<oplus> C" 
    unfolding A_def B_def C_def equation_6 assms 
    by (metis Qp.not_nonzero_memI Qp.r_right_minus_eq assms(2) assms(3) assms(4) equation_6 n)
  have 4: "B = A \<ominus> C"
    unfolding 3 using  Qp.ring_simprules B_closed C_closed 
    by presburger
  have 7: "A \<in> \<O>\<^sub>p"
  proof-
    have 50: "val A = N + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
      using 0 C_closed val_C val_mult[of "\<pp> [^] N" "(t \<ominus> c1)\<div> (c2 \<ominus> c1)"] 0
      unfolding 2 C_def D_dlt by blast 
    have 51: "val A \<ge> N + eint (-N)"
      unfolding 50 using assms 
      by (metis "2" C_closed C_def Qp.add.nat_pow_eone Qp.l_one Qp.one_closed eint_add_mono int_add_pow val_ring_int_inc_closed val_val_ring_prod)
    hence 52: "val A \<ge> 0"
      by (metis add.right_inverse eint_defs(1) plus_eint_simps(1))
    show ?thesis using A_closed 52 val_ring_memI
      by blast 
  qed
  have 6: "C \<in> \<O>\<^sub>p"
    unfolding C_def 
    using val_ring_int_inc_closed val_ring_nat_pow_closed by blast
  have 5: "B \<in> \<O>\<^sub>p"
    unfolding 4 using 6 7 val_ring_minus_closed by blast
  have 8: "val B \<ge> 2*N"
  proof-
    have "val (B \<ominus> \<zero>) \<ge> 2*N"
      apply(rule Qp_res_eqE, rule 5)
      using zero_in_val_ring apply linarith
      unfolding Qp_res_zero assms B_alt by blast 
    then show ?thesis using B_closed 
      using Qp.minus_zero by metis
  qed
  have 9: "eint N < eint (2*N)"
  proof-
    have "N < 2*N"
    using assms(1)  by linarith
    thus ?thesis 
      using eint_ord_simps(2) of_nat_less_iff by blast
  qed
  have 10: "val B > val C"
    unfolding val_C
    using 8 9 assms(1) 
    by (metis (no_types, opaque_lifting) Qp_res_neqI eint_ord_trans notin_closed val_ring_int_inc_closed)
  have 11: "val A = val C"
    using 10 A_closed C_closed B_closed unfolding 4
    by (metis "3" "4" val_ultrametric_noteq)
  have A_nonzero: "A \<in> nonzero Q\<^sub>p"
    using A_closed 11 unfolding val_C 
    using val_nonzero' by blast
  have C_nonzero: "C \<in> nonzero Q\<^sub>p"
    using C_def Qp_nat_pow_nonzero p_nonzero by blast
  have 12: "ac N A = ac N C"
    apply(rule ac_val)
    using A_closed 11 unfolding val_C 
    using val_nonzero' apply blast
    using C_def Qp_nat_pow_nonzero p_nonzero apply blast
    unfolding 11 val_C apply blast
    using 8 unfolding 4  by (metis eint_nat_times_2 two_times_eint)
  have 13: "ac N (A \<div> C) = 1"
    using assms(1) 12 A_nonzero C_nonzero ac_div_1[of A C N] by linarith 
  have 14: "val (A \<div> C) = 0"
    using A_nonzero C_nonzero 11 A_closed val_ord[of "A \<div> C"] ord_mult 
    by (simp add: eint_defs(1) val_fract)
  have 15: "(A \<div> C) \<in> P_set n"
    using 13 14 assms(1) A_closed C_nonzero fract_closed by blast
  then obtain u where u_def: "u \<in> carrier Q\<^sub>p \<and> (A \<div> C) = u[^]n"
    using 15 unfolding P_set_def by blast 
  have 16: "(A \<div> C) =  u[^]n"
    using u_def by blast 
  have 17: "A \<div> C = ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
    using 0 C_nonzero unfolding D_dlt C_def   
    using Qp.cring_simprules(11) Qp.nonzero_memE(1) local.fract_cancel_right nonzero_inverse_Qp by presburger
  have 18: "t \<ominus> c1 = (c2 \<ominus> c1) \<otimes> u [^] n"
    using 16 n assms unfolding 17 
    by (metis Qp.cring_simprules(4) local.fract_cancel_right)
  have 19: "val u = 0"
    using 14 u_def assms(8) unfolding 16 
    using val_root by blast
  show "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 = (c2 \<ominus> c1) \<otimes> u [^] n"
    using u_def 18 19 by blast 
qed

lemma Case_iv: 
  assumes "n> 0"
  assumes "N > 1"
  assumes "(\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes " t \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  assumes "c2 \<in> carrier Q\<^sub>p" 
  assumes "c1 \<noteq> c2"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<ge> eint (-N)" 
  assumes "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (3*N) = a"
  assumes "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (2*N) \<noteq> 0"
  assumes "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (2*N) \<noteq> Qp_res (\<ominus>(\<pp>[^]N)) (2*N)"
  shows "\<exists>u \<in> carrier Q\<^sub>p. val u = 0 \<and> (t \<ominus> c1) =  ((\<pp> [^]- N) \<otimes> ([(a+p^N)]\<cdot>\<one>) \<otimes> (c2 \<ominus> c1)) \<otimes> u [^] n" 
        "\<exists>v\<in>carrier Q\<^sub>p. val v = 0 \<and> (t \<ominus> c2) =((\<pp> [^] -N)\<otimes> ([a]\<cdot>\<one>)  \<otimes>(c2 \<ominus> c1)) \<otimes> v [^] n"
proof- 
  have n: "(c2 \<ominus> c1) \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 0: "((t \<ominus> c1)\<div> (c2 \<ominus> c1)) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 00: "(t \<ominus> c2 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 1: "val ((\<pp>[^]N)\<otimes>((t \<ominus> c1)\<div> (c2 \<ominus> c1))) = val (\<pp>[^]N) + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
    using val_mult 0  p_natpow_closed(1) by blast
  have 2: "val (\<pp>[^]N) = N"
    by (metis int_pow_int val_p_int_pow)
  obtain A where A_def: "A = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c1)"
    by blast 
  have A_closed: "A \<in> carrier Q\<^sub>p"
    unfolding A_def using assms 0  Qp.cring_simprules(5) equation_6_alt p_natpow_closed(1) by presburger
  obtain B where B_def: "B = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c2)"
    by blast 
  have B_closed: "B \<in> carrier Q\<^sub>p"
    unfolding B_def 
    using assms Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.r_right_minus_eq field_inv(3) p_natpow_closed(1) by presburger
  have D_dlt: "A = (\<pp> [^] N ) \<otimes> (t \<ominus> c1 \<div> c2 \<ominus> c1)"
    unfolding A_def using equation_6_alt assms by presburger
  have B_alt: "B = (\<pp> [^] N ) \<otimes> (t \<ominus> c2\<div> c2 \<ominus> c1)"
    unfolding B_def using equation_6_alt assms by presburger
  obtain C where C_def: "C = \<pp>[^]N"
    by blast 
  have val_C: "val C = N"
    unfolding C_def using "2" by blast
  have C_closed: "C \<in> carrier Q\<^sub>p"
    unfolding C_def by blast 
  have 3: "A = B \<oplus> C" 
    unfolding A_def B_def C_def equation_6 assms 
    using assms(4) assms(5) assms(6) assms(7) equation_6 by blast
  have 4: "B = A \<ominus> C"
    unfolding 3 using  Qp.ring_simprules B_closed C_closed 
    by presburger
  have 7: "A \<in> \<O>\<^sub>p"
  proof-
    have 50: "val A = N + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
      using 0 C_closed val_C val_mult[of "\<pp> [^] N" "(t \<ominus> c1)\<div> (c2 \<ominus> c1)"] 0
      unfolding 2 C_def D_dlt by blast 
    have 51: "val A \<ge> N + eint (-N)"
      unfolding 50 using assms 
      by (metis "2" C_closed C_def Qp.add.int_pow_1 Qp.l_one Qp.one_closed eint_add_mono val_ring_int_inc_closed val_val_ring_prod)
    hence 52: "val A \<ge> 0"
      by (metis add.right_inverse eint_defs(1) plus_eint_simps(1))
    show ?thesis using A_closed 52 val_ring_memI
      by blast 
  qed
  have 6: "C \<in> \<O>\<^sub>p"
    unfolding C_def 
    using val_ring_int_inc_closed val_ring_nat_pow_closed by blast
  have 5: "B \<in> \<O>\<^sub>p"
    unfolding 4 using 6 7 val_ring_minus_closed by blast
  obtain x where x_def: "x = [a]\<cdot>\<one>"
    by blast 
  have x_closed: "x \<in> carrier Q\<^sub>p"
    unfolding x_def by blast 
  have x_val_ring: "x \<in> \<O>\<^sub>p"
    unfolding x_def 
    using val_ring_int_inc_closed by blast
  have 8: "Qp_res B (3*N) = a"
    using assms unfolding B_alt by blast 
  have 9: "Qp_res B (3*N) mod p^(3*N) = a"
    using 5 8 Qp_res_mod_triv by blast
  have 9: "a mod p^(3*N) = a"
    using 9 unfolding 8 by blast  
  have 10: "Qp_res B (3*N) = Qp_res x (3*N)"
    unfolding 5 x_def 
    using Qp_res_int_inc[of a] B_closed 5 x_def 
    using "8" Qp_res_equal by blast
  have 11: "N < 2*N"
    using assms by linarith 
  have 12: "2*N < 3*N"
    using assms by linarith 
  have 13: "Qp_res B (2*N) = Qp_res x (2*N)"
    using 5 x_val_ring 10 12 
    by (metis Qp_res_def equal_res_mod to_Zp_closed val_ring_memE(2))
  have 14: "Qp_res A (2*N) = Qp_res (x \<oplus> C) (2*N)"
    using 5 6 7 x_val_ring 13 unfolding 3 
    using Qp_res_add by presburger
  have 15: "x \<oplus> C \<noteq> \<zero>"
  proof(rule ccontr)
    assume A: "\<not> x \<oplus> C \<noteq> \<zero>"
    then have a0: "x = \<ominus> C"
      using C_closed x_closed Qp.sum_zero_eq_neg by blast
    then have a1: "Qp_res B (2*N) = Qp_res (\<ominus> C) (2*N)"
      using 13 unfolding a0 by blast 
    then show False using assms 
      unfolding B_alt C_def by blast 
  qed
  have 16: "x \<oplus> C \<in> nonzero Q\<^sub>p"
    using 15 x_closed x_closed 
    by (meson C_closed Qp.cring_simprules(1) not_nonzero_Qp)
  have 17: "Qp_res (x \<oplus> C) (2*N) \<noteq> 0"
  proof(rule ccontr)
    assume A: "\<not> Qp_res (x \<oplus> C) (2 * N) \<noteq> 0"
    hence "Qp_res (x \<oplus> C) (2 * N) = 0"
      by blast 
    hence "Qp_res (x \<ominus> (\<ominus> C)) (2 * N) = 0"
      using x_closed C_closed Qp.cring_simprules(15) Qp.cring_simprules(21) by presburger
    then have a0: "Qp_res x (2*N) = Qp_res (\<ominus> C) (2*N)"
      using 6 x_val_ring 
      by (meson Qp_res_eqI val_ring_ainv_closed)
    then have a1: "Qp_res B (2*N) = Qp_res (\<ominus> C) (2*N)"
      using 13 unfolding a0 by blast 
    then show False using assms 
      unfolding B_alt C_def by blast 
  qed
  have 18: "A \<in> nonzero Q\<^sub>p"
    using 17 14 A_closed 
    by (metis Qp.not_nonzero_memE Qp_res_zero)
  have 19: "val A = val (x \<oplus> C)"
  proof- 
    have 190: " eint (int (2 * N)) \<le> val (A \<ominus> (x \<oplus> C))"
      using Qp_res_eqE[of A "x \<oplus> C" "2*N"] 6 7 x_val_ring 14 val_ring_add_closed by blast
    have 191: "val A < 2*N"
      using 7 17 Qp_res_eq_zeroI[of A "2*N"] unfolding 14 
      using notin_closed by blast
    have 191: "val A < val (A \<ominus> (x \<oplus> C))"
      using 190 191 
      by (meson eint_ord_simps(1) eint_ord_trans le_eq_less_or_eq notin_closed of_nat_mono)
    show ?thesis using A_closed C_closed x_closed 191 
      using Qp.cring_simprules(1) ultrametric_equal_eq' by blast
  qed
  have 20: "ac N A= ac N (x \<oplus> C)"
    apply(rule ac_val, rule 18, rule 16, rule 19)
  proof- 
    have a0: "Qp_res A (3*N) = Qp_res (x \<oplus> C) (3*N)"
      using 5 6 7 x_val_ring 10 unfolding 3 
      using Qp_res_add by presburger
    have a1: " eint (int (3* N)) \<le> val (A \<ominus> (x \<oplus> C))"
      using Qp_res_eqE[of A "x \<oplus> C" "3*N"] 6 7 x_val_ring a0 val_ring_add_closed by blast
    have 190: " eint (int (2 * N)) \<le> val (A \<ominus> (x \<oplus> C))"
      using Qp_res_eqE[of A "x \<oplus> C" "2*N"] 6 7 x_val_ring 14 val_ring_add_closed by blast
    have 191: "val A < 2*N"
      using 7 17 Qp_res_eq_zeroI[of A "2*N"] unfolding 14 
      using notin_closed by blast
    have 192: "eint (int (3* N)) = eint N + eint (2*N)"
      by (metis mult_Suc numeral_nat(3) of_nat_add plus_eint_simps(1))
    have 193: "eint (int (3* N)) > eint N + val A"
      unfolding 192 using 191 
      by (meson eint_ord_code(6) notin_closed padic_fields.add_cancel_eint_geq padic_fields_axioms)
    show 194: "val A + eint (int N) \<le> val (A \<ominus> (x \<oplus> C))"      
      apply(rule eint_ord_trans[of _ "eint (int (3* N)) "  ])
      using 193 unfolding le_less apply (metis Groups.add_ac(2))
      using a1 unfolding le_less by blast 
  qed 
  have 21: "val (A \<div> (x \<oplus> C)) = 0"
    using 16 18 19 A_closed by (simp add: equal_val_quotient)
  have 22: "ac N (A \<div> (x \<oplus> C)) = 1"
    using 16 18 20 
    by (metis ac_div_1 assms(2) less_nat_zero_code linorder_neqE_nat not_less0)
  have 23: "(A \<div> (x \<oplus> C)) \<in> P_set n"
    using 21 22 A_closed 16 assms (3) fract_closed by blast
  then obtain u where u_def: "u \<in> carrier Q\<^sub>p \<and> (A \<div> (x \<oplus> C)) = u[^]n"
    unfolding P_set_def by blast 
  have 24: "(A \<div> (x \<oplus> C)) = u[^]n"
    using u_def by blast 
  have 25: "val u = 0"
    using 21 u_def assms(1) unfolding 24 
    using val_root by blast
  have 26: "A = (x \<oplus> C) \<otimes> u[^]n"
    using 24 A_closed u_def 16 
    by (metis local.fract_cancel_right)
  have 27: "inv (\<pp>[^]N) = \<pp>[^](-N)"
  proof- 
    have 270: "(\<pp>[^]N) = (\<pp>[^]int N)"
      by (metis int_pow_int)
    show ?thesis unfolding 270 
      using p_intpow_inv'' by blast
  qed
  have 28: "(t \<ominus> c1 \<div> c2 \<ominus> c1) =inv (\<pp>[^]N) \<otimes> (x \<oplus> C) \<otimes> u [^] n"
    using 26 27 0 x_closed C_closed  unfolding D_dlt C_def 
  proof -
    assume a1: "\<pp> [^] N \<in> carrier Q\<^sub>p"
  assume a2: "\<pp> [^] N \<otimes> (t \<ominus> c1 \<div> c2 \<ominus> c1) = (x \<oplus> \<pp> [^] N) \<otimes> u [^] n"
  have f3: "(t \<ominus> c1 \<div> c2 \<ominus> c1) \<otimes> \<one> = (t \<ominus> c1 \<div> c2 \<ominus> c1)"
    using Qp.r_one \<open>(t \<ominus> c1 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p\<close> by presburger
  have "\<forall>x0. - (x0::int) = - 1 * x0"
    by presburger
  then have f4: "\<one> = \<pp> [^] N \<otimes> \<pp> [^] (- 1 * int N)"
  by (metis (no_types) int_pow_int p_intpow_inv)
  have f5: "\<forall>r ra. r \<notin> carrier Q\<^sub>p \<or> ra \<notin> carrier Q\<^sub>p \<or> r \<otimes> ra = ra \<otimes> r"
    using Qp.cring_simprules(14) by satx
  then have "(t \<ominus> c1 \<div> c2 \<ominus> c1) \<otimes> \<pp> [^] N = (x \<oplus> \<pp> [^] N) \<otimes> u [^] n"
    using a2 a1 \<open>(t \<ominus> c1 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p\<close> by presburger
  then have f6: "(t \<ominus> c1 \<div> c2 \<ominus> c1) = \<pp> [^] (- 1 * int N) \<otimes> ((x \<oplus> \<pp> [^] N) \<otimes> u [^] n)"
    using f5 f4 f3 a1 by (metis (full_types) Qp.cring_simprules(11) \<open>(t \<ominus> c1 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p\<close> p_intpow_closed(1))
  have "- int N = - 1 * int N"
    by linarith 
  then show "(t \<ominus> c1 \<div> c2 \<ominus> c1) = inv (\<pp> [^] N) \<otimes> (x \<oplus> \<pp> [^] N) \<otimes> u [^] n"
    using f6 a1 Qp.cring_simprules(1) Qp.cring_simprules(11) Qp.nat_pow_closed \<open>inv (\<pp> [^] N) = \<pp> [^] - int N\<close> \<open>x \<in> carrier Q\<^sub>p\<close> p_intpow_closed(1) u_def by presburger
  qed
  have 29: "(t \<ominus> c1) = (c2 \<ominus> c1) \<otimes> \<pp> [^](- N) \<otimes> (x \<oplus> C) \<otimes> u [^] n"
    using 28 0 n unfolding 27 
    by (metis (no_types, lifting) "16" Qp.cring_simprules(11) Qp.minus_closed Qp.nat_pow_closed Qp.nonzero_memE(1) Qp.nonzero_mult_closed Qp_int_pow_nonzero assms(4) assms(5) local.fract_cancel_right p_nonzero u_def)
  have R: "\<And> a b c d. \<lbrakk>a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p; d \<in> carrier Q\<^sub>p \<rbrakk> \<Longrightarrow>
                   a \<otimes> b \<otimes> c \<otimes> d = (b \<otimes> c \<otimes> a) \<otimes> d"
    by (metis Qp.cring_simprules(11) Qp.cring_simprules(14))
  have 30: "(t \<ominus> c1) =  ((\<pp> [^]- N) \<otimes> (x \<oplus> C) \<otimes> (c2 \<ominus> c1)) \<otimes> u [^] n"   
    unfolding 29 apply(rule R)
    using assms apply blast
    using p_intpow_closed(1) apply blast
    using x_closed C_closed apply blast
    using u_def by blast
  have e: "[(a + p ^ N)] \<cdot> \<one> = x \<oplus> C"
    unfolding C_def x_def 
    using Qp.add.int_pow_mult Qp.int_nat_pow_rep Qp.one_closed by presburger
  show "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 = \<pp> [^] - int N \<otimes> [(a + p ^ N)] \<cdot> \<one> \<otimes> (c2 \<ominus> c1) \<otimes> u [^] n"
    using 30 25 u_def unfolding e by blast 
  have 31: "val B = val x"
  proof- 
    have 190: " eint (int (2 * N)) \<le> val (B \<ominus> x)"
      using Qp_res_eqE[of B "x" "2*N"] 5 6 7 x_val_ring 13 val_ring_add_closed by blast
    have 191: "val B < 2*N"
      using 5 assms Qp_res_eq_zeroI[of B "2*N"] unfolding 13 B_alt 
      by (meson notin_closed val_ring_memE(1) val_ring_memE(2) val_val_ring_prod)       
    have 191: "val B < val (B \<ominus> x)"
      using 190 191 
      by (meson eint_ord_simps(1) eint_ord_trans le_eq_less_or_eq notin_closed of_nat_mono)
    show ?thesis using B_closed C_closed x_closed 191 
      using Qp.cring_simprules(1) ultrametric_equal_eq' by blast
  qed
  have x_nonzero: "x \<in> nonzero Q\<^sub>p"
    unfolding x_def using assms 
    by (metis "31" B_alt B_closed Qp_res_zero val_nonzero' val_ord'  x_closed x_def)
  have 32: "ac N B = ac N x"
    apply(rule ac_val) 
    using 31 x_def assms 
    apply (metis B_alt B_closed Qp_res_zero finite_val_imp_nonzero val_nonzero' val_ord')
    apply(rule x_nonzero)
     apply(rule 31)
  proof- 
    have a0: "Qp_res B (3*N) = Qp_res x (3*N)"
      using "10" by blast
    have a1: " eint (int (3* N)) \<le> val (B \<ominus> x)"
      using Qp_res_eqE[of B x "3*N"] a0 5 x_val_ring by blast
    have 190: " eint (int (2 * N)) \<le> val (B \<ominus> x)"
      using Qp_res_eqE[of B "x" "2*N"] 5 6 7 x_val_ring 13 val_ring_add_closed by blast
    have 191: "val B < 2*N"
      using 5 assms Qp_res_eq_zeroI[of B "2*N"] unfolding 13 B_alt 
      by (meson notin_closed val_ring_memE(1) val_ring_memE(2) val_val_ring_prod)       
    have 192: "val B < val (B \<ominus> x)"
      using 190 191 
      by (meson eint_ord_simps(1) eint_ord_trans le_eq_less_or_eq notin_closed of_nat_mono)
    have 193: "eint (int (3* N)) = eint N + eint (2*N)"
      by (metis mult_Suc numeral_nat(3) of_nat_add plus_eint_simps(1))
    have 194: "eint (int (3* N)) > eint N + val B"
      unfolding 192 193 using 191 
      using eint_add_left_cancel_less by blast
    show "val B + eint (int N) \<le> val (B \<ominus> x)"     
      apply(rule eint_ord_trans[of _ "eint (int (3* N)) "  ])
      using 194 unfolding le_less apply (metis Groups.add_ac(2))
      using a1 unfolding le_less by blast 
  qed 
  have B_nonzero: "B \<in> nonzero Q\<^sub>p"
    using 31 x_nonzero B_closed equal_val_imp_equal_ord(2) by presburger
  have 33: "ac N (B \<div> x) = 1"
    using B_nonzero x_nonzero 32 ac_div_1 assms(2) gr_implies_not_zero by blast
  have 34: "val (B \<div> x) = 0"
    using B_nonzero x_nonzero 31 B_closed equal_val_quotient by blast
  have 35: "(B \<div> x) \<in> P_set n"
    using B_closed x_nonzero 33 34 assms(3) fract_closed by blast
  then obtain v where v_def: "v \<in> carrier Q\<^sub>p \<and> (B \<div>x) = v[^]n"
    unfolding P_set_def by blast 
  have 36: "B \<div> x = v[^]n"
    using v_def by blast 
  have 37: "val v = 0"
    using 34 v_def assms(1) unfolding 36
    using val_root by blast
  have 38: "B = x \<otimes> v[^]n"
    using 36 B_closed v_def x_nonzero 
    by (metis local.fract_cancel_right)
  have 39: "(t \<ominus> c2 \<div> c2 \<ominus> c1) = (inv (\<pp>[^]N))\<otimes> x \<otimes> v [^] n"
  proof- 
    have a0: "x \<otimes> v [^] n \<in> carrier Q\<^sub>p"
      using x_def v_def by blast
    have a1: "\<pp>[^]N \<in> nonzero Q\<^sub>p"
      using p_natpow_closed(2) by blast
    have R: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> c \<otimes> a = b \<Longrightarrow> a = (inv c) \<otimes>b"
      by (metis Qp.cring_simprules(11) Qp.cring_simprules(12) Qp.nonzero_memE(1) Qp.nonzero_memE(2) field_inv(1) field_inv(3))
    have a2: "(t \<ominus> c2 \<div> c2 \<ominus> c1) = (inv (\<pp>[^]N))\<otimes> (x \<otimes> v [^] n)"
      apply(rule R, rule 00, rule a0, rule a1)
      using 38 00 a0 a1 unfolding B_alt by blast 
    thus ?thesis using a0 a1 a2 
      by (metis "35" P_set_nonzero'(2) Qp.cring_simprules(11) Qp.nonzero_memE(1) nonzero_inverse_Qp v_def x_closed)
  qed
  have 40: "(t \<ominus> c2) = (c2 \<ominus> c1) \<otimes> (\<pp> [^] - int N)\<otimes> x \<otimes> v [^] n"
  proof- 
    have a0: "(t \<ominus> c2) \<in> carrier Q\<^sub>p"
      using assms by blast 
    have a1: "(\<pp> [^] - int N)\<otimes> x \<otimes> v [^] n \<in> carrier Q\<^sub>p"
      using x_closed v_def 
      by (metis "00" "27" "39")
    show ?thesis unfolding 39 27 using a0 a1 
      by (metis "27" "39" Qp.cring_simprules(11) Qp.m_closed Qp.minus_closed Qp.nat_pow_closed assms(5) assms(6) local.fract_cancel_right n p_intpow_closed(1) v_def x_closed)
  qed
  have 41: "(t \<ominus> c2) =((\<pp> [^] -N)\<otimes> x  \<otimes>(c2 \<ominus> c1)) \<otimes> v [^] n"
    unfolding 40 27  
    apply(rule R)
    using assms apply blast
    using p_intpow_closed(1) apply blast
    using x_closed C_closed apply blast
    using v_def by blast
  show "\<exists>v\<in>carrier Q\<^sub>p. val v = 0 \<and> (t \<ominus> c2) =((\<pp> [^] -N)\<otimes> ([a]\<cdot>\<one>)  \<otimes>(c2 \<ominus> c1)) \<otimes> v [^] n"
    using v_def 37 41 unfolding x_def by blast 
qed

lemma not_Case_i_or_Case_ii_or_Case_iii_imp_Case_iv: 
  assumes " n> 0"
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes " t \<in> carrier Q\<^sub>p"
  assumes "c1 \<in> carrier Q\<^sub>p"
  assumes " c2 \<in> carrier Q\<^sub>p" 
  assumes "c1 \<noteq> c2"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) < N"
  assumes "val ((t \<ominus> c1) \<div> (c2 \<ominus> c1)) \<ge> eint (-N)" 
  assumes "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (2*N) \<noteq> 0"
  shows "Qp_res ((\<pp>[^]N)\<otimes>((t \<ominus> c2)\<div> (c2 \<ominus> c1))) (2*N) \<noteq> Qp_res (\<ominus>(\<pp>[^]N)) (2*N)"
proof- 
  have n: "(c2 \<ominus> c1) \<in> nonzero Q\<^sub>p"
    using assms Qp.not_eq_diff_nonzero by blast
  have 0: "((t \<ominus> c1)\<div> (c2 \<ominus> c1)) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 00: "(t \<ominus> c2 \<div> c2 \<ominus> c1) \<in> carrier Q\<^sub>p"
    using n assms Qp.cring_simprules(4) fract_closed by presburger
  have 1: "val ((\<pp>[^]N)\<otimes>((t \<ominus> c1)\<div> (c2 \<ominus> c1))) = val (\<pp>[^]N) + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
    using val_mult 0  p_natpow_closed(1) by blast
  have 2: "val (\<pp>[^]N) = N"
    by (metis int_pow_int val_p_int_pow)
  obtain A where A_def: "A = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c1)"
    by blast 
  have A_closed: "A \<in> carrier Q\<^sub>p"
    unfolding A_def using assms 0  Qp.cring_simprules(5) equation_6_alt p_natpow_closed(1) by presburger
  obtain B where B_def: "B = (\<pp> [^] N \<div> c2 \<ominus> c1) \<otimes> (t \<ominus> c2)"
    by blast 
  have B_closed: "B \<in> carrier Q\<^sub>p"
    unfolding B_def 
    using assms Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.r_right_minus_eq field_inv(3) p_natpow_closed(1) by presburger
  have D_dlt: "A = (\<pp> [^] N ) \<otimes> (t \<ominus> c1 \<div> c2 \<ominus> c1)"
    unfolding A_def using equation_6_alt assms by presburger
  have B_alt: "B = (\<pp> [^] N ) \<otimes> (t \<ominus> c2\<div> c2 \<ominus> c1)"
    unfolding B_def using equation_6_alt assms by presburger
  obtain C where C_def: "C = \<pp>[^]N"
    by blast 
  have val_C: "val C = N"
    unfolding C_def using "2" by blast
  have C_closed: "C \<in> carrier Q\<^sub>p"
    unfolding C_def by blast 
  have 3: "A = B \<oplus> C" 
    unfolding A_def B_def C_def equation_6 assms 
    using assms equation_6 by blast
  have 4: "B = A \<ominus> C"
    unfolding 3 using  Qp.ring_simprules B_closed C_closed 
    by presburger
  have 7: "A \<in> \<O>\<^sub>p"
  proof-
    have 50: "val A = N + val ((t \<ominus> c1)\<div> (c2 \<ominus> c1))"
      using 0 C_closed val_C val_mult[of "\<pp> [^] N" "(t \<ominus> c1)\<div> (c2 \<ominus> c1)"] 0
      unfolding 2 C_def D_dlt by blast 
    have 51: "val A \<ge> N + eint (-N)"
      unfolding 50 using assms 
      by (metis "2" C_closed C_def Qp.add.int_pow_1 Qp.l_one Qp.one_closed eint_add_mono val_ring_int_inc_closed val_val_ring_prod)
    hence 52: "val A \<ge> 0"
      by (metis add.right_inverse eint_defs(1) plus_eint_simps(1))
    show ?thesis using A_closed 52 val_ring_memI
      by blast 
  qed
  have 6: "C \<in> \<O>\<^sub>p"
    unfolding C_def 
    using val_ring_int_inc_closed val_ring_nat_pow_closed by blast
  have 5: "B \<in> \<O>\<^sub>p"
    unfolding 4 using 6 7 val_ring_minus_closed by blast
  show ?thesis 
  proof(rule ccontr)
    assume A: " \<not> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 \<div> c2 \<ominus> c1)) (2 * N) \<noteq> Qp_res (\<ominus> (\<pp> [^] N)) (2 * N)"
    then have a0: "Qp_res B (2*N) = Qp_res (\<ominus>C) (2*N)"
      unfolding B_alt C_def by blast 
    have a1: "Qp_res (B \<ominus> (\<ominus> C)) (2*N) = 0"
      using a0 6 5 
      by (meson Qp_res_eqE Qp_res_eq_zeroI val_ring_ainv_closed val_ring_minus_closed)
    have a2: "Qp_res A (2*N) = 0"
      unfolding 3 using a1 B_closed C_closed 
      using Qp.cring_simprules(15) Qp.minus_minus by metis
    have a3: "val A \<ge> 2*N"
    proof-
      have  "val (A \<ominus> \<zero>) \<ge> 2*N"
        using A_closed 7 a2 Qp_res_eqE Qp_res_zero zero_in_val_ring by presburger
      thus ?thesis 
        using A_closed Qp.minus_zero by metis
    qed
    have a4: "eint (int (2 * N)) \<le> eint (int N) + val (t \<ominus> c1 \<div> c2 \<ominus> c1)"
      using assms(7) a3 unfolding D_dlt  1 2
      by blast 
    have a5: "eint (- int N) + eint (int (2 * N)) \<le>( eint (- int N) + eint (int N)) + val (t \<ominus> c1 \<div> c2 \<ominus> c1)"
      using a4 
      by (metis "0" C_closed add_cancel_eint_geq assms(7) eint_nat_times_2 notin_closed two_times_eint ultrametric_equal_eq val_C val_ultrametric_noteq')
    have a6: "eint (- int N) + eint (int (2 * N)) = eint N"
    proof -
      have f1: "int N + int N = 2 * int N"
        by presburger
      have f2: "- 1 * int N + 2 * int N = int N"
        by presburger
      have "- int N = - 1 * int N"
        by linarith
      then show ?thesis
        using f2 f1 eint_nat_times_2 plus_eint_simps(1) two_times_eint by presburger
    qed
    have a7: "eint (- int N) + eint (int N) = 0"
      by (metis add_eq_0_iff2 eint_defs(1) plus_eint_simps(1))
    show False using a5 assms(7) unfolding a6 a7 
      by (metis "0" C_closed add_0 notin_closed ultrametric_equal_eq' val_C val_ultrametric_noteq'')
  qed
qed

definition bottom_cell_cut where 
"bottom_cell_cut m N \<A> c2 = (SOME \<A>1. is_cell_condition \<A>1 \<and> arity \<A>1 = arity \<A> \<and> center \<A>1 = center \<A> \<and>
                                    condition_to_set \<A>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> (fibre_set \<A>)  \<and>val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N)  }) "

lemma cell_intersection_same_center_fixed:
  assumes "is_cell_condition \<C>"
  assumes "is_cell_condition \<C>'"
  assumes "\<C> = Cond m C c a1 a2 I"
  assumes "\<C>' = Cond m C' c a1' a2' I'"
  shows "\<exists> \<C>''. is_cell_condition \<C>'' \<and> arity \<C>'' = m \<and> center \<C>'' = c \<and> fibre_set \<C>'' = C \<inter> C'
                \<and> condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
proof-
  obtain l u J where luJ_def: " is_convex_condition J \<and> l \<in> carrier (SA m) \<and> u \<in> carrier (SA m) \<and>
               (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (J (val (l x)) (val (u x)) = I (val (a1 x)) (val (a2 x)) \<inter> I' (val (a1' x)) (val (a2' x))))"
    using convex_condition_intersection[of I I' a1 m a1' a2 a2'] assms[of ] 
    by (metis (mono_tags, lifting) is_cell_conditionE(3) is_cell_conditionE(4) is_cell_conditionE(5))
  obtain \<C>'' where def: "\<C>'' = Cond m (C \<inter> C') c l u J"
    by blast 
  have 0:"is_cell_condition \<C>''"
    apply(rule is_cell_conditionI)
    using assms
    unfolding def assms fibre_set.simps arity.simps center.simps l_bound.simps u_bound.simps boundary_condition.simps
        apply (meson is_cell_conditionE(1) padic_fields.intersection_is_semialg padic_fields_axioms)
    using assms padic_fields.is_cell_conditionE(2) padic_fields_axioms apply blast
    using assms luJ_def apply blast 
    using assms luJ_def apply blast 
    using assms luJ_def by blast 
  have 1: "condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
    unfolding assms def condition_to_set.simps 
    apply(rule equalityI')
     apply(rule IntI)
    apply(rule cell_memI) using cell_memE 
    apply blast
    using cell_memE(2) apply blast
  proof- 
    show " \<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
    proof-  fix x assume A: " x \<in> cell m (C \<inter> C') c l u J"
      have 0: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A cell_memE 
        by (meson Qp_pow_ConsE(1))
      have 1: " J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using "0" luJ_def by blast
      have 2: "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def cell_memE[of x m "C \<inter> C'" c l u J] IntE unfolding 1
        using A by blast
      thus "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
        by blast 
    qed
    show "\<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> x \<in> cell m C' c a1' a2' I'"
      apply(rule cell_memI)
      using cell_memE(1) apply blast
      using cell_memE(2) apply blast
    proof- 
    show " \<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> val (lead_coeff x \<ominus> c (tl x)) \<in> I' (val (a1' (tl x))) (val (a2' (tl x)))"
    proof-  fix x assume A: " x \<in> cell m (C \<inter> C') c l u J"
      have 0: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A cell_memE 
        by (meson Qp_pow_ConsE(1))
      have 1: " J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using "0" luJ_def by blast
      have 2: "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def cell_memE[of x m "C \<inter> C'" c l u J] IntE unfolding 1
        using A by blast
      thus "val (lead_coeff x \<ominus> c (tl x)) \<in> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        by blast 
    qed
    qed
    show "\<And>x. x \<in> cell m C c a1 a2 I \<inter> cell m C' c a1' a2' I' \<Longrightarrow> x \<in> cell m (C \<inter> C') c l u J"
      apply(rule cell_memI)
        apply (meson Int_iff cell_memE(1))
      using cell_memE(2) apply blast
    proof- 
      fix x assume A: "x \<in> cell m C c a1 a2 I \<inter> cell m C' c a1' a2' I'"
      then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        by (meson basic_trans_rules(31) cell_subset inf_le1)
      have 0:" J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def x_closed Qp_pow_ConsE(1) by blast
      show "val (lead_coeff x \<ominus> c (tl x)) \<in> J (val (l (tl x))) (val (u (tl x)))"
        unfolding 0 using A cell_memE[of x m C' c a1' a2' I'] cell_memE[of x m C c a1 a2 I] 
        by (metis Int_iff Qp_pow_ConsE(1) luJ_def)
    qed
  qed
  have "fibre_set \<C>'' = C \<inter> C'"
    unfolding def fibre_set.simps by blast  
  show  "\<exists>\<C>''. is_cell_condition \<C>'' \<and>
          arity \<C>'' = m \<and> center \<C>'' = c \<and> fibre_set \<C>'' = C \<inter> C' \<and> condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
    by (metis (mono_tags, opaque_lifting) def "0" "1" arity.elims assms(4) cell_condition.simps(1) center.simps padic_fields.cell_condition.exhaust padic_fields.cell_condition.simps(1) padic_fields.condition_decomp' padic_fields_axioms)
qed

lemma cell_intersection_same_center':
  assumes "is_cell_condition \<C>"
  assumes "is_cell_condition \<C>'"
  assumes "arity \<C> = m" 
  assumes "arity \<C>' = m"
  assumes "center \<C> = c"
  assumes "center \<C>' = c"
  shows "\<exists> \<C>''. is_cell_condition \<C>'' \<and> arity \<C>'' = m \<and> center \<C>'' = c \<and> fibre_set \<C>'' = fibre_set \<C> \<inter> fibre_set \<C>'
                \<and> condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
proof- 
  obtain C a1 a2 I where params: "\<C> = Cond m C c a1 a2 I"
    using assms equal_CondI by blast
  obtain C'  a1' a2' I' where params': "\<C>' = Cond m C' c a1' a2' I'"
    using assms equal_CondI by blast
  show ?thesis 
    using cell_intersection_same_center_fixed[of \<C> \<C>' m C c a1 a2 I C' a1' a2' I'] assms params params' fibre_set.simps 
    by metis 
qed

lemma cell_finite_intersection_same_center:
  assumes "finite F"
  assumes "\<And>\<C>. \<C> \<in> F \<Longrightarrow> is_cell_condition \<C>"
  assumes "\<And>\<C>. \<C> \<in> F \<Longrightarrow> center \<C> = c"
  assumes "\<And>\<C>. \<C> \<in> F \<Longrightarrow> arity \<C> = m"
  assumes "F \<noteq> {}"
  shows "\<exists> \<C>'. is_cell_condition \<C>' \<and> center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = (\<Inter> \<C> \<in> F. fibre_set \<C>) \<and> 
                condition_to_set \<C>' = (\<Inter>\<C> \<in> F. condition_to_set \<C>)"
proof- 
  have "finite F \<and> F \<noteq> {} \<and> (\<forall>\<C> \<in> F. is_cell_condition \<C> \<and> center \<C> = c \<and> arity \<C> = m) \<longrightarrow> (\<exists> \<C>'. is_cell_condition \<C>' \<and> center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = (\<Inter> \<C> \<in> F. fibre_set \<C>) \<and> 
                condition_to_set \<C>' = (\<Inter>\<C> \<in> F. condition_to_set \<C>))"
    apply(rule finite.induct[of F])
      using assms apply blast 
      apply blast
    proof(rule)
      fix A a 
      assume A: "finite A " "(finite A \<and> A \<noteq> {} \<and> (\<forall>\<C>\<in>A. is_cell_condition \<C> \<and> center \<C> = c \<and> arity \<C> = m)) \<longrightarrow>
           (\<exists>\<C>'. is_cell_condition \<C>' \<and>
                 center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` A) \<and> condition_to_set \<C>' = \<Inter> (condition_to_set ` A))"
      "finite (insert a A) \<and> insert a A \<noteq> {} \<and> (\<forall>\<C>\<in>insert a A. is_cell_condition \<C> \<and> center \<C> = c \<and> arity \<C> = m)"
      show " \<exists>\<C>'. is_cell_condition \<C>' \<and>
                center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` insert a A) \<and> condition_to_set \<C>' = \<Inter> (condition_to_set ` insert a A)"
      proof(cases "A = {}")
        case True
        have T0: "insert a A = {a}"
          unfolding True by blast 
        have T1: " \<Inter> (fibre_set ` insert a A) = fibre_set a "
          unfolding T0 by blast 
        have T2: " \<Inter> (condition_to_set ` insert a A) = condition_to_set a"
          unfolding T0 by blast 
        have T3: "is_cell_condition a \<and> center a = c \<and> arity a = m"
          using A by blast 
        show ?thesis using  T3 unfolding T1 T2 by blast 
      next
        case False
        have 0: "finite A \<and> A \<noteq> {} \<and> (\<forall>\<C>\<in>A. is_cell_condition \<C> \<and> center \<C> = c \<and> arity \<C> = m)"
          using False A 
          by blast
        have 1: " (\<exists>\<C>'. is_cell_condition \<C>' \<and>
                 center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` A) \<and> condition_to_set \<C>' = \<Inter> (condition_to_set ` A))"
          using 0 A by blast 
        then obtain \<C> where \<C>_def: " is_cell_condition \<C> \<and>
                 center \<C> = c \<and> arity \<C> = m \<and> fibre_set \<C> = \<Inter> (fibre_set ` A) \<and> condition_to_set \<C> = \<Inter> (condition_to_set ` A)"
          by blast 
        obtain B a1 a2 I where params: "\<C> = Cond m B c a1 a2 I"
          using \<C>_def by (meson equal_CondI)
        obtain D b1 b2 J where params': "a = Cond m D c b1 b2 J"
          using A by (metis equal_CondI insert_iff)
        have 2: "\<exists> \<C>'. is_cell_condition \<C>' \<and> arity \<C>' = m \<and> center \<C>' = c \<and> fibre_set \<C>' =  B \<inter> D 
                \<and> condition_to_set \<C>' = condition_to_set \<C> \<inter> condition_to_set a"
          apply(rule cell_intersection_same_center_fixed[of _ _ m B c a1 a2 I _ b1 b2 J])
          using \<C>_def apply blast
          using A apply blast
          unfolding params apply blast
          unfolding params' by blast 
        then obtain \<C>' where \<C>'_def: "is_cell_condition \<C>' \<and> arity \<C>' = m \<and> center \<C>' = c \<and> fibre_set \<C>' =  B \<inter> D 
                \<and> condition_to_set \<C>' = condition_to_set \<C> \<inter> condition_to_set a"
          by blast 
        have 3: "condition_to_set \<C>' = condition_to_set \<C> \<inter> condition_to_set a"
          using \<C>'_def by blast 
        have 4: "condition_to_set \<C> = \<Inter> (condition_to_set ` A)"
          using \<C>_def by blast 
        have 5: "condition_to_set \<C>' = \<Inter> (condition_to_set ` insert a A)"
          unfolding 3 4 by blast 
        have 6: "fibre_set a = D"
          unfolding params' fibre_set.simps by blast 
        have 7: "\<Inter> (fibre_set ` insert a A) = B \<inter> D"
          using params' \<C>_def fibre_set.simps[of m D c b1 b2 J] 
          unfolding 6 params fibre_set.simps using "6" by blast
        show " \<exists>\<C>'. is_cell_condition \<C>' \<and>
         center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` insert a A) \<and> condition_to_set \<C>' = \<Inter> (condition_to_set ` insert a A)"
          using \<C>'_def 5 params' 7 
          by metis
      qed  
    qed
    thus ?thesis 
      using assms by blast 
qed

lemma triple_disjointI:
  assumes "A \<inter> B = {}"
  assumes "A \<inter> C = {}"
  assumes "B \<inter> C = {}"
  shows "disjoint {A,B,C}"
proof(rule disjointI)
  fix D E assume A: "D \<in> {A, B, C}" "E \<in> {A, B, C}" "D \<noteq> E"
  show "D \<inter> E = {}"
    apply(cases "D = A")
     apply(cases "E = A")
    using A assms apply blast
    apply(cases "E = B")
    using A assms apply blast
    apply(cases "E = C")
    using A assms apply blast 
    using A assms apply blast

    apply(cases "D = B")
     apply(cases "E = A")
    using A assms apply blast
    apply(cases "E = B")
    using A assms apply blast
    apply(cases "E = C")
    using A assms apply blast
    using A assms apply blast


    apply(cases "D = C")
     apply(cases "E = A")
    using A assms apply blast
    apply(cases "E = B")
    using A assms apply blast
    apply(cases "E = C")
    using A assms apply blast
    using A apply blast
    using A by blast
qed

lemma SA_poly_factors_change_of_center:
  assumes "\<exists>u h k. SA_poly_factors p m n f c2 A u h k"
  assumes "c1 \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  assumes "v \<in> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
  assumes "\<And>t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> t # x \<in> A \<Longrightarrow>(t#x) \<in> A \<Longrightarrow> val (v(t#x)) = 0 \<and> t \<ominus> c2 x = (t \<ominus> c1 x)[^](j::nat) \<otimes>(g x)\<otimes>(v (t#x))[^]n"
  shows "\<exists>u h k. SA_poly_factors p m n f c1 A u h k"
proof- 
  obtain u h k where uhk_def: "SA_poly_factors p m n f c2 A u h k"
    using assms by blast 
  have 0: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using uhk_def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast
  have 1: " u \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    using uhk_def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast
  have 2: "c2 \<in> carrier (SA m)"
    using uhk_def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast
  have 3: "h \<in> carrier (SA m)"
    using uhk_def unfolding  SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def by blast
  have 4: "\<And>x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow> t # x \<in> A \<Longrightarrow> val (u (t # x)) = 0 \<and> SA_poly_to_Qp_poly m x f \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c2 x) [^] k"
    using uhk_def unfolding  SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def  by blast
  obtain u' where u'_def: "u' = (\<lambda>x. u x \<otimes> v x [^] k)"
    by blast 
  have u'_closed: "u' \<in> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
    apply(rule )
    unfolding u'_def using 1 assms (4) 
    by blast
  obtain h' where h'_def: "h' = h \<otimes>\<^bsub>SA m\<^esub>(g[^]\<^bsub>SA m\<^esub>k)"
    by blast 
  have h'_closed: "h' \<in> carrier (SA m)"
    unfolding h'_def using assms 3 by blast
  have h'_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> h' x = h x \<otimes> g x [^]k"
    unfolding h'_def using assms 3  SA_mult SA_nat_pow by presburger
  have 5: "\<And> x t. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>
           t \<in> carrier Q\<^sub>p \<Longrightarrow> t # x \<in> A \<Longrightarrow> val (u' (t # x)) = 0 \<and> SA_poly_to_Qp_poly m x f \<bullet> t =  (u' (t # x)) [^] n \<otimes> h' x \<otimes> (t \<ominus> c1 x) [^] (j*k)"
  proof- 
    fix x t assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p" "t # x \<in> A"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A Qp_pow_ConsI by blast
    have c0: "val (v(t#x)) = 0 \<and> t \<ominus> c2 x = (t \<ominus> c1 x)[^]j \<otimes>(g x)\<otimes>(v (t#x))[^]n"
      using A assms by blast 
    have c1: "val (u (t # x)) = 0 \<and> SA_poly_to_Qp_poly m x f \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c2 x) [^] k"
      using A 4 by blast 
    have c2: "u (t # x) \<in> carrier Q\<^sub>p"
      using 1 A tx_closed by blast 
    have c3: "v (t # x) \<in> carrier Q\<^sub>p"
      using assms 1 A tx_closed by blast 
    have c4: "t \<ominus> c2 x = (t \<ominus> c1 x)[^]j \<otimes>(g x)\<otimes>(v (t#x))[^]n"
      using c0 by blast
    have c5: "g x \<in> carrier Q\<^sub>p"
      using A assms SA_car_closed by blast 
    have d0: "(t \<ominus> c1 x) \<in> carrier Q\<^sub>p"
      using A assms 
      by (meson Qp.cring_simprules(4) SA_car_closed)
    have d1: "(t \<ominus> c1 x)[^]j \<in> carrier Q\<^sub>p"
      using d0 by blast
    have c6: "(t \<ominus> c2 x) [^] k = ((t \<ominus> c1 x)[^]j)[^]k \<otimes> (g x)[^]k \<otimes> (v (t # x) [^] n) [^] k"
      unfolding c4 using c3 c5  Qp.nat_pow_distrib 
      using Qp.cring_simprules(5) Qp.nat_pow_closed d1 by presburger
    have c7: "(v (t # x) [^] n) [^] k = (v (t # x) [^] k) [^] n"
      using c3 
      by (metis Groups.mult_ac(2) Qp_nat_pow_pow)
    have c8: "SA_poly_to_Qp_poly m x f \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c2 x) [^] k"
      using c1 by blast 
    have c9: "SA_poly_to_Qp_poly m x f \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (((t \<ominus> c1 x)[^]j)[^]k \<otimes> g x [^] k \<otimes> (v (t # x) [^] k) [^] n)"
      unfolding c6 c7 c8 by blast 
    have R: "\<And> a b c d e. \<lbrakk>a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p; d \<in> carrier Q\<^sub>p; e \<in> carrier Q\<^sub>p \<rbrakk> \<Longrightarrow> 
                a[^]n \<otimes> b \<otimes> (e \<otimes> c \<otimes> d[^]n)  = (a \<otimes> d)[^]n \<otimes> (b \<otimes> c) \<otimes> e"
      by (smt Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.cring_simprules(5) Qp.nat_pow_closed Qp.nat_pow_distrib)
    have c10: "h x \<in> carrier Q\<^sub>p"
      using uhk_def SA_car_closed  A  unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
        by meson         
    have c11: "SA_poly_to_Qp_poly m x f \<bullet> t = (u (t # x) \<otimes> v (t # x) [^] k) [^] n \<otimes> (h x \<otimes> g x [^] k) \<otimes> ((t \<ominus> c1 x)[^]j)[^]k"
      unfolding c9 apply(rule R[of "u (t # x)" "h x" "g x [^] k" "(v (t # x) [^] k)" ])
         apply(rule c2)
        apply(rule c10)
      using c5 apply blast
      using assms tx_closed apply blast
      using A assms d1 by blast
    have c12: "SA_poly_to_Qp_poly m x f \<bullet> t = (u' (t # x)) [^] n \<otimes> h' x \<otimes> ((t \<ominus> c1 x)[^]j)[^]k"
      unfolding c11 u'_def using A tx_closed h'_eval 
      by presburger
    have c13: "((t \<ominus> c1 x)[^]j)[^]k = (t \<ominus> c1 x)[^](j*k)"
      using Qp_nat_pow_pow d0 by blast
    have c14: "val (u' (t # x)) = 0 "
    proof- 
      have b0: "val (v (t # x)) = 0"
        using c0 by blast 
      have b1: "val (v (t # x)[^]k) = 0"
      proof- 
        have 00: "v (t # x) \<in> nonzero Q\<^sub>p"
          using b0 c3  Qp.one_nonzero equal_val_imp_equal_ord(2) val_one by presburger
        then have "ord (v (t # x)) = 0"
          using b0 val_ord 
          by (metis Qp.one_closed equal_val_imp_equal_ord(1) ord_one val_one)
        then have "ord (v (t # x)[^]k) = 0"
          using 00  nonzero_nat_pow_ord by presburger
        thus ?thesis using 00 val_ord 
          using Qp_nat_pow_nonzero \<open>ord (v (t # x)) = 0\<close> b0 by presburger
      qed
      have b2: "val (u (t # x) \<otimes> v (t # x) [^] k) = val (u (t # x)) + val( v (t # x) [^] k)"
        using val_mult Qp.nat_pow_closed c2 c3 by blast
      show ?thesis 
        unfolding u'_def b2 b1 using A 4 
        by (metis arith_simps(50))
    qed
    thus "val (u' (t # x)) = 0 \<and> SA_poly_to_Qp_poly m x f \<bullet> t =  (u' (t # x)) [^] n \<otimes> h' x \<otimes> (t \<ominus> c1 x) [^] (j*k)"
      unfolding c12 using c13 by presburger
  qed
  have A_closed: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    using uhk_def unfolding SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
    by blast 
  have 6: "SA_poly_factors p m n f c1 A u' h' (j*k)"
    by(intro SA_poly_factorsI A_closed u'_closed assms h'_closed 5, auto)
  thus ?thesis 
    by auto
qed

lemma change_centers_same_set_ii: 
  assumes "\<C> = Cond m C c2 a1 a2 I"
  assumes "is_cell_condition \<C>"
  assumes "c1 \<in> carrier (SA m)"
  assumes "g \<in> carrier (SA m)"
  assumes "v \<in> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p)"
  assumes "A \<inter> condition_to_set \<C> \<noteq> {}"
  assumes "A = condition_to_set \<D>"
  assumes "\<D> = Cond m D c1 d1 d2 J"
  assumes "is_cell_condition \<D>"
  assumes " n> 0"
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes "\<And>t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow>(t#x) \<in> A \<Longrightarrow> val (v(t#x)) = 0 \<and> t \<ominus> c2 x = (g x)\<otimes>(v (t#x))[^](n::nat)"
  assumes "\<And>x. x \<in> D \<Longrightarrow> c2 x \<noteq> c1 x"
  shows "\<exists>\<B>. is_cell_condition \<B> \<and> arity \<B> = m \<and> center \<B> = c1 \<and> condition_to_set \<D> \<inter> condition_to_set \<C> = condition_to_set \<B>"
proof-  
  have c2_closed: "c2 \<in> carrier (SA m)"
    using assms is_cell_conditionE by meson
  have a0: "\<And>t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)  \<Longrightarrow>(t#x) \<in> A \<Longrightarrow> val (t \<ominus> c2 x) = val (g x) "
  proof-  
   fix x t assume A: " x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t \<in> carrier Q\<^sub>p" "t # x \<in> A"
    have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A Qp_pow_ConsI by blast
    have 0: "(t \<ominus> c2 x) \<in> carrier Q\<^sub>p"
      using A c2_closed SA_car_closed  by blast
    have 1: "g x \<in> carrier Q\<^sub>p"
      using A assms SA_car_closed by blast 
    have 2: "v(t#x) \<in> carrier Q\<^sub>p"
      using assms tx_closed by blast 
    have 3: "val ((v (t#x))[^]n) = 0"
    proof- 
      have 00: "(v (t#x)) \<in> nonzero Q\<^sub>p"
        using 2 assms(12)[of t x] A Qp.one_nonzero equal_val_imp_equal_ord(2) val_one by presburger
      have 01: "ord (v (t#x)) = 0"
        using 00 2 assms(12)[of t x] A val_ord 
        by (metis Qp.one_closed equal_val_imp_equal_ord(1) ord_one val_one)
      have 02: "ord (v (t#x)[^]n) = 0"
        using 01 00 nonzero_nat_pow_ord by presburger
      show ?thesis using val_ord 00 02 
        using Qp.one_nonzero Qp_nat_pow_nonzero ord_one val_one by presburger
    qed
    have 4: "t \<ominus> c2 x = (g x)\<otimes>(v (t#x))[^]n"
      using A assms by blast 
    show "val (t \<ominus> c2 x) = val (g x) "
      unfolding 4 
      using 0 1 2 3 val_mult[of "g x" "v (t # x) [^] n"] 
      unfolding 3 
      by (metis Qp.nat_pow_closed add.comm_neutral)
  qed
  obtain B where B_def: "B = C \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (g x) \<in> I (val (a1 x)) (val (a2 x))}"
    by blast 
  obtain \<A> where \<A>_def: "\<A> = Cond m B c2 g g closed_interval"
    by blast 
  have a1: "A \<inter> condition_to_set \<C> = A \<inter> condition_to_set \<A>"
  proof(rule equalityI')
    fix xs assume xs_def: "xs \<in> A \<inter> condition_to_set \<C>" 
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using xs_def unfolding assms condition_to_set.simps cell_def by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have 0: "val (t \<ominus> c2 x) = val (g x)"
      apply(rule a0, rule t_closed, rule x_closed)
      using xs_def unfolding tx_def by blast
    have 1: "x \<in> B"
      using xs_def x_closed t_closed
      unfolding Int_iff assms B_def condition_to_set.simps
                cell_def mem_Collect_eq tx_def list_tl list_hd 0
      by blast 
    have 2: "xs \<in> condition_to_set \<A>"
      unfolding \<A>_def condition_to_set.simps
      apply(rule cell_memI, rule xs_closed)
      using 1 unfolding tx_def list_tl list_hd apply blast
      apply(rule closed_interval_memI)
      using 0 apply (metis basic_trans_rules(20) notin_closed)
      using 0 by (metis basic_trans_rules(20) notin_closed)
    show "xs \<in> A \<inter> condition_to_set \<A>"
      using 2 xs_def by blast 
  next
    fix xs assume xs_def: "xs \<in> A \<inter> condition_to_set \<A>" 
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using xs_def unfolding \<A>_def assms condition_to_set.simps cell_def by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have 0: "x \<in> B"
      using xs_def unfolding \<A>_def condition_to_set.simps cell_def Int_iff mem_Collect_eq tx_def list_tl 
      by blast 
    have 1: "val (t \<ominus> c2 x) = val (g x)"
      apply(rule a0, rule t_closed, rule x_closed)
      using xs_def unfolding tx_def by blast
    have 2: "xs \<in> condition_to_set \<C>"
      unfolding tx_def assms condition_to_set.simps
      apply(rule cell_memI)
      using xs_closed unfolding tx_def apply blast
      using 0 unfolding B_def list_tl apply blast
      unfolding list_hd 1 using 0 unfolding B_def Int_iff mem_Collect_eq by blast 
    show "xs \<in> A \<inter> condition_to_set \<C>"
      using 2 xs_def by blast 
  qed
  have a1_closed: "a1 \<in> carrier (SA m)"
    using assms is_cell_conditionE(3) unfolding assms by meson 
  have a2_closed: "a2 \<in> carrier (SA m)"
    using assms is_cell_conditionE(4) unfolding assms by meson
  have B_semialg: "is_semialgebraic m B"
    unfolding B_def apply(rule intersection_is_semialg)
    using assms(2) is_cell_conditionE unfolding assms apply blast
    apply(rule cell_cond_semialg)
    using assms(2) is_cell_conditionE(5) unfolding assms apply blast
    using assms(4) apply blast
    using  a1_closed  apply blast 
    using  a2_closed by blast 
  have \<A>_cell: "is_cell_condition \<A>"
    unfolding \<A>_def apply(rule is_cell_conditionI', rule B_semialg, rule c2_closed, rule assms, rule assms)
    unfolding is_convex_condition_def by blast 
  have 0: "\<And> t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> t#x \<in> condition_to_set \<D> \<Longrightarrow>
       (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
    apply(rule equation_6, blast)
    apply(rule SA_car_closed[of c1 m], rule assms, blast )
    apply(rule SA_car_closed[of c2 m], rule c2_closed, blast )
    apply(rule assms) unfolding assms condition_to_set.simps cell_def mem_Collect_eq  list_tl by blast 
  have 1: "\<And> t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> t#x \<in> condition_to_set \<D> \<Longrightarrow>
                  t \<ominus> c1 x = t \<ominus> c2 x \<oplus> (c2 x \<ominus> c1 x)"
  proof- fix t x assume A: "t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)" "t#x \<in> condition_to_set \<D>"
    have c0: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
      using A 0 by blast
    have R: "\<And> a b c. \<lbrakk>a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> nonzero Q\<^sub>p \<rbrakk> \<Longrightarrow> 
                    (\<pp> [^] N \<div> c)\<otimes> a = (\<pp> [^] N \<div> c)\<otimes> b \<oplus> \<pp> [^] N \<Longrightarrow> 
                     a = b \<oplus> c "
    proof -
  fix a :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set" and b :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set" and c :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"
  assume a1: "a \<in> carrier Q\<^sub>p"
  assume a2: "c \<in> nonzero Q\<^sub>p"
assume a3: "b \<in> carrier Q\<^sub>p"
assume a4: "(\<pp> [^] N \<div> c) \<otimes> a = (\<pp> [^] N \<div> c) \<otimes> b \<oplus> \<pp> [^] N"
  have f5: "\<forall>r ra. r \<notin> carrier Q\<^sub>p \<or> ra \<notin> nonzero Q\<^sub>p \<or> ra \<otimes> (r \<div> ra) = r"
    using local.fract_cancel_right by presburger
  have f6: "\<forall>r. r \<notin> nonzero Q\<^sub>p \<or> inv r \<in> nonzero Q\<^sub>p"
    using nonzero_inverse_Qp by blast
  have f7: "\<forall>r n. r \<notin> nonzero Q\<^sub>p \<or> r [^] (n::nat) \<in> nonzero Q\<^sub>p"
    using Qp_nat_pow_nonzero by blast
  then have f8: "inv (\<pp> [^] int N) \<otimes> (a \<div> inv (\<pp> [^] int N)) = a"
    using f6 f5 a1 by (metis (full_types) int_pow_int p_nonzero)
  have f9: "\<forall>x0. - (x0::int) = - 1 * x0"
    by presburger
  have "- 1 * (- 1 * int N) = int N"
    by presburger
  then have f10: "inv (inv (\<pp> [^] int N)) = \<pp> [^] N"
    using f9 by (metis (full_types) int_pow_int p_intpow_inv'')
  have f11: "\<forall>r. r \<notin> nonzero Q\<^sub>p \<or> r \<in> carrier Q\<^sub>p"
    by (meson Qp.nonzero_memE(1))
  then have f12: "c \<otimes> (\<pp> [^] N \<div> c) = \<pp> [^] N"
    using f7 f5 a2 p_nonzero by presburger
  have f13: "\<forall>r ra. r \<notin> carrier Q\<^sub>p \<or> ra \<notin> carrier Q\<^sub>p \<or> r \<otimes> ra = ra \<otimes> r"
    by (meson Qp.cring_simprules(14))
  have f14: "c \<in> carrier Q\<^sub>p"
    using f11 a2 by meson
  have f15: "(\<pp> [^] N \<div> c) \<in> carrier Q\<^sub>p"
    using f11 f7 f6 a2 by (meson Qp.cring_simprules(5) p_nonzero)
  then have f16: "\<pp> [^] N = (\<pp> [^] N \<div> c) \<otimes> c"
    using f14 f13 f12 by presburger
  have f17: "b \<oplus> c \<in> carrier Q\<^sub>p"
    using f14 a3 by (meson Qp.cring_simprules(1))
  have f18: "b \<otimes> (\<pp> [^] N \<div> c) = (\<pp> [^] N \<div> c) \<otimes> b"
    using f15 f13 a3 by presburger
  have "a \<otimes> (\<pp> [^] N \<div> c) = (\<pp> [^] N \<div> c) \<otimes> a"
    using f15 f13 a1 by presburger
  then have "a = inv (\<pp> [^] int N) \<otimes> (b \<oplus> c \<div> inv (\<pp> [^] int N))"
    using f18 f17 f16 f15 f14 f12 f10 f8 a4 a3 a1 by (metis (no_types) Qp.cring_simprules(11) Qp.cring_simprules(13))
  then show "a = b \<oplus> c"
    using f17 f7 f6 f5 by (metis (full_types) int_pow_int p_nonzero)
    qed
    have c1: "c1 x \<in> carrier Q\<^sub>p"
      by(rule SA_car_closed[of _ m], rule assms, rule A)
    have c2: "c2 x \<in> carrier Q\<^sub>p"
      by( rule SA_car_closed[of _ m], rule c2_closed, rule A)
    have c3: "c2 x \<noteq> c1 x"
      apply(rule assms )
      using A unfolding assms condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
    have c4: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
      using c1 c2 c3 Qp.not_eq_diff_nonzero by blast
    show c5: "t \<ominus> c1 x = t \<ominus> c2 x \<oplus> (c2 x \<ominus> c1 x)"
      apply(rule  R[of "t \<ominus> c1 x" "t \<ominus> c2 x" "c2 x \<ominus> c1 x"])
         apply(rule Qp.ring_simprules, rule A, rule SA_car_closed[of _ m], rule assms, rule A)
         apply(rule Qp.ring_simprules, rule A, rule SA_car_closed[of _ m], rule c2_closed, rule A)
         apply(rule c4)
      by(rule c0)
  qed
  obtain \<B> where \<B>_def: "\<B> = Cond m (B \<inter> D) c1 d1 d2 J"
    by blast 
  have d1_closed: "d1 \<in> carrier (SA m)"
    using assms(9) is_cell_conditionE(3) unfolding assms by blast 
  have d2_closed: "d2 \<in> carrier (SA m)"
    using assms(9) is_cell_conditionE(4) unfolding assms by blast 
  have J_closed: "is_convex_condition J"
    using assms(9) is_cell_conditionE(5) unfolding assms by blast 
  have 2: "is_cell_condition \<B>"
    unfolding \<B>_def
    apply(rule is_cell_conditionI')
        apply(rule intersection_is_semialg, rule B_semialg, rule is_cell_conditionE[of _ _ c1 d1 d2 J])
    using assms unfolding assms apply blast
       apply(rule assms, rule d1_closed, rule d2_closed)
    by(rule J_closed)
  have 3: "condition_to_set \<B> = condition_to_set \<D> \<inter> condition_to_set \<A>"
  proof(rule equalityI')
    fix xs assume A: " xs \<in> condition_to_set \<B>"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding assms condition_to_set.simps cell_def \<B>_def by blast
     obtain t x where tx_def: "xs = t#x"
       using xs_closed Qp_pow_Suc_decomp by blast  
     have t_closed: "t \<in> carrier Q\<^sub>p"
       using xs_closed unfolding tx_def  
       by (metis Qp_pow_ConsE list_hd)
     have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using xs_closed unfolding tx_def 
       by (metis Qp_pow_ConsE(1) list_tl)
     have c0: " val (t \<ominus> c2 x) = val (g x)"
       apply(rule a0, rule t_closed, rule x_closed)
       using A unfolding assms tx_def \<B>_def unfolding condition_to_set.simps cell_def  by blast 
     have c1: "xs \<in> condition_to_set \<A>"
       unfolding \<A>_def condition_to_set.simps 
       apply(rule cell_memI)
         apply(rule xs_closed)
       using A unfolding \<B>_def condition_to_set.simps cell_def Int_iff apply blast
       apply(rule closed_interval_memI)
       unfolding tx_def list_tl list_hd using c0 
       apply (metis basic_trans_rules(20) notin_closed)
       unfolding tx_def list_tl list_hd using c0 
       by (metis basic_trans_rules(20) notin_closed)
     have c2: "condition_to_set \<B> \<subseteq> condition_to_set \<D>"
       unfolding assms \<B>_def condition_to_set.simps cell_def by blast 
     show "xs \<in> condition_to_set \<D> \<inter> condition_to_set \<A>"
       using A c1 c2 by blast 
  next
     fix xs assume A: "xs \<in> condition_to_set \<D> \<inter> condition_to_set \<A>"
     have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding assms condition_to_set.simps cell_def by blast
     obtain t x where tx_def: "xs = t#x"
       using xs_closed Qp_pow_Suc_decomp by blast  
     have t_closed: "t \<in> carrier Q\<^sub>p"
       using xs_closed unfolding tx_def  
       by (metis Qp_pow_ConsE list_hd)
     have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using xs_closed unfolding tx_def 
       by (metis Qp_pow_ConsE(1) list_tl)
     have c0: " val (t \<ominus> c2 x) = val (g x)"
       apply(rule a0, rule t_closed, rule x_closed)
       using A unfolding assms tx_def by blast 
     have c1: "xs \<in> condition_to_set \<B>"
       unfolding \<B>_def condition_to_set.simps
       apply(rule cell_memI)
         apply(rule xs_closed)
       using A unfolding assms condition_to_set.simps \<A>_def cell_def mem_Collect_eq Int_iff apply blast
       using A unfolding B_def c0 tx_def list_tl list_hd assms condition_to_set.simps \<A>_def cell_def mem_Collect_eq Int_iff
       by blast 
     show "xs \<in> condition_to_set \<B>"
       using c1 A by blast 
  qed
  have 4: "condition_to_set \<D> \<inter> condition_to_set \<C> =  condition_to_set \<B>"
    using a1 3 unfolding assms by blast 
  have 5: "is_cell_condition \<B> \<and> arity \<B> = m \<and> center \<B> = c1 \<and> condition_to_set \<D> \<inter> condition_to_set \<C> = condition_to_set \<B>"
    unfolding 4 using 2 unfolding \<B>_def arity.simps center.simps
    by blast 
  show ?thesis using 5 by blast 
qed

lemma empty_is_1_prepared:
  assumes "finite fs"
  assumes "fs \<noteq> {}"
  assumes "fs \<subseteq> carrier (UP (SA m))"
  shows "is_r_prepared m n 1 fs {}"
proof- 
  obtain \<C> where \<C>_def: "\<C> = Cond m (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) (\<cc>\<^bsub>m\<^esub>\<one>) (\<cc>\<^bsub>m\<^esub>\<zero>) (\<cc>\<^bsub>m\<^esub>\<one>) closed_interval"
    by blast 
  have \<C>_cell_cond: "is_cell_condition \<C>"
    unfolding \<C>_def apply(rule is_cell_conditionI')
    using carrier_is_semialgebraic apply auto[1]
    using constant_fun_closed apply blast
    using constant_fun_closed apply blast
    using constant_fun_closed apply blast
    unfolding is_convex_condition_def by blast 
  have \<C>_empty: "condition_to_set \<C> = {}"
    apply(rule equalityI')
    unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq closed_interval_def 
     apply (smt Qp.cring_simprules(2) Qp.cring_simprules(6) Qp.zero_not_one Qp_constE eint_ord_trans val_ineq)
    by blast
  obtain F where F_def: "F = (\<lambda>f \<in> fs. \<C>)"
    by blast 
  have F_eval: "\<And>f. f \<in> fs \<Longrightarrow> F f = \<C>"
    unfolding F_def restrict_apply by metis 
  have 0: "F ` fs = {\<C>}"
    apply(rule equalityI') using F_def unfolding restrict_apply F_def singleton_mem 
    apply (smt imageE)
    using assms 
    by (smt ex_in_conv rev_image_eqI)
  have 1: "(center ` {\<C>}) = {center \<C>}"
    by blast 
  have 2: "card (center ` {\<C>}) = 1"
    unfolding 1 using is_singleton_altdef by blast
  have 3: "\<one>\<^bsub>SA (Suc m)\<^esub> \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    apply(rule )
    using SA_car_closed by blast
  have 4: "(\<cc>\<^bsub>m\<^esub>\<one>) \<in> carrier (SA m)"
    using constant_fun_closed by blast
  show ?thesis 
    apply(rule is_r_preparedI[of _ _ F "F ` fs"])
    using assms apply blast
    using assms apply blast
    apply blast
    unfolding 0 2 apply simp 
    unfolding F_eval apply(rule \<C>_cell_cond)
    using \<C>_def arity.simps apply blast
     apply(intro exI, rule SA_poly_factorsI[of _ _ "\<one>\<^bsub>SA (Suc m)\<^esub>" _ "(\<cc>\<^bsub>m\<^esub>\<one>)" _ _ 0  ])
    unfolding \<C>_empty apply blast
    using 3 apply blast 
    unfolding \<C>_def center.simps apply(intro 4, intro 4)
    unfolding \<C>_empty  \<C>_def center.simps apply blast 
    using assms F_eval \<C>_empty by blast
qed

lemma finite_int_is_c_decomposable: 
  assumes "c \<in> carrier (SA m)"
  assumes "finite As"
  assumes "As \<noteq>{}"
  assumes "\<And>A. A \<in> As \<Longrightarrow> is_c_decomposable m c A"
  shows "is_c_decomposable m c (\<Inter> As)"
proof- 
  have 0:  "c_decomposables m c (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) = gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) (Cells\<^bsub>m,c\<^esub>((carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))))"
    using assms c_decomposable_is_gen_boolean_algebra carrier_is_c_decomposable by blast
  have 1: "\<And>A. A \<in> As \<Longrightarrow> A \<in> c_decomposables m c (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    unfolding c_decomposables_def mem_Collect_eq apply(rule conjI, rule assms, blast)
    using assms(4) is_c_decomposableE(3) is_semialgebraic_closed by blast 
  have 2: "As \<subseteq> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) (Cells\<^bsub>m,c\<^esub>((carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))))"
    using 1 unfolding 0 by blast 
  have 3: "(\<Inter> As) \<in> gen_boolean_algebra (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) (Cells\<^bsub>m,c\<^esub>((carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))))"
    using 2 assms(2) unfolding 0 
    by (meson assms(3) gen_boolean_algebra_finite_intersection in_mono)
  have 4: "(\<Inter> As) \<in>  c_decomposables m c (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    using 3 unfolding 0 by blast 
  show "is_c_decomposable m c (\<Inter> As)"
    using 4 unfolding c_decomposables_def by blast 
qed

lemma val_of_nonzero_residue: "\<And> b n::nat. b \<in> carrier (Zp_res_ring n) \<Longrightarrow> b \<noteq> (0::int) \<Longrightarrow> val ([b]\<cdot>\<one>) < n"
proof(rule ccontr) fix b n
  assume A: "b \<noteq> (0::int)" "\<not> val ([b] \<cdot> \<one>) < eint (int n)" "b \<in> carrier (Zp_res_ring n)"
  then have "val ([b]\<cdot>\<one>) \<ge> n"
    using notin_closed by blast
  hence "Qp_res([b]\<cdot>\<one>) n = 0"
    by (meson Qp_res_eq_zeroI val_ring_int_inc_closed)
  then show False using A                       
    by (metis Qp_res_int_inc mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))
qed

lemma partition_intersect: 
  assumes "As partitions A"
  shows "(\<inter>) B ` As partitions (B \<inter>A)"
  apply(rule is_partitionI)
   apply(rule disjointI)
  using assms is_partitionE disjointE 
  apply blast
  using assms is_partitionE(2) by blast 

lemma c_cell_finite_inter_decomp:
  assumes "finite \<C>s"
  assumes "c \<in> carrier (SA m)"
  assumes "\<C>s \<subseteq> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  assumes "\<C>s \<noteq> {}"
  shows "\<exists>\<C> \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = (\<Inter>\<C> \<in> \<C>s. condition_to_set \<C>)"
proof- 
  have 0: "\<C>s \<subseteq> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> \<C>s \<noteq>{} \<longrightarrow>
            ( \<exists>\<C> \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = (\<Inter>\<C> \<in> \<C>s. condition_to_set \<C>))"
  proof(rule finite.induct[of \<C>s], rule assms, blast, rule)
    fix A a 
    assume IH: "finite A"
           "A \<subseteq> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> A \<noteq> {} \<longrightarrow>
           (\<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = \<Inter> (condition_to_set ` A))"
          " insert a A \<subseteq> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> insert a A \<noteq> {}"
    have a_closed: "a \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
      using IH by blast 
    show " \<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = \<Inter> (condition_to_set ` insert a A)"
    proof(cases "A = {}")
      case True
      then show ?thesis unfolding True using a_closed by blast  
    next
      case False
      have F0:  "A \<subseteq> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> A \<noteq> {}"
        using False IH by blast 
      then obtain \<C> where \<C>_def: "\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> condition_to_set \<C> = \<Inter> (condition_to_set ` A)"
        using IH by blast 
      obtain C \<phi> where \<C>_params: "\<C> = Cond m C c \<phi> \<phi> closed_interval"
        using \<C>_def unfolding c_cells_at_one_val_point_def mem_Collect_eq 
        by (metis equal_CondI)
      have \<C>_cell: "is_cell_condition \<C>"
        using \<C>_def unfolding c_cells_at_one_val_point_def mem_Collect_eq by blast 
      obtain B \<psi> where a_params: "a = Cond m B c \<psi> \<psi> closed_interval"
        using a_closed unfolding c_cells_at_one_val_point_def mem_Collect_eq 
        by (metis equal_CondI)
      have a_cell: "is_cell_condition a"
        using a_closed unfolding c_cells_at_one_val_point_def mem_Collect_eq by blast 
      obtain \<D> where \<D>_def: "\<D> = Cond m (C \<inter> B \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<phi> x) = val (\<psi> x)}) c \<phi> \<phi> closed_interval"
        by blast 
      have F1: "is_semialgebraic m {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<phi> x) = val (\<psi> x)}"
        apply(rule semialg_val_eq_set_is_semialg)
        using \<C>_cell unfolding \<C>_params 
        using is_cell_conditionE''(7) apply blast
                using a_cell unfolding a_params 
                using is_cell_conditionE''(7) by blast
      have \<D>_cell: "is_cell_condition \<D>"
        unfolding \<D>_def apply(rule is_cell_conditionI')
            apply(rule intersection_is_semialg)
             apply(rule intersection_is_semialg)
        using \<C>_cell unfolding \<C>_params 
        using is_cell_conditionE''  apply blast
        using a_cell unfolding a_params 
        using is_cell_conditionE'' apply blast
        using F1 apply blast
        using assms apply blast
        using \<C>_cell unfolding \<C>_params 
        using is_cell_conditionE''(7) apply blast
        using \<C>_cell unfolding \<C>_params 
        using is_cell_conditionE''(7) apply blast
        unfolding is_convex_condition_def by blast 
      have F2: "\<D> \<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
        using \<D>_cell
        unfolding \<D>_def c_cells_at_one_val_point_def mem_Collect_eq 
          arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
          condition_to_set.simps
          cell_def by auto 
      have F3: "condition_to_set \<C> \<inter> condition_to_set a = condition_to_set \<D>"
        unfolding \<C>_params a_params \<D>_def
        by(rule finite_closed_interval_cell_intersection)
      have F4: " \<Inter> (condition_to_set ` insert a A) = condition_to_set a \<inter> (\<Inter>(condition_to_set ` A))"
        by blast
      have F5: "condition_to_set \<C> = \<Inter> (condition_to_set ` A)"
        using \<C>_def by blast 
      have F6: "condition_to_set \<D> = \<Inter> (condition_to_set ` insert a A)"
        using F3 unfolding F5 F4 by blast 
      have F7: "is_cell_condition \<D>"
        using c_cells_at_one_val_point_def F2 by blast 
      then show "\<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = \<Inter> (condition_to_set ` insert a A)" 
        using F6 F3 F2 by blast 
    qed
  qed
  thus ?thesis using assms by blast 
qed

lemma c_cell_finite_union_decomp:
  assumes "finite \<C>s"
  assumes "c \<in> carrier (SA m)"
  assumes "\<And> \<C>. \<C>\<in> \<C>s \<Longrightarrow> is_cell_condition \<C>"
  assumes "\<And> \<C>. \<C> \<in> \<C>s \<Longrightarrow> arity \<C> = m"
  assumes "\<And> \<C>. \<C> \<in> \<C>s \<Longrightarrow> center \<C> = c"
  assumes "\<And> \<C>. \<C> \<in> \<C>s \<Longrightarrow> boundary_condition \<C> = closed_interval"
  assumes "\<And> \<C>. \<C> \<in> \<C>s \<Longrightarrow> l_bound \<C> = u_bound \<C>"
  shows "\<exists>S. is_cell_decomp m S (\<Union> (condition_to_set ` \<C>s)) \<and> 
              (\<forall>\<C> \<in> S. center \<C> = c) \<and> (\<forall>\<C> \<in> S.\<forall>\<C>'\<in>\<C>s.  condition_to_set \<C> \<inter> condition_to_set \<C>' = {} \<or> condition_to_set \<C> \<subseteq> condition_to_set \<C>' ) \<and> 
              (\<forall>\<C> \<in> S. u_bound \<C> = l_bound \<C>) \<and> (\<forall>\<C> \<in> S. boundary_condition \<C> = closed_interval)"
proof- 
  have \<C>s_closed: "\<C>s \<subseteq>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    apply(rule subsetI)
    using assms is_cell_conditionE 
    unfolding c_cells_at_one_val_point_def mem_Collect_eq 
    by (metis cell_condition_to_set_subset equal_CondI)
  have 0: "one_val_point_c_decomposable m c (carrier (SA m))(carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) (\<Union> (condition_to_set ` \<C>s))"
    apply(rule finite_union_one_val_point_c_decomposable[of c m "condition_to_set ` \<C>s"])
    using assms apply blast
    using assms apply blast
    apply auto[1] apply auto[1]
    unfolding c_cells_at_one_val_point_def 
    apply(rule subsetI)
    using assms is_cell_conditionE
    unfolding image_iff 
    by (smt (z3) arity.elims c_cells_at_one_val_point_def carrier_is_cell cell_condition_to_set_subset mem_Collect_eq u_bound.simps)   
  obtain B where B_def: "B= (\<lambda>C. (SOME \<C>. \<C> \<in> \<C>s \<and> condition_to_set \<C> = C))"
    by blast 
  have BE: "\<And>C. C \<in> (condition_to_set ` \<C>s)\<Longrightarrow> condition_to_set (B C) = C"
    unfolding B_def image_iff using SomeE by smt 
  have Bin: "\<And>C. C \<in> (condition_to_set ` \<C>s) \<Longrightarrow> B C \<in> \<C>s"
    unfolding B_def image_iff using SomeE by smt 
  obtain \<B>s where \<B>s_def: "\<B>s = B ` (condition_to_set ` \<C>s)"
    by blast 
  have \<B>s_sub: "\<B>s \<subseteq> \<C>s"
    using Bin unfolding \<B>s_def by blast 
  have \<B>s_uni: "\<Union> (condition_to_set ` \<B>s) = \<Union> (condition_to_set ` \<C>s)"
    using BE unfolding \<B>s_def by blast 
  have \<B>s_finite: "finite \<B>s"
    using \<B>s_sub assms finite_subset by blast 
  have \<B>s_closed: "\<B>s \<subseteq>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    using \<C>s_closed \<B>s_sub by blast 
  obtain \<B> where \<B>_def: "\<B> = gen_boolean_algebra (\<Union> (condition_to_set ` \<B>s)) (condition_to_set ` \<B>s)"
    by blast 
  obtain As where As_def: "As = atoms_of (condition_to_set ` \<B>s)"
    by blast 
  have As_finite: "finite As"
    unfolding As_def 
    apply(rule finite_set_imp_finite_atoms)
    using assms \<B>s_finite  by blast 
  have As_cell: "\<And>a. a \<in> As \<Longrightarrow> \<exists> \<C> \<in>  c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)).  a = condition_to_set \<C>"
  proof- fix a assume A: "a \<in> As"
    obtain Cs where Cs_def: "Cs \<noteq> {} \<and>Cs \<subseteq> condition_to_set ` \<B>s \<and> a = subset_to_atom (condition_to_set ` \<B>s) Cs"
      using A unfolding As_def atoms_of_def by blast 
    obtain \<D>s where \<D>s_def: "\<D>s \<subseteq> \<B>s \<and> Cs = condition_to_set ` \<D>s"
      using Cs_def by (meson subset_image_iff)
    have \<D>s_nonempty: "\<D>s \<noteq> {}"
      using \<D>s_def Cs_def by blast 
    have \<D>s_inter: " \<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = \<Inter> (condition_to_set ` \<D>s)"
      apply(rule c_cell_finite_inter_decomp[of \<D>s c m])
      using \<D>s_def assms finite_subset \<B>s_finite  apply blast
      using assms apply blast
      using \<B>s_closed \<D>s_def apply blast
      using \<D>s_nonempty by blast 
    then obtain \<C> where \<C>_def: "\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> condition_to_set \<C> = \<Inter> (condition_to_set ` \<D>s)"
      by blast 
    have a_eq: "a = subset_to_atom (condition_to_set ` \<B>s) Cs"
      using Cs_def by blast 
    have comp: "(condition_to_set ` \<B>s - Cs) = (condition_to_set ` \<B>s) - condition_to_set ` \<D>s"
      using \<D>s_def by blast 
    show " \<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). a = condition_to_set \<C>"
    proof(cases "\<B>s = \<D>s")
      case True
      have T0: "(condition_to_set ` \<B>s - Cs) = {}"
        unfolding comp unfolding True by blast 
      have T1: "condition_to_set \<C> = \<Inter> Cs"
        using \<C>_def \<D>s_def by blast 
      have "a = condition_to_set \<C>"
        unfolding a_eq subset_to_atom_def T0  T1 by blast 
      then show ?thesis using \<C>_def by blast 
    next
      case False
      have 00: "\<And> \<D>. \<D> \<in> \<B>s \<Longrightarrow> (\<exists>\<D>' \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). 
                                     condition_to_set \<C> - condition_to_set \<D> =  condition_to_set \<D>')"
        apply(rule one_val_point_c_cell_diff)
        using \<C>_def apply blast
        using \<B>s_closed by blast 
      obtain F where F_def: "F = (\<lambda> \<D>. (SOME \<D>'. \<D>' \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> 
                                     condition_to_set \<C> - condition_to_set \<D> =  condition_to_set \<D>' ))"
        by blast 
      have FE: "\<And>\<D>. \<D> \<in> \<B>s \<Longrightarrow> F \<D> \<in> c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>  condition_to_set \<C> - condition_to_set \<D> =  condition_to_set (F \<D>)"
        using F_def 00 SomeE by smt 
      have 01: " \<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). condition_to_set \<C> = \<Inter> (condition_to_set ` F ` (\<B>s - \<D>s))"
        apply(rule c_cell_finite_inter_decomp[of "F ` (\<B>s - \<D>s)" c m] )
        using \<D>s_def assms finite_subset \<B>s_finite apply blast
        using assms apply blast
        using \<D>s_def FE apply blast
        using False \<D>s_def  by blast
      then obtain \<E> where \<E>_def: "\<E>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> condition_to_set \<E> = \<Inter> (condition_to_set ` F ` (\<B>s - \<D>s))"
        by blast 
      have \<E>_inter: "condition_to_set \<E> = (\<Inter> \<D> \<in> (\<B>s - \<D>s). condition_to_set \<C> - condition_to_set \<D>)"
        using \<E>_def FE by blast 
      have 02: "condition_to_set \<C> = \<Inter> Cs"
        using \<C>_def \<D>s_def by blast 
      have R: "\<And> Cs A. Cs \<noteq> {} \<Longrightarrow>   A - \<Union> Cs = (\<Inter> C \<in> Cs. A - C)"
        apply(rule equalityI') apply blast
        by blast 
      have 03: "condition_to_set ` (\<B>s - \<D>s) \<noteq> {} "
        using False \<D>s_def by blast 
      have 04: "condition_to_set \<C> - \<Union> (condition_to_set ` (\<B>s - \<D>s)) = condition_to_set \<E>"
        using 03 R[of "condition_to_set ` (\<B>s - \<D>s)" "condition_to_set \<C>"]
        unfolding \<E>_inter by blast 
      have \<D>s_eq: "Cs = condition_to_set ` \<D>s"
        using \<D>s_def by blast 
      obtain Es where Es_def: "Es = condition_to_set ` (\<B>s - \<D>s)"
        by blast 
      obtain C where C_def: "C = condition_to_set \<C>"
        by blast 
      have C_eq: "C = \<Inter> Cs"
        unfolding 02 C_def by blast 
      have \<E>_inter': "condition_to_set \<E> = (\<Inter> D \<in> Es. C - D)"
        unfolding \<E>_inter C_def Es_def by blast 
      have \<B>s_inj: "\<And> a b. a \<in> condition_to_set ` \<C>s \<Longrightarrow> b \<in> condition_to_set ` \<C>s \<Longrightarrow> B a = B b \<Longrightarrow> a = b"
      proof- 
        fix a b assume A: " a \<in> condition_to_set ` \<C>s" "b \<in> condition_to_set ` \<C>s" "B a = B b"
        have 0: "condition_to_set (B a) = a"
          using BE A by blast 
        have 1: "condition_to_set (B b) = b"
          using BE A  by blast 
        show "a = b"
          using 0 unfolding A 1 by blast 
      qed
      have a: "condition_to_set ` \<C>s = condition_to_set ` \<B>s"
        unfolding \<B>s_def using Bin BE by blast 
      have Bin': "\<And>C. C \<in> (condition_to_set ` \<B>s) \<Longrightarrow> B C \<in> \<B>s"
        unfolding \<B>s_def using Bin  by blast  
      have Binv: "\<And>a. a \<in> \<B>s \<Longrightarrow> B (condition_to_set a) = a"
      proof- fix a assume A: "a \<in> \<B>s"
        obtain b where b_def: "b \<in> condition_to_set ` \<C>s \<and> a = B b"
          using A unfolding \<B>s_def by blast 
        have 0: "b \<in> condition_to_set ` \<B>s"
          using b_def unfolding a by blast 
        have 1: "a = B b"
          using b_def by blast 
        have 2: "condition_to_set (B b) = b"
          apply(rule BE) using b_def by blast 
        have 3: "condition_to_set a = b"
          unfolding 1 2 by blast 
        show "B (condition_to_set a) = a"
          unfolding 3 unfolding 1 by blast 
      qed
      have 05: "(condition_to_set ` \<B>s - Cs) = condition_to_set ` (\<B>s - \<D>s)"
        unfolding \<D>s_eq 
      proof(rule equalityI')
        fix x assume A: "x \<in> condition_to_set ` \<B>s - condition_to_set ` \<D>s"
        obtain \<A> where \<A>_def: "\<A> \<in> \<B>s \<and> x = condition_to_set \<A>"
          using A  by blast 
        have \<A>_notin: "\<A> \<notin> \<D>s" using A \<A>_def by blast 
        thus "x \<in> condition_to_set ` (\<B>s - \<D>s)"
          using \<A>_def A by blast 
      next
        fix x assume A: "x \<in> condition_to_set ` (\<B>s - \<D>s)"
        then obtain \<A> where \<A>_def: "\<A> \<in> \<B>s - \<D>s \<and> x = condition_to_set \<A>"
          by blast 
        have 0: "B x \<in> \<B>s"
          unfolding \<B>s_def using \<A>_def A BE \<B>s_sub by blast 
        have 1: " x = condition_to_set \<A>"
          using \<A>_def by blast 
        have 2: "B x = \<A>"
          unfolding 1 using Binv A \<A>_def by blast
        have "x \<notin> condition_to_set ` \<D>s"
        proof 
          assume A0: "x \<in> condition_to_set ` \<D>s"
          then obtain d where d_def: "d \<in> \<D>s \<and> x = condition_to_set d"
            by blast 
          have "B x = d"
            using d_def \<D>s_def Binv A d_def by blast 
          hence "d = \<A>"
            unfolding 2 by blast 
          thus False using d_def \<A>_def by blast 
        qed
        thus " x \<in> condition_to_set ` \<B>s - condition_to_set ` \<D>s"
          using A by blast 
      qed
      have a_eq': "a = condition_to_set \<C> - \<Union> (condition_to_set ` (\<B>s - \<D>s))"
        unfolding a_eq subset_to_atom_def 02 
        apply(rule equalityI', rule DiffI, blast, rule)
        unfolding 05 apply blast
        by blast
      have 06: "a = condition_to_set \<E>"
        unfolding a_eq' 04 by blast 
      show " \<exists>\<C>\<in>c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)). a = condition_to_set \<C>"
        using \<E>_def 06 by blast 
    qed
  qed
  obtain \<C> where \<C>_def: "\<C> = (\<lambda>a. (SOME \<C>. \<C> \<in>  c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>  a = condition_to_set \<C>))"
    by blast 
  have \<C>E: "\<And>a. a \<in> As \<Longrightarrow>  \<C> a \<in>  c_cells_at_one_val_point m c (carrier (SA m)) (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>  a = condition_to_set (\<C> a)"
    using \<C>_def As_cell SomeE by smt 
  have 1: "\<Union> As = (\<Union> (condition_to_set ` \<C>s))"
    unfolding As_def apply(rule atoms_of_covers) unfolding \<B>s_uni by blast 
  have 2: "condition_to_set ` \<C> ` As = As"
    apply(rule equalityI)
    using \<C>E apply (smt image_iff subsetI)
    using \<C>E by (smt image_iff subsetI)
  have 3: "is_cell_decomp m (\<C> ` As) (\<Union> (condition_to_set ` \<C>s))"
    apply(rule is_cell_decompI)
    using As_finite apply blast
    unfolding 2 apply(rule is_partitionI, rule disjointI)
    unfolding As_def
        apply(rule atoms_of_disjoint[of _ "condition_to_set ` \<B>s"], blast, blast, blast)
    using 1 unfolding As_def apply blast
    using \<C>E unfolding As_def c_cells_at_one_val_point_def mem_Collect_eq image_iff 
      apply blast
    using assms 
    apply (metis condition_to_set_is_semialg finite_union_is_semialgebraic'' is_semialgebraic_closed)
  proof- 
    fix s s' 
    assume A: " \<exists>x\<in>atoms_of (condition_to_set ` \<B>s). s = \<C> x"
      " \<exists>x\<in>atoms_of (condition_to_set ` \<B>s). s' = \<C> x" "s \<noteq> s'"
    obtain a1 where a1_def: "a1 \<in> atoms_of (condition_to_set ` \<B>s) \<and> s = \<C> a1"
      using A by blast 
    obtain a2 where a2_def: "a2 \<in> atoms_of (condition_to_set ` \<B>s) \<and> s' = \<C> a2"
      using A by blast 
    have p0: "s = \<C> a1"
      using a1_def by blast 
    have p1: "s' = \<C> a2"
      using a2_def by blast 
    have p2: "a1 = condition_to_set s"
      using \<C>E[of a1] a1_def unfolding p0 As_def by blast 
    have p3: "a2 = condition_to_set s'"
      using \<C>E[of a2] a2_def unfolding p1 As_def by blast 
    have p4: "a1 \<inter> a2 = {}"
      apply(rule atoms_of_disjoint[of _ "condition_to_set ` \<B>s"])
      using a1_def apply blast
      using a2_def apply blast
      using A unfolding p0 p1 by blast 
    show "condition_to_set s \<inter> condition_to_set s' = {}"
      using p4 unfolding p2 p3 by blast 
  qed
  have 4: "(\<forall>\<C>\<in>(\<C> ` As). center \<C> = c)"
    using \<C>E unfolding c_cells_at_one_val_point_def mem_Collect_eq image_iff by blast 
  have 5: " (\<forall>\<C>\<in>(\<C> ` As). \<forall>\<C>'\<in>\<C>s.  condition_to_set \<C> \<inter> condition_to_set \<C>' = {} \<or> condition_to_set \<C> \<subseteq> condition_to_set \<C>' )"
  proof(rule, rule) fix \<A> \<D> assume A: " \<A> \<in> \<C> ` As" "\<D> \<in> \<C>s "
    obtain a where a_def: "\<A> = \<C> a \<and>a \<in> As"
      using A by blast 
    have a_notempty: "a \<noteq> {}"
      using a_def unfolding As_def atoms_of_def subset_to_atom_def by blast 
    have 50: "a \<subseteq> (\<Union> (condition_to_set ` \<C>s))"
      using a_def 1 by blast 
    have b: "(condition_to_set ` \<B>s) = (condition_to_set ` \<C>s)"
      apply(rule equalityI') 
      using \<B>s_sub apply blast
      unfolding \<B>s_def using BE by blast 
    have c: "condition_to_set \<D> \<inter> \<Union> (condition_to_set ` \<C>s) \<in> gen_boolean_algebra (\<Union> (condition_to_set ` \<C>s)) (condition_to_set ` \<C>s)"
      apply(rule gen_boolean_algebra.generator[of "condition_to_set \<D>" "(condition_to_set ` \<C>s)" "\<Union> (condition_to_set ` \<C>s)"])
      using A by blast 
    have d: "condition_to_set \<D> \<inter> \<Union> (condition_to_set ` \<C>s) = condition_to_set \<D> "
      using A by blast 

    have 51: "condition_to_set \<D> \<inter> a = {} \<or> a \<subseteq> condition_to_set \<D>"
      apply(rule finite_algebra_atoms_are_minimal[of "(condition_to_set ` \<C>s)"  "\<Union> (condition_to_set ` \<C>s)" a "condition_to_set \<D>"])
      using assms apply blast
      apply blast
      using a_def \<B>s_sub  unfolding As_def b apply blast
      using c A unfolding d by blast
    have 53: "condition_to_set \<A> = a"
      using A a_def \<C>E[of a] by metis 
    thus "condition_to_set \<A> \<inter> condition_to_set \<D>= {} \<or> condition_to_set \<A> \<subseteq> condition_to_set \<D>"
      using a_def 51 by blast 
  qed
  have 6: "(\<forall>\<C>\<in>(\<C> ` As). u_bound \<C> = l_bound \<C>)"
    using u_bound.simps l_bound.simps \<C>E 
    unfolding c_cells_at_one_val_point_def mem_Collect_eq by blast 
  have 7: "(\<forall>\<C>\<in>(\<C> ` As). boundary_condition \<C> = closed_interval)"
    using u_bound.simps l_bound.simps \<C>E 
    unfolding c_cells_at_one_val_point_def mem_Collect_eq by blast 
  show ?thesis 
    using 3 4 5 6 7 by blast 
qed

lemma mod_eq_zero_val:
  assumes "b mod p^n = 0"
  shows "val ([b]\<cdot>\<one>) \<ge> n"
proof- 
  have 0: " ([b]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) n = 0"
    using assms Zp_int_inc_res by presburger
  have 2: "val_Zp (([b]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)) \<ge> n"
  proof(cases "([b]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>) = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
    case True
    show ?thesis unfolding True val_Zp_def 
      using eint_ord_simps(3) by presburger
  next
    case False
    have 1: "ord_Zp (([b]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)) \<ge> n"
      using 0 False above_ord_nonzero[of "([b]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>)"] 
      by (smt Zp.int_inc_closed)
    show ?thesis 
      using 1 
      by (smt Zp_int_inc_closed eint_ord_simps(1) of_nat_0_le_iff ord_of_nonzero(1) val_ord_Zp)
  qed
  show ?thesis using 2
    by (metis Q\<^sub>p_def Zp_def padic_fields.to_Zp_int_inc padic_fields_axioms to_Zp_val val_ring_int_inc_closed)
qed

lemma val_of_nonzero_residue': 
  assumes "b mod p^n \<noteq> 0"
  shows "val ([b] \<cdot> \<one>) < eint (int n)"
proof- 
  obtain c where c_def: "c = b mod p^n"
    by blast 
  have 0: "(b - c) mod p^n = 0 mod p^n"
    unfolding c_def 
    by (metis diff_self mod_diff_right_eq)
  have 1: "val ([c] \<cdot> \<one>) < eint (int n)"
    apply(rule val_of_nonzero_residue)
    unfolding c_def 
    using mod_in_carrier apply blast
    by(rule assms)
  have 2: "val ([(b-c)]\<cdot>\<one>) \<ge> eint (int n)"
    using 0 mod_eq_zero_val 
    by presburger
  have "[b]\<cdot>\<one> \<ominus> [c]\<cdot>\<one> = [(b-c)]\<cdot>\<one>"
    unfolding a_minus_def 
    using Qp.add.int_pow_diff by blast
  then have 3: "val ([b]\<cdot>\<one> \<ominus> [c]\<cdot>\<one>) \<ge> eint (int n)"
    using 2 by metis  
  have 4: "val ([b]\<cdot>\<one> \<ominus> [c]\<cdot>\<one>) > val ([c]\<cdot>\<one>)"
    using 3 1 eint_ord_trans notin_closed by blast
  have 5: "val ([b]\<cdot>\<one>) = val ([c]\<cdot>\<one>)"
    using 4 
    by (metis Qp.int_inc_closed ultrametric_equal_eq)
  thus ?thesis using 1 by metis 
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Setup to Show that $2$-preparable set is a $1$-preparable set\<close>
(**************************************************************************************************)
(**************************************************************************************************)
locale two_preparable_to_one_preparable_reduction = common_decomp_proof_context  + 
  fixes m n fs gs A' B'
  assumes "denef_I p (Suc d)"
  assumes "fs \<subseteq> carrier (UP (SA m))"
  assumes "\<And>f. f \<in> fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "gs \<subseteq> carrier (UP (SA m))"
  assumes "\<And>g. g \<in> gs \<Longrightarrow> deg (SA m) g \<le> Suc d"
  assumes "n > 0" 
  assumes "is_r_prepared m n 1 fs A'"
  assumes "is_r_prepared m n 1 gs B'"
  assumes "fs \<inter> gs = {}"
  assumes fs_nonempty: "fs \<noteq> {}"
  assumes gs_nonempty: "gs \<noteq> {}"

context two_preparable_to_one_preparable_reduction
begin

text\<open>I can't unfold equations within the locale where A' or B' appear on the left side, and an expression
     which involves constants which have been defined within the locale in terms of A' and B' appear on the 
     right side. My ad hoc solution is to guard them with constants defined to be equal to them and use them 
     as proxies for the actual A' and B' while reasoning inside my locale.\<close>

definition A where A_def: "A = A'"
definition B where B_def: "B = B'"

lemma locale_assms: 
   "denef_I p (Suc d)"
   "fs \<subseteq> carrier (UP (SA m))"
   "\<And>f. f \<in> fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
   "gs \<subseteq> carrier (UP (SA m))"
   "\<And>g. g \<in> gs \<Longrightarrow> deg (SA m) g \<le> Suc d"
   "n > 0" 
   "is_r_prepared m n 1 fs A"
   "is_r_prepared m n 1 gs B"
   "fs \<inter> gs = {}"
  using two_preparable_to_one_preparable_reduction_axioms 
  unfolding A_def B_def two_preparable_to_one_preparable_reduction_def
            two_preparable_to_one_preparable_reduction_axioms_def
  by auto 

definition \<C>\<^sub>1 where \<C>\<^sub>1_def: "\<C>\<^sub>1 = (SOME \<C>\<^sub>1. \<exists> Cs\<^sub>1. \<C>\<^sub>1 \<in> fs \<rightarrow> Cs\<^sub>1 \<and>
       card (center ` \<C>\<^sub>1 ` fs) \<le> 1 \<and>
       A = (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f)) \<and>
       (\<forall>f\<in>fs. is_cell_condition (\<C>\<^sub>1 f) \<and> arity (\<C>\<^sub>1 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k)))"

lemma some_fact:
  assumes "a = (SOME x. P x)"
  assumes "\<exists> x. P x"
  shows "P a"
  using assms 
  by (simp add: some_eq_ex)

lemma \<C>\<^sub>1_ex:
" \<exists> Cs\<^sub>1. \<C>\<^sub>1 \<in> fs \<rightarrow> Cs\<^sub>1 \<and>
       card (center ` \<C>\<^sub>1 ` fs) \<le> 1 \<and>
       A = (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f)) \<and>
       (\<forall>f\<in>fs. is_cell_condition (\<C>\<^sub>1 f) \<and> arity (\<C>\<^sub>1 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k))"
  apply(rule some_fact[of  "\<C>\<^sub>1"])
  using \<C>\<^sub>1_def apply auto[1] 
  using locale_assms \<C>\<^sub>1_def is_r_preparedE[of m n 1 fs A] by blast 


definition Cs\<^sub>1 where Cs\<^sub>1_def: "Cs\<^sub>1 = (SOME Cs\<^sub>1. \<C>\<^sub>1 \<in> fs \<rightarrow> Cs\<^sub>1 \<and>
       card (center ` \<C>\<^sub>1 ` fs) \<le> 1 \<and>
       A = (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f)) \<and>
       (\<forall>f\<in>fs. is_cell_condition (\<C>\<^sub>1 f) \<and> arity (\<C>\<^sub>1 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k)))"

lemma fs_defs_0: 
      " \<C>\<^sub>1 \<in> fs \<rightarrow> Cs\<^sub>1 \<and>
       card (center ` \<C>\<^sub>1 ` fs) \<le> 1 \<and>
       A = (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f)) \<and>
       (\<forall>f\<in>fs. is_cell_condition (\<C>\<^sub>1 f) \<and> arity (\<C>\<^sub>1 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k))"
by(rule some_fact[of Cs\<^sub>1], rule Cs\<^sub>1_def, rule \<C>\<^sub>1_ex) 

definition \<C>\<^sub>2 where \<C>\<^sub>2_def: "\<C>\<^sub>2 = (SOME \<C>\<^sub>2. \<exists> Cs\<^sub>1. \<C>\<^sub>2 \<in> gs \<rightarrow> Cs\<^sub>1 \<and>
       card (center ` \<C>\<^sub>2 ` gs) \<le> 1 \<and>
       B = (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f)) \<and>
       (\<forall>f\<in>gs. is_cell_condition (\<C>\<^sub>2 f) \<and> arity (\<C>\<^sub>2 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>2 f)) (condition_to_set (\<C>\<^sub>2 f)) u h k)))"

lemma \<C>\<^sub>2_ex:
" \<exists> Cs\<^sub>2. \<C>\<^sub>2 \<in> gs \<rightarrow> Cs\<^sub>2 \<and>
       card (center ` \<C>\<^sub>2 ` gs) \<le> 1 \<and>
       B = (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f)) \<and>
       (\<forall>f\<in>gs. is_cell_condition (\<C>\<^sub>2 f) \<and> arity (\<C>\<^sub>2 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>2 f)) (condition_to_set (\<C>\<^sub>2 f)) u h k))"
  apply(rule some_fact[of  "\<C>\<^sub>2"])
  using \<C>\<^sub>2_def apply auto[1] 
  using locale_assms \<C>\<^sub>2_def is_r_preparedE[of m n 1 gs B] by blast 


definition Cs\<^sub>2 where Cs\<^sub>2_def: "Cs\<^sub>2 = (SOME Cs\<^sub>2. \<C>\<^sub>2 \<in> gs \<rightarrow> Cs\<^sub>2 \<and>
       card (center ` \<C>\<^sub>2 ` gs) \<le> 1 \<and>
       B = (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f)) \<and>
       (\<forall>f\<in>gs. is_cell_condition (\<C>\<^sub>2 f) \<and> arity (\<C>\<^sub>2 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>2 f)) (condition_to_set (\<C>\<^sub>2 f)) u h k)))"

lemma gs_defs_0: 
      " \<C>\<^sub>2 \<in> gs \<rightarrow> Cs\<^sub>2 \<and>
       card (center ` \<C>\<^sub>2 ` gs) \<le> 1 \<and>
       B = (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f)) \<and>
       (\<forall>f\<in>gs. is_cell_condition (\<C>\<^sub>2 f) \<and> arity (\<C>\<^sub>2 f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>2 f)) (condition_to_set (\<C>\<^sub>2 f)) u h k))"
  by(rule some_fact[of Cs\<^sub>2], rule Cs\<^sub>2_def, rule \<C>\<^sub>2_ex) 

lemma fs0: "(center ` \<C>\<^sub>1 ` fs)\<noteq> {}"
  using fs_nonempty by auto 

lemma fs1: "finite fs"
  using locale_assms is_r_preparedE by blast 

lemma fs2: "card (center ` \<C>\<^sub>1 ` fs) = 1"
proof-
  have "card (center ` \<C>\<^sub>1 ` fs) > 0"
  using fs0 fs1 card_gt_0_iff by blast
  thus ?thesis using fs_defs_0 by linarith
qed

lemma gs0: "(center ` \<C>\<^sub>1 ` gs)\<noteq> {}"
  using gs_nonempty by blast 

lemma gs1: "finite gs"
  using locale_assms is_r_preparedE by blast 

lemma gs2: "card (center ` \<C>\<^sub>2 ` gs) = 1"
proof-
  have "card (center ` \<C>\<^sub>2 ` gs) > 0"
  using gs0 gs1  card_gt_0_iff by blast
  thus ?thesis using gs_defs_0 by linarith
qed

definition c1 where c1: "c1 = (SOME c1. (center ` \<C>\<^sub>1 ` fs) = {c1})"

lemma c1_def: "(center ` \<C>\<^sub>1 ` fs) = {c1}"
  apply(rule some_fact[of c1], rule c1)
  by (meson card_1_singletonE fs2)

lemma fs_defs: " \<C>\<^sub>1 \<in> fs \<rightarrow> Cs\<^sub>1"
  " A = (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f))"
              "\<And>f. f \<in> fs \<Longrightarrow> center (\<C>\<^sub>1 f) = c1"
              "\<And>f. f \<in> fs \<Longrightarrow> is_cell_condition (\<C>\<^sub>1 f)"
              "\<And>f. f \<in> fs \<Longrightarrow> arity (\<C>\<^sub>1 f) = m"
              "\<And>f. f \<in> fs \<Longrightarrow> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k)"
  using fs_defs_0 apply blast
  using fs_defs_0 apply blast
  using c1_def apply blast
  using fs_defs_0 apply blast
  using fs_defs_0 apply blast
  using fs_defs_0 by blast

definition c2 where c2: "c2 = (SOME c2. (center ` \<C>\<^sub>2 ` gs) = {c2})"

lemma c2_def: "(center ` \<C>\<^sub>2 ` gs) = {c2}"
  apply(rule some_fact[of c2], rule c2)
  by (meson card_1_singletonE gs2)

lemma gs_defs: " \<C>\<^sub>2 \<in> gs \<rightarrow> Cs\<^sub>2"
              " B = (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f))"
              "\<And>f. f \<in> gs \<Longrightarrow> center (\<C>\<^sub>2 f) = c2"
              "\<And>f. f \<in> gs \<Longrightarrow> is_cell_condition (\<C>\<^sub>2 f)"
              "\<And>f. f \<in> gs \<Longrightarrow> arity (\<C>\<^sub>2 f) = m"
              "\<And>f. f \<in> gs \<Longrightarrow> (\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>2 f)) (condition_to_set (\<C>\<^sub>2 f)) u h k)"
  using gs_defs_0 apply blast
  using gs_defs_0 apply blast
  using c2_def apply blast
  using gs_defs_0 apply blast
  using gs_defs_0 apply blast
  using gs_defs_0 by blast

lemma c1_closed: "c1 \<in> carrier (SA m)"
proof-
  obtain f where f_def: "f \<in> fs"
    using fs_nonempty by blast 
  obtain C a1 a2 I where params: "\<C>\<^sub>1 f = Cond m C c1 a1 a2 I"
    using c1_def fs_defs fs_nonempty is_cell_conditionE(2) arity.simps center.simps
    by (metis equal_CondI f_def)
  show ?thesis 
  apply(rule is_cell_conditionE[of _ C _ a1 a2 I])
     using f_def fs_defs(4)[of f] unfolding params by blast 
qed

lemma c2_closed: "c2 \<in> carrier (SA m)"
proof-
  obtain f where f_def: "f \<in> gs"
    using gs_nonempty by blast 
  obtain C a1 a2 I where params: "\<C>\<^sub>2 f = Cond m C c2 a1 a2 I"
    using c2_def gs_defs gs_nonempty  is_cell_conditionE(2) arity.simps center.simps
    by (metis equal_CondI f_def)
  show ?thesis 
  apply(rule is_cell_conditionE[of _ C _ a1 a2 I])
     using f_def gs_defs(4)[of f] unfolding params by blast 
qed

text\<open>We want to break $A \cap B$ into two pieces. One piece will be the region where $c_1$ and $c_2$ 
agree, and the other the region where they disagree. We can then show that $A \cap B$ can be 
$1$-prepared by doing this on each of these two pieces separately. We do this by defining the sets 
$Y_0$ and $Y_1$ below and then intersecting them with $A$ and $B$.\<close>

definition Y0 where Y0_def: "Y0 = {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). c1 x = c2 x}"

lemma Y0_closed: "is_semialgebraic m Y0"
  unfolding Y0_def 
  by(rule SA_eq_set_is_semialg, rule c1_closed, rule c2_closed)

definition Y1 where Y1_def: "Y1 = carrier (Q\<^sub>p\<^bsup>m\<^esup>) - Y0"

lemma Y1_closed: "is_semialgebraic m Y1"
  unfolding Y1_def using Y0_closed 
  using complement_is_semialg by blast

lemma Y1_un_Y0: "Y0 \<union> Y1 = carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  apply(rule equalityI')
  unfolding Y1_def using Y0_closed 
   apply (metis (no_types, opaque_lifting) Set.basic_monos(7) Un_Diff_cancel Un_iff is_semialgebraic_closed)
  by blast 

definition \<A>1 where \<A>1_def: "\<A>1 = (\<lambda> f. refine_fibres_2 (\<C>\<^sub>1 f) Y0)"

definition \<B>1 where \<B>1_def: "\<B>1 = (\<lambda>f. refine_fibres_2 (\<C>\<^sub>1 f) Y1)"

definition \<A>2 where \<A>2_def: "\<A>2 = (\<lambda> f. refine_fibres_2 (\<C>\<^sub>2 f) Y0)"

definition \<B>2 where \<B>2_def: "\<B>2 = (\<lambda>f. refine_fibres_2 (\<C>\<^sub>2 f) Y1)"

definition A1 where A1_def: "A1 = (\<Inter> f \<in> fs. condition_to_set (\<A>1 f))"

definition A2 where A2_def: "A2 = (\<Inter> f \<in> gs. condition_to_set (\<A>2 f))"

definition B1 where B1_def: "B1 = (\<Inter> f \<in> fs. condition_to_set (\<B>1 f))"

definition B2 where B2_def: "B2 = (\<Inter> f \<in> gs. condition_to_set (\<B>2 f))"

lemma \<A>1_int_\<B>1: "\<And>f g. condition_to_set (\<A>1 f) \<inter> condition_to_set (\<B>1 g) = {}"
  unfolding \<A>1_def \<B>1_def Y1_def
  by(rule refine_fibres_2_disjoint, blast)

lemma \<A>1_int_\<B>2: "\<And>f g. condition_to_set (\<A>1 f) \<inter> condition_to_set (\<B>2 g) = {}"
  unfolding \<A>1_def \<B>2_def Y1_def
  by(rule refine_fibres_2_disjoint, blast)

lemma \<A>2_int_\<B>1: "\<And>f g. condition_to_set (\<A>2 f) \<inter> condition_to_set (\<B>1 g) = {}"
  unfolding \<A>2_def \<B>1_def Y1_def
  by(rule refine_fibres_2_disjoint, blast)

lemma \<A>2_int_\<B>2: "\<And>f g. condition_to_set (\<A>2 f) \<inter> condition_to_set (\<B>2 g) = {}"
  unfolding \<A>2_def \<B>2_def Y1_def
  by(rule refine_fibres_2_disjoint, blast)

lemma \<A>1_un_\<B>1_ptwise: "\<And>f. f \<in> fs \<Longrightarrow> condition_to_set (\<A>1 f) \<union> condition_to_set (\<B>1 f) =   
                             condition_to_set (\<C>\<^sub>1 f)"
  unfolding \<A>1_def  \<B>1_def apply(rule refine_fibres_2_covers[of _ _ m])
    apply(rule Y1_un_Y0)
  by(rule fs_defs, blast, rule fs_defs, blast)

lemma \<A>2_un_\<B>2_ptwise: "\<And>f. f \<in> gs \<Longrightarrow> condition_to_set (\<A>2 f) \<union> condition_to_set (\<B>2 f) =   
                             condition_to_set (\<C>\<^sub>2 f)"
  unfolding \<A>2_def  \<B>2_def apply(rule refine_fibres_2_covers[of _ _ m])
    apply(rule Y1_un_Y0)
  by(rule gs_defs, blast, rule gs_defs, blast)

lemma A_covered: "A = A1 \<union> B1"
   unfolding A1_def B1_def fs_defs 
proof(rule equalityI')
  fix x assume A: "x \<in> (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f))"
  have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  proof- 
    obtain f where f_def: "f \<in> fs"
      using fs_nonempty by blast 
    show ?thesis 
      using f_def A fs_nonempty condition_to_set_memE[of x "\<C>\<^sub>1 f" m] fs_defs(5)[of f] by blast 
  qed
  show " x \<in> (\<Inter>f\<in>fs. condition_to_set (\<A>1 f)) \<union> (\<Inter>f\<in>fs. condition_to_set (\<B>1 f))"
  proof(cases "tl x \<in> Y0")
    case True
    have T0: " x \<in> (\<Inter>f\<in>fs. condition_to_set (\<A>1 f))"
      apply(rule InterI)
      using True A unfolding \<A>1_def 
      by (smt image_iff mem_simps(10) refine_fibres_2_memI)          
    then show ?thesis by blast 
  next
    case False
    then have F0: "tl x \<in> Y1"
      unfolding Y1_def using tl_x_closed by blast 
    have F1: " x \<in> (\<Inter>f\<in>fs. condition_to_set (\<B>1 f))"
      apply(rule InterI)
      using F0 A unfolding \<B>1_def 
      by (smt image_iff mem_simps(10) refine_fibres_2_memI)  
    then show ?thesis by blast 
  qed
next
  fix x assume A: "x \<in> (\<Inter>f\<in>fs. condition_to_set (\<A>1 f)) \<union> (\<Inter>f\<in>fs. condition_to_set (\<B>1 f))"
  show "x \<in> (\<Inter>f\<in>fs. condition_to_set (\<C>\<^sub>1 f))"
    using A refine_fibres_2_subset  unfolding  \<A>1_def \<B>1_def   by blast 
qed

lemma B_covered: "B = A2 \<union> B2"
  unfolding A2_def B2_def gs_defs
proof(rule equalityI')
  fix x assume A: "x \<in>  (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f))"
  have tl_x_closed: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
  proof- 
    obtain f where f_def: "f \<in> gs"
      using gs_nonempty by blast 
    show ?thesis 
      using f_def A  condition_to_set_memE[of x "\<C>\<^sub>2 f" m] gs_defs(5)[of f] by blast 
  qed
  show " x \<in> (\<Inter>f\<in>gs. condition_to_set (\<A>2 f)) \<union> (\<Inter>f\<in>gs. condition_to_set (\<B>2 f))"
  proof(cases "tl x \<in> Y0")
    case True
    have T0: " x \<in> (\<Inter>f\<in>gs. condition_to_set (\<A>2 f))"
      apply(rule InterI)
      using True A unfolding \<A>2_def 
      by (smt image_iff mem_simps(10) refine_fibres_2_memI)          
    then show ?thesis by blast 
  next
    case False
    then have F0: "tl x \<in> Y1"
      unfolding Y1_def using tl_x_closed by blast 
    have F1: " x \<in> (\<Inter>f\<in>gs. condition_to_set (\<B>2 f))"
      apply(rule InterI)
      using F0 A unfolding \<B>2_def 
      by (smt image_iff mem_simps(10) refine_fibres_2_memI)  
    then show ?thesis by blast 
  qed
next
  fix x assume A: "x \<in> (\<Inter>f\<in>gs. condition_to_set (\<A>2 f)) \<union> (\<Inter>f\<in>gs. condition_to_set (\<B>2 f))"
  show "x \<in> (\<Inter>f\<in>gs. condition_to_set (\<C>\<^sub>2 f))"
    using A refine_fibres_2_subset unfolding \<A>2_def \<B>2_def by blast 
qed

lemma A1_B1_disjoint: "A1 \<inter> B1 = {}"
  unfolding A1_def B1_def using \<A>1_int_\<B>1 fs_nonempty by blast 

lemma A2_B2_disjoint: "A2 \<inter> B2 = {}"
  unfolding A2_def B2_def using \<A>2_int_\<B>2 gs_nonempty  by blast 

lemma A1_B2_disjoint: "A1 \<inter> B2 = {}"
  unfolding A1_def B2_def using \<A>1_int_\<B>2 gs_nonempty fs_nonempty by blast

lemma A2_B1_disjoint: "A2 \<inter> B1 = {}"
  unfolding A2_def B1_def using \<A>2_int_\<B>1 gs_nonempty fs_nonempty by blast

lemma 0: "A \<inter> B = (A1 \<inter> A2) \<union> (B1 \<inter> B2)"
  unfolding A_covered B_covered
  using A1_B1_disjoint A2_B2_disjoint A1_B2_disjoint A2_B1_disjoint by blast 

lemma 1: "(A1 \<inter> A2) \<inter> (B1 \<inter> B2) = {}"
  using A1_B1_disjoint by blast 

text\<open>Showing $1$-preparability on $A_1 \cap A_2$ is easy because this is the piece of $A \cap B$ 
where the centers $c_1$ and $c_2$ agree.\<close>
lemma first_piece: 
"is_r_preparable m n 1 (fs \<union> gs) (A1 \<inter> A2)"
proof- 
  obtain \<A>3 where \<A>3_def: "\<A>3= (\<lambda>f. change_center c1 (\<A>2 f))"
    by blast 
  have \<A>3_cell_cond: "\<And>f. f \<in> gs \<Longrightarrow> is_cell_condition (\<A>3 f)"
    unfolding \<A>3_def
    apply(rule change_center_cell_cond[of _  m])
    unfolding \<A>2_def apply(rule refine_fibres_2_is_cell'[of _ m])
        apply(rule gs_defs, blast, rule gs_defs, blast)
      apply(rule Y0_closed)
    unfolding refine_fibres_2_params apply(rule gs_defs, blast)
    by(rule c1_closed)
  have \<A>3_set: "\<And>f. f \<in> gs \<Longrightarrow> condition_to_set (\<A>3 f) = condition_to_set (\<A>2 f)"
    unfolding \<A>3_def apply(rule change_center_equal_set)
    unfolding \<A>2_def refine_fibres_2_def  refine_fibres_fibre_set 
    unfolding refine_fibres_def center.simps 
    unfolding gs_defs Y0_def mem_Collect_eq Int_iff by blast 
  have \<A>3_center: "\<And>f. center (\<A>3 f) = c1"
    unfolding \<A>3_def change_center_params by blast 
  have A2_alt_def: "A2 = (\<Inter>f\<in>gs. condition_to_set (\<A>3 f))"
    unfolding A2_def using  \<A>3_set by blast 
  obtain \<C> where \<C>_def: "\<C> = (\<lambda>f. if f \<in> fs then \<A>1 f else \<A>3 f)"
    by blast 
  have \<C>_fs: "\<And>f. f \<in> fs \<Longrightarrow> \<C> f = \<A>1 f"
    using \<C>_def by metis 
  have \<C>_gs: "\<And>f. f \<in> gs \<Longrightarrow> \<C> f = \<A>3 f"
    using \<C>_def locale_assms
    by (metis (no_types, lifting) IntI empty_iff)
  have \<C>_center_fs: "\<And>f. f \<in> fs \<Longrightarrow> center (\<C> f) = c1"
    unfolding \<C>_fs \<A>1_def refine_fibres_2_params fs_defs by blast 
  have \<C>_center_gs: "\<And>f. f \<in> gs \<Longrightarrow> center (\<C> f) = c1"
    unfolding \<C>_gs \<A>3_def change_center_params by blast 
  have \<C>_center: "center ` \<C> ` (fs \<union> gs) = {c1}"
    apply(rule equalityI')
    using \<C>_center_fs \<C>_center_gs apply blast
    using \<C>_center_fs \<C>_center_gs gs_nonempty 
    by (metis (no_types, lifting) Un_iff ex_in_conv image_iff singleton_mem)
  have \<C>_cell_cond_fs: "\<And>f. f \<in> fs  \<Longrightarrow> is_cell_condition (\<C> f)"
    unfolding \<C>_fs \<A>1_def apply(rule refine_fibres_2_is_cell'[of _ m])
    unfolding fs_defs apply blast
     apply(rule fs_defs, blast)
    by(rule Y0_closed)
  have \<C>_cell_cond_gs: "\<And>f. f \<in> gs  \<Longrightarrow> is_cell_condition (\<C> f)"
    unfolding \<C>_gs by(rule \<A>3_cell_cond, blast)
  have \<C>_arity_fs: "\<And>f. f \<in> fs  \<Longrightarrow> arity (\<C> f) = m"
    unfolding \<C>_fs \<A>1_def refine_fibres_2_params fs_defs by blast 
  have \<C>_arity_gs: "\<And>f. f \<in> gs  \<Longrightarrow> arity (\<C> f) = m"
    unfolding \<C>_gs \<A>3_def change_center_params \<A>2_def refine_fibres_2_params gs_defs by blast 
  have \<C>_factors_fs: " \<And>f. f \<in> fs\<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k"
    unfolding \<C>_fs \<A>1_def refine_fibres_2_params 
    using fs_defs(6) SA_poly_factors_subset refine_fibres_2_subset  unfolding fs_defs 
    by (metis fs_defs(3))
  have \<C>_factors_gs: " \<And>f. f \<in> gs\<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k"
    apply(rule SA_poly_factors_center_eq[of _ _ _ c2])
    unfolding \<C>_gs \<A>3_set unfolding \<A>3_center \<A>2_def 
    using gs_defs(6) SA_poly_factors_subset refine_fibres_2_subset  unfolding gs_defs 
      apply (metis gs_defs(3))
    unfolding condition_to_set.simps Y0_def refine_fibres_2_def refine_fibres_def cell_def mem_Collect_eq list_tl 
              Int_iff apply blast 
    by(rule c1_closed)
  have c0: "A1 \<inter> A2 = (\<Inter>f\<in>fs \<union> gs. condition_to_set (\<C> f))"
    apply(rule equalityI')
    unfolding A1_def A2_alt_def Int_iff using \<C>_fs \<C>_gs 
    apply (smt mem_simps(10) mem_simps(3))
    using \<C>_fs \<C>_gs 
    by (smt mem_simps(10) mem_simps(3))
  show ?thesis
    apply(rule is_r_prepared_imp_is_r_preparable)
    apply(rule is_r_preparedI[of _ _ \<C> "\<C> ` (fs \<union>gs)"])
    using locale_assms is_r_preparedE apply blast
    using locale_assms is_r_preparedE apply blast
         apply blast
    unfolding \<C>_center apply simp
    using \<C>_cell_cond_fs \<C>_cell_cond_gs apply blast
    using \<C>_arity_fs \<C>_arity_gs apply blast
    using \<C>_factors_gs \<C>_factors_fs apply blast
    by(rule c0)
qed
end 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Showing that $B_1 \cap B_2$ is $1$-preparable\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The heart of the proof lies in showing that $B_1 \cap B_2$ (as defined in the locale 
\texttt{two\_preparable\_to\_one\_preparable\_reduction} is also $1$-preparable. This section will 
focus on that step.\<close>

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Preliminary Definitions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context two_preparable_to_one_preparable_reduction
begin
lemma \<B>1_neq: "\<And>t x f. t#x \<in> condition_to_set (\<B>1 f) \<Longrightarrow> c1 x \<noteq> c2 x"
  unfolding \<B>1_def refine_fibres_def refine_fibres_2_def
  unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl Y1_def Y0_def by blast

lemma \<B>2_neq: "\<And>t x f. t#x \<in> condition_to_set (\<B>2 f) \<Longrightarrow> c1 x \<noteq> c2 x"
  unfolding \<B>2_def refine_fibres_def refine_fibres_2_def
  unfolding condition_to_set.simps cell_def mem_Collect_eq list_tl Y1_def Y0_def by blast 

lemma \<B>1_arity: "\<And> f. f \<in> fs \<Longrightarrow> arity (\<B>1 f) = m"
  using fs_defs unfolding \<B>1_def refine_fibres_2_params by blast  

lemma \<B>2_arity: "\<And> f. f \<in> gs \<Longrightarrow> arity (\<B>2 f) = m"
  using gs_defs unfolding \<B>2_def refine_fibres_2_params by blast  

lemma \<B>1_cond: "\<And> f. f \<in> fs \<Longrightarrow> is_cell_condition (\<B>1 f)"
  unfolding \<B>1_def  
  apply(rule refine_fibres_2_is_cell'[of _ m])
  unfolding fs_defs apply blast
   apply(rule fs_defs, blast)
  by(rule Y1_closed)

lemma \<B>2_cond: "\<And> f. f \<in> gs \<Longrightarrow> is_cell_condition (\<B>2 f)"
  unfolding \<B>2_def  
  apply(rule refine_fibres_2_is_cell'[of _ m])
  unfolding gs_defs apply blast
   apply(rule gs_defs, blast)
  by(rule Y1_closed)

lemma \<B>1_center: "\<And> f. f \<in> fs \<Longrightarrow> center (\<B>1 f) = c1"
  using fs_defs unfolding \<B>1_def refine_fibres_2_params by blast  

lemma \<B>2_center: "\<And> f. f \<in> gs \<Longrightarrow> center (\<B>2 f) = c2"
  using gs_defs unfolding \<B>2_def refine_fibres_2_params by blast 

lemma c1_x_closed1: "\<And>t x f. f \<in> fs \<Longrightarrow> t#x \<in> condition_to_set (\<B>1 f) \<Longrightarrow> c1 x \<in> carrier Q\<^sub>p"
  apply(rule SA_car_closed[of _ m], rule c1_closed)
  using  list_tl  \<B>1_arity  condition_to_set_memE by metis

lemma c1_x_closed2: "\<And>t x f. f \<in> gs \<Longrightarrow> t#x \<in> condition_to_set (\<B>2 f) \<Longrightarrow> c1 x \<in> carrier Q\<^sub>p"
  apply(rule SA_car_closed[of _ m], rule c1_closed)
  using condition_to_set_memE list_tl \<B>2_arity by metis

lemma c2_x_closed1: "\<And>t x f. f \<in> fs \<Longrightarrow> t#x \<in> condition_to_set (\<B>1 f) \<Longrightarrow> c2 x \<in> carrier Q\<^sub>p"
  apply(rule SA_car_closed[of _ m], rule c2_closed)
  using condition_to_set_memE list_tl \<B>1_arity by metis

lemma c2_x_closed2: "\<And>t x f. f \<in> gs \<Longrightarrow> t#x \<in> condition_to_set (\<B>2 f) \<Longrightarrow> c2 x \<in> carrier Q\<^sub>p"
  apply(rule SA_car_closed[of _ m], rule c2_closed)
  using condition_to_set_memE list_tl \<B>2_arity by metis

lemma c1_minus_c21: "\<And>t x f. f \<in> fs \<Longrightarrow> t#x \<in> condition_to_set (\<B>1 f) \<Longrightarrow> c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
  apply(rule nonzero_memI) using c1_x_closed1 c2_x_closed1 Qp.ring_simprules apply blast
  using \<B>2_neq c1_x_closed1 c2_x_closed1 Qp.ring_simprules 
  by (metis (no_types, opaque_lifting) \<B>1_neq Qp.r_right_minus_eq)

lemma c1_minus_c22: "\<And>t x f. f \<in> gs \<Longrightarrow> t#x \<in> condition_to_set (\<B>2 f) \<Longrightarrow> c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
  apply(rule nonzero_memI) using c1_x_closed2 c2_x_closed2 Qp.ring_simprules apply blast
  using \<B>2_neq c1_x_closed2 c2_x_closed2 Qp.ring_simprules 
  by (metis (no_types, opaque_lifting) \<B>2_neq Qp.r_right_minus_eq)  

definition N where N: "N = (SOME N. N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n))"

lemma N_def: "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
apply(rule some_fact[of N], rule N, rule nth_power_fact''[of n])
  using locale_assms by linarith 

lemma N_pos: "N > 1"
  using N_def by blast 

lemma N_fact: "\<And>u. u \<in> carrier Q\<^sub>p \<Longrightarrow> ac N u = 1 \<Longrightarrow> val u = 0 \<Longrightarrow> u \<in> P_set n"
  using N_def by blast 

text\<open>The function $f$ is just an arbitrary element of $fs$.\<close>


definition f where f: "f = (SOME f. f \<in> fs)"

lemma f_def: "f \<in> fs"
  apply(rule some_fact[of f], rule f)
  using fs_nonempty by auto 
end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Cutting a Cell $\mathcal{A}$ Into Three Pieces Along the Value Group\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context padic_fields
begin

lemma cell_intersection_same_center':
  assumes "is_cell_condition \<C>"
  assumes "is_cell_condition \<C>'"
  assumes "\<C> = Cond m C c a1 a2 I"
  assumes "\<C>' = Cond m C' c a1' a2' I'"
  shows "\<exists> \<C>''. is_cell_condition \<C>'' \<and> arity \<C>'' = m \<and> center \<C>'' = c 
                \<and> fibre_set \<C>'' = C \<inter> C' 
                \<and> condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
proof-
  obtain l u J where luJ_def: " is_convex_condition J \<and> l \<in> carrier (SA m) \<and> u \<in> carrier (SA m) \<and>
               (\<forall>x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). (J (val (l x)) (val (u x)) = I (val (a1 x)) (val (a2 x)) \<inter> I' (val (a1' x)) (val (a2' x))))"
    using convex_condition_intersection[of I I' a1 m a1' a2 a2'] assms[of ] 
    by (metis (mono_tags, lifting) is_cell_conditionE(3) is_cell_conditionE(4) is_cell_conditionE(5))
  obtain \<C>'' where def: "\<C>'' = Cond m (C \<inter> C') c l u J"
    by blast 
  have 0:"is_cell_condition \<C>''"
    apply(rule is_cell_conditionI)
    using assms
    unfolding def assms fibre_set.simps arity.simps center.simps l_bound.simps u_bound.simps boundary_condition.simps
        apply (meson is_cell_conditionE(1) padic_fields.intersection_is_semialg padic_fields_axioms)
    using assms padic_fields.is_cell_conditionE(2) padic_fields_axioms apply blast
    using assms luJ_def apply blast 
    using assms luJ_def apply blast 
    using assms luJ_def by blast 
  have 1: "condition_to_set \<C>'' = condition_to_set \<C> \<inter> condition_to_set \<C>'"
    unfolding assms def condition_to_set.simps 
    apply(rule equalityI')
     apply(rule IntI)
    apply(rule cell_memI) using cell_memE 
    apply blast
    using cell_memE(2) apply blast
  proof- 
    show " \<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
    proof-  fix x assume A: " x \<in> cell m (C \<inter> C') c l u J"
      have 0: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A cell_memE 
        by (meson Qp_pow_ConsE(1))
      have 1: " J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using "0" luJ_def by blast
      have 2: "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def cell_memE[of x m "C \<inter> C'" c l u J] IntE unfolding 1
        using A by blast
      thus "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x)))"
        by blast 
    qed
    show "\<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> x \<in> cell m C' c a1' a2' I'"
      apply(rule cell_memI)
      using cell_memE(1) apply blast
      using cell_memE(2) apply blast
    proof- 
    show " \<And>x. x \<in> cell m (C \<inter> C') c l u J \<Longrightarrow> val (lead_coeff x \<ominus> c (tl x)) \<in> I' (val (a1' (tl x))) (val (a2' (tl x)))"
    proof-  fix x assume A: " x \<in> cell m (C \<inter> C') c l u J"
      have 0: "tl x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A cell_memE 
        by (meson Qp_pow_ConsE(1))
      have 1: " J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using "0" luJ_def by blast
      have 2: "val (lead_coeff x \<ominus> c (tl x)) \<in> I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def cell_memE[of x m "C \<inter> C'" c l u J] IntE unfolding 1
        using A by blast
      thus "val (lead_coeff x \<ominus> c (tl x)) \<in> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        by blast 
    qed
    qed
    show "\<And>x. x \<in> cell m C c a1 a2 I \<inter> cell m C' c a1' a2' I' \<Longrightarrow> x \<in> cell m (C \<inter> C') c l u J"
      apply(rule cell_memI)
        apply (meson Int_iff cell_memE(1))
      using cell_memE(2) apply blast
    proof- 
      fix x assume A: "x \<in> cell m C c a1 a2 I \<inter> cell m C' c a1' a2' I'"
      then have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        by (meson basic_trans_rules(31) cell_subset inf_le1)
      have 0:" J (val (l (tl x))) (val (u (tl x))) = I (val (a1 (tl x))) (val (a2 (tl x))) \<inter> I' (val (a1' (tl x))) (val (a2' (tl x)))"
        using luJ_def x_closed Qp_pow_ConsE(1) by blast
      show "val (lead_coeff x \<ominus> c (tl x)) \<in> J (val (l (tl x))) (val (u (tl x)))"
        unfolding 0 using A cell_memE[of x m C' c a1' a2' I'] cell_memE[of x m C c a1 a2 I] 
        by (metis Int_iff Qp_pow_ConsE(1) luJ_def)
    qed
  qed
  show ?thesis using def assms fibre_set.simps
    by (metis (mono_tags, opaque_lifting) "0" "1" assms(4) cell_condition.simps(1) center.simps 
              padic_fields.condition_decomp' padic_fields_axioms)
qed

lemma bottom_cell_cut_ex: 
  assumes "n > 0"
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes "is_cell_condition \<A>"
  assumes "center \<A> = c1"
  assumes "arity \<A> = m"
  assumes "fibre_set \<A> = A"
  assumes "c2 \<in> carrier (SA m)"
  assumes "\<And>x. x \<in> A \<Longrightarrow> c1 x \<noteq> c2 x"
  shows "\<exists>\<A>1. is_cell_condition \<A>1 \<and> arity \<A>1 = arity \<A> \<and> center \<A>1 = center \<A> \<and> fibre_set \<A>1 = A \<and>
                                    condition_to_set \<A>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N)  } "
proof- 
  obtain a1 a2 I where params: "\<A> = Cond m A c1 a1 a2 I"
    using assms(3,4,5,6) equal_CondI by blast
  have c1_closed: "c1 \<in> carrier (SA m)"
    using assms  is_cell_conditionE by (metis params)
  obtain h where h_def: "h = c2 \<ominus>\<^bsub>SA m\<^esub> c1"
    by blast 
  have h_closed: "h \<in> carrier (SA m)"
    using h_def assms c1_closed by blast
  obtain g where g_def: "g = (\<pp>[^](-N)) \<odot>\<^bsub>SA m\<^esub> h"
    by blast 
  have g_closed: "g \<in> carrier (SA m)"
    unfolding g_def using h_def SA_smult_closed h_closed p_intpow_closed(1) by blast
  obtain \<C> where \<C>_def: "\<C> = Cond m A c1 c1 g open_ray"
    by blast 
  have \<C>_cell: "is_cell_condition \<C>"
    unfolding \<C>_def 
    apply(rule is_cell_conditionI')
    using assms(3) is_cell_conditionE'(1)[of \<A>] unfolding assms(5,6) apply blast
       apply(rule c1_closed, rule c1_closed)
     apply(rule g_closed)
    unfolding is_convex_condition_def by blast
  obtain \<A>1 where \<A>1_def: "is_cell_condition \<A>1 \<and> arity \<A>1 = m \<and> center \<A>1 = c1 \<and> fibre_set \<A>1 = A \<inter> A \<and> condition_to_set \<A>1 = condition_to_set \<A> \<inter> condition_to_set \<C>"
    using cell_intersection_same_center'[of \<A> \<C> m A c1 a1 a2 I A c1 g open_ray] 
          \<C>_cell assms(3) \<C>_def params 
    by auto 
  have 0: "condition_to_set \<A>1 = condition_to_set \<A> \<inter> condition_to_set \<C>"
    using \<A>1_def by blast 
  have 1: "\<And>xs. xs \<in> condition_to_set \<C> \<Longrightarrow> xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> 
                  val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < - N"
  proof- 
    fix xs assume A: "xs \<in> condition_to_set \<C>"
    then have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding \<C>_def condition_to_set.simps cell_def by blast 
     obtain t x where tx_def: "xs = t#x"
       using xs_closed Qp_pow_Suc_decomp by blast  
     have t_closed: "t \<in> carrier Q\<^sub>p"
       using xs_closed unfolding tx_def  
       by (metis Qp_pow_ConsE list_hd)
     have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using xs_closed unfolding tx_def 
       by (metis Qp_pow_ConsE(1) list_tl)
     have 10: "x \<in> A"
       using A unfolding tx_def \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
     have 11: "c1 x \<noteq> c2 x"
       using 10 assms by blast 
     have 12: "h x = c2 x \<ominus> c1 x"
       unfolding h_def using x_closed c1_closed assms 
       by (meson SA_minus_eval)
     have 13: "h x \<in> carrier Q\<^sub>p"
       using h_closed x_closed SA_car_closed by blast
     have 14: "h x \<noteq> \<zero>"
       unfolding 12 using assms c1_closed x_closed 11 Qp.r_right_minus_eq SA_car_closed by presburger
     have 15: "g x = \<pp>[^](-N) \<otimes> h x"
       unfolding g_def using h_closed x_closed  
       using SA_smult_formula p_intpow_closed(1) by blast
     have 16: "g x \<in> nonzero Q\<^sub>p"
       unfolding 15 using 13 14 
       by (metis Qp.integral Qp.m_closed Qp.not_nonzero_memE Qp.not_nonzero_memI p_intpow_closed(1) p_intpow_closed(2))
     have 17: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                      val a < val (b \<otimes> c) \<Longrightarrow> val (a \<div> c) < val b"
       using Qp.cring_simprules(14) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right val_ineq_cancel_le by presburger
     have 18: "val (t \<ominus> c1 x) < val (g x)"
       using A unfolding tx_def condition_to_set.simps \<C>_def cell_def mem_Collect_eq list_tl list_hd open_ray_def 
       by blast 
     have 19: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) <  val (\<pp> [^] - int N)"
       apply(rule 17[of "t \<ominus> c1 x" "\<pp>[^](-N)" "c2 x \<ominus> c1 x"  ])
       using t_closed c1_closed x_closed SA_car_closed apply blast
       using p_intpow_closed(1) apply blast
       using x_closed h_closed 14  12 11 Qp.not_eq_diff_nonzero SA_car_closed assms  c1_closed apply presburger
       using 18 unfolding 15 12 by blast 
     show " xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) < eint (- int N)"
       using xs_closed 19 
       unfolding val_p_int_pow tx_def assms center.simps list_tl list_hd 
       by blast 
  qed
  have 2: "\<And>xs. xs \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N) }
          \<Longrightarrow> xs \<in> condition_to_set \<C>"
  proof- 
    fix xs 
    assume A: "xs \<in>  {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < - N }"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
     have 10: "x \<in> A"
       using A unfolding tx_def \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
     have 11: "c1 x \<noteq> c2 x"
       using 10 assms by blast 
     have 12: "h x = c2 x \<ominus> c1 x"
       unfolding h_def using x_closed c1_closed assms 
       by (meson SA_minus_eval)
     have 13: "h x \<in> carrier Q\<^sub>p"
       using h_closed x_closed SA_car_closed by blast
     have 14: "h x \<noteq> \<zero>"
       unfolding 12 using assms c1_closed x_closed 11 Qp.r_right_minus_eq SA_car_closed by presburger
     have 15: "g x = \<pp>[^](-N) \<otimes> h x"
       unfolding g_def using h_closed x_closed  
       using SA_smult_formula p_intpow_closed(1) by blast
     have 16: "g x \<in> nonzero Q\<^sub>p"
       unfolding 15 using 13 14 
       by (metis Qp.integral Qp.m_closed Qp.not_nonzero_memE Qp.not_nonzero_memI p_intpow_closed(1) p_intpow_closed(2))
     have 17: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> val (a \<div> c) < val b \<Longrightarrow>
                      val a < val (b \<otimes> c) "
       by (metis (no_types, lifting) Groups.add_ac(2) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right val_ineq_cancel_le' val_mult)
     have 18: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) < eint (- int N)"
       using A unfolding mem_Collect_eq list_tl list_hd tx_def assms center.simps by blast 
     have 19: " val (t \<ominus> c1 x) < val (\<pp> [^] - int N \<otimes> (c2 x \<ominus> c1 x))"
       apply(rule 17[of "t \<ominus> c1 x" "\<pp>[^](-N)" "c2 x \<ominus> c1 x"])
       using t_closed x_closed SA_car_closed c1_closed apply blast
       using p_intpow_closed(1) apply blast
       using x_closed h_closed 14  12 11 Qp.not_eq_diff_nonzero SA_car_closed assms  c1_closed apply presburger
       unfolding val_p_int_pow by(rule 18)
     show " xs \<in> condition_to_set \<C>"
       using xs_closed 19 10
       unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq tx_def list_tl list_hd
         open_ray_def 15 12
       by blast 
  qed
  have 3: "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N)  } = 
          condition_to_set \<C>"
    apply(rule equalityI')
    using 2 apply blast
    using 1 unfolding mem_Collect_eq \<C>_def condition_to_set.simps cell_def by blast 
  have 4: " condition_to_set \<A>1 = condition_to_set \<A> \<inter>
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < - N }"
    unfolding 0 unfolding 3  by blast  
  have 5: " is_cell_condition \<A>1 \<and>
          arity \<A>1 = arity \<A> \<and>
          center \<A>1 = center \<A> \<and>
          condition_to_set \<A>1 =
          condition_to_set \<A> \<inter>
          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl xs \<in> A \<and> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) < eint (-int N)}"
    apply(rule conjI) 
    using \<A>1_def apply blast
    unfolding assms arity.simps center.simps
    apply(rule conjI) 
    using \<A>1_def apply blast
    apply(rule conjI) 
    using \<A>1_def apply blast
    unfolding 4 assms center.simps 
    by blast 
  thus ?thesis using \<A>1_def by blast 
qed

lemma top_cell_cut_ex: 
  assumes " n> 0"
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes "is_cell_condition \<A>"
  assumes "center \<A> = c1"
  assumes "arity \<A> = m"
  assumes "fibre_set \<A> = A"
  assumes "c2 \<in> carrier (SA m)"
  assumes "\<And>x. x \<in> A \<Longrightarrow> c1 x \<noteq> c2 x"
  shows "\<exists>\<A>1. is_cell_condition \<A>1 \<and> arity \<A>1 = arity \<A> \<and> center \<A>1 = center \<A> \<and> fibre_set \<A>1 = A \<and>
                                    condition_to_set \<A>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N  } "
proof- 
  obtain a1 a2 I where params: "\<A> = Cond m A c1 a1 a2 I"
    using assms(3,4,5,6) equal_CondI by blast
  have c1_closed: "c1 \<in> carrier (SA m)"
    using assms params by auto  
  obtain h where h_def: "h = c2 \<ominus>\<^bsub>SA m\<^esub> c1"
    by blast 
  have h_closed: "h \<in> carrier (SA m)"
    using h_def assms c1_closed by blast
  obtain g where g_def: "g = (\<pp>[^]N) \<odot>\<^bsub>SA m\<^esub> h"
    by blast 
  have g_closed: "g \<in> carrier (SA m)"
    unfolding g_def using h_def SA_smult_closed h_closed p_natpow_closed(1) by blast
  obtain \<C> where \<C>_def: "\<C> = Cond m A c1 g (\<cc>\<^bsub>m\<^esub>\<zero>) closed_interval"
    by blast 
  have \<C>_cell: "is_cell_condition \<C>"
    unfolding \<C>_def 
    apply(rule is_cell_conditionI')
    using assms(3) is_cell_conditionE'(1)[of \<A>] unfolding assms(5,6) apply blast
       apply(rule c1_closed, rule g_closed)
    using constant_fun_closed apply blast
    unfolding is_convex_condition_def by blast
  obtain \<A>1 where \<A>1_def: "is_cell_condition \<A>1 \<and> arity \<A>1 = m \<and> center \<A>1 = c1 \<and> fibre_set \<A>1 = A \<inter> A \<and> condition_to_set \<A>1 = condition_to_set \<A> \<inter> condition_to_set \<C>"
    using cell_intersection_same_center'[of \<A> \<C> m A c1 a1 a2 I A g "\<cc>\<^bsub>m\<^esub>\<zero>" closed_interval] 
          \<C>_cell assms \<C>_def params by auto 
  have 0: "condition_to_set \<A>1 = condition_to_set \<A> \<inter> condition_to_set \<C>"
    using \<A>1_def by blast 
  have 1: "\<And>xs. xs \<in> condition_to_set \<C> \<Longrightarrow> xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> 
                  val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N"
  proof- 
    fix xs assume A: "xs \<in> condition_to_set \<C>"
    then have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding \<C>_def condition_to_set.simps cell_def by blast 
     obtain t x where tx_def: "xs = t#x"
       using xs_closed Qp_pow_Suc_decomp by blast  
     have t_closed: "t \<in> carrier Q\<^sub>p"
       using xs_closed unfolding tx_def  
       by (metis Qp_pow_ConsE list_hd)
     have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
       using xs_closed unfolding tx_def 
       by (metis Qp_pow_ConsE(1) list_tl)
     have 10: "x \<in> A"
       using A unfolding tx_def \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
     have 11: "c1 x \<noteq> c2 x"
       using 10 assms by blast 
     have 12: "h x = c2 x \<ominus> c1 x"
       unfolding h_def using x_closed c1_closed assms 
       by (meson SA_minus_eval)
     have 13: "h x \<in> carrier Q\<^sub>p"
       using h_closed x_closed SA_car_closed by blast
     have 14: "h x \<noteq> \<zero>"
       unfolding 12 using assms c1_closed x_closed 11 Qp.r_right_minus_eq SA_car_closed by presburger
     have 15: "g x = \<pp>[^]N \<otimes> h x"
       unfolding g_def using h_closed x_closed  
       using SA_smult_formula p_natpow_closed(1) by blast
     have 16: "g x \<in> nonzero Q\<^sub>p"
       unfolding 15 using 13 14 
       by (metis Qp.integral Qp.m_closed Qp.not_nonzero_memE Qp.not_nonzero_memI p_natpow_closed(1) p_natpow_closed(2))
     have 17: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                      val a \<ge> val (b \<otimes> c) \<Longrightarrow> val (a \<div> c) \<ge> val b"
       using Qp.cring_simprules(14) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right val_ineq_cancel_leq by presburger
     have 18: "val (t \<ominus> c1 x) \<ge> val (g x)"
       using A unfolding tx_def condition_to_set.simps \<C>_def cell_def mem_Collect_eq list_tl list_hd closed_interval_def 
       by blast 
     have 19: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<ge>  val (\<pp> [^] N)"
       apply(rule 17[of "t \<ominus> c1 x" "\<pp>[^]N" "c2 x \<ominus> c1 x"  ])
       using t_closed c1_closed x_closed SA_car_closed apply blast
       using p_intpow_closed(1) apply blast
       using x_closed h_closed 14  12 11 Qp.not_eq_diff_nonzero SA_car_closed assms c1_closed apply presburger
       using 18 unfolding 15 12 by blast 
     have 20: "val (\<pp>[^]N) = N"
       by (metis int_pow_int val_p_int_pow)
     show " xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) \<ge> eint ( int N)"
       using xs_closed 19 
       unfolding  tx_def  center.simps list_tl list_hd 20 params
       by auto        
  qed
  have 2: "\<And>xs. xs \<in> {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint N }
          \<Longrightarrow> xs \<in> condition_to_set \<C>"
  proof- 
    fix xs 
    assume A: "xs \<in>  {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N }"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
     have 10: "x \<in> A"
       using A unfolding tx_def \<C>_def condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
     have 11: "c1 x \<noteq> c2 x"
       using 10 assms by blast 
     have 12: "h x = c2 x \<ominus> c1 x"
       unfolding h_def using x_closed c1_closed assms 
       by (meson SA_minus_eval)
     have 13: "h x \<in> carrier Q\<^sub>p"
       using h_closed x_closed SA_car_closed by blast
     have 14: "h x \<noteq> \<zero>"
       unfolding 12 using assms c1_closed x_closed 11 Qp.r_right_minus_eq SA_car_closed by presburger
     have 15: "g x = \<pp>[^]N \<otimes> h x"
       unfolding g_def using h_closed x_closed  
       using SA_smult_formula p_natpow_closed(1) by blast
     have 16: "g x \<in> nonzero Q\<^sub>p"
       unfolding 15 using 13 14 
       by (metis Qp.integral Qp.m_closed Qp.not_nonzero_memE Qp.not_nonzero_memI p_natpow_closed(1) p_natpow_closed(2))
     have 17: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> val (a \<div> c) \<ge> val b \<Longrightarrow>
                      val a \<ge> val (b \<otimes> c) "
       by (metis (no_types, lifting) Qp.cring_simprules(14) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right val_ineq_cancel_leq')
     have 18: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<ge> N"
       using A unfolding mem_Collect_eq list_tl list_hd tx_def assms center.simps by blast 
     have 19: " val (t \<ominus> c1 x) \<ge> val (\<pp> [^] N \<otimes> (c2 x \<ominus> c1 x))"
       apply(rule 17[of "t \<ominus> c1 x" "\<pp>[^]N" "c2 x \<ominus> c1 x"])
       using t_closed x_closed SA_car_closed c1_closed apply blast
       using p_intpow_closed(1) apply blast
       using x_closed h_closed 14  12 11 Qp.not_eq_diff_nonzero SA_car_closed assms c1_closed apply presburger
       using int_pow_int val_p_int_pow 18 
       by metis
     have 20: "(\<cc>\<^bsub>m\<^esub>\<zero>) x = \<zero>"
       using x_closed constant_functionE by blast 
     show " xs \<in> condition_to_set \<C>"
       using xs_closed 19 10
       unfolding \<C>_def condition_to_set.simps cell_def mem_Collect_eq tx_def list_tl list_hd
         closed_interval_def 15 12 20 val_zero 
       using eint_ord_simps(3) by blast
  qed
  have 3: "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint N  } = 
          condition_to_set \<C>"
    apply(rule equalityI')
    using 2 apply blast
    using 1 unfolding mem_Collect_eq \<C>_def condition_to_set.simps cell_def by blast 

  have 4: " condition_to_set \<A>1 = condition_to_set \<A> \<inter>
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge>N }"
    unfolding 0 unfolding 3  by blast  
  have 5: " is_cell_condition \<A>1 \<and>
          arity \<A>1 = arity \<A> \<and>
          center \<A>1 = center \<A> \<and>
          condition_to_set \<A>1 =
          condition_to_set \<A> \<inter>
          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). tl xs \<in> A \<and> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) \<ge> N}"
    apply(rule conjI) 
    using \<A>1_def apply blast
    unfolding assms arity.simps center.simps
    apply(rule conjI) 
    using \<A>1_def apply blast
    apply(rule conjI) 
    using \<A>1_def apply blast
    unfolding 4 assms center.simps 
    by blast 
  thus ?thesis using \<A>1_def by blast 
qed

lemma middle_cell_cut_ex: 
  assumes " n> 0"
  assumes "N > 1 \<and> (\<forall>u\<in>carrier Q\<^sub>p. ac N u = 1 \<and> val u = 0 \<longrightarrow> u \<in> P_set n)"
  assumes "is_cell_condition \<A>"
  assumes "center \<A> = c1"
  assumes "arity \<A> = m"
  assumes "fibre_set \<A> = A"
  assumes "c2 \<in> carrier (SA m)"
  assumes "\<And>x. x \<in> A \<Longrightarrow> c1 x \<noteq> c2 x"
  shows "\<exists>\<A>1. is_cell_condition \<A>1 \<and> arity \<A>1 = arity \<A> \<and> center \<A>1 = center \<A> \<and> fibre_set \<A>1 = A  \<and>
                                    condition_to_set \<A>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> A \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint (-N) \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < N  } "
proof-
  obtain a1 a2 I where params: "\<A> = Cond m A c1 a1 a2 I"
    using assms(3,4,5,6) equal_CondI by blast
  have c1_closed: "c1 \<in> carrier (SA m)"
    using assms params by auto  
  obtain h where h_def: "h = c2 \<ominus>\<^bsub>SA m\<^esub> c1"
    by blast 
  have h_closed: "h \<in> carrier (SA m)"
    using h_def assms c1_closed by blast
  obtain g2 where g2_def: "g2 = (\<pp>[^]N) \<odot>\<^bsub>SA m\<^esub> h"
    by blast 
  have g2_closed: "g2 \<in> carrier (SA m)"
    unfolding g2_def using h_def SA_smult_closed h_closed p_natpow_closed(1) by blast
  obtain g1 where g1_def: "g1 = (\<pp>[^](-N)) \<odot>\<^bsub>SA m\<^esub> h"
    by blast 
  have g1_closed: "g1 \<in> carrier (SA m)"
    unfolding g1_def using h_def SA_smult_closed h_closed p_intpow_closed(1) by blast
  obtain \<C> where \<C>_def: "\<C> = Cond m A c1 g1 g2 left_closed_interval"
    by blast 
  have \<C>_cell: "is_cell_condition \<C>"
    unfolding \<C>_def 
    apply(rule is_cell_conditionI')
    using assms(3) is_cell_conditionE'(1)[of \<A>] unfolding assms(5,6) apply blast
       apply(rule c1_closed, rule g1_closed)
    using g2_closed apply blast
    unfolding is_convex_condition_def by blast
  have A_closed: "A \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
    using \<C>_cell \<C>_def is_cell_conditionE(1) is_semialgebraic_closed by blast
  have 0: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> carrier Q\<^sub>p \<Longrightarrow> 
              val y < val (g2 x) \<longleftrightarrow> val (y \<div> (c2 x \<ominus> c1 x)) < N"
  proof- 
    fix x y assume A: "x \<in> A" "y \<in> carrier Q\<^sub>p"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A A_closed by blast 
    have 00: "g2 x = \<pp>[^]N \<otimes> h x"
      unfolding g2_def using h_closed x_closed SA_smult_formula p_natpow_closed(1) by blast
    have 01: "val (\<pp>[^]N) = N"
      by (metis int_pow_int val_p_int_pow)
    have 02: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                  (val a < val (b \<otimes>c) \<longleftrightarrow> val (a \<div> c) < val b)"
      by (metis (no_types, opaque_lifting) Qp.cring_simprules(14) Qp.cring_simprules(5) Qp.nonzero_memE(1) local.fract_cancel_right nonzero_inverse_Qp val_ineq_cancel_le val_ineq_cancel_le')
    have 03: "h x = c2 x \<ominus> c1 x"
      unfolding h_def 
      by (metis (no_types, opaque_lifting) A(1) SA_minus_eval \<C>_cell \<C>_def assms  c1_closed h_def is_cell_conditionE(1) is_semialgebraic_closed subsetD)
    have " (val y < val (g2 x)) = (val (y \<div> c2 x \<ominus> c1 x) < val (\<pp>[^]N)) "
      unfolding 00 03 
      apply(rule 02, rule A)
       apply blast
      using A assms(8)[of x] c1_closed assms SA_car_closed 
      by (metis Qp.not_eq_diff_nonzero x_closed)
    thus " val y < val (g2 x) \<longleftrightarrow> val (y \<div> (c2 x \<ominus> c1 x)) < N"
      unfolding 01 by blast 
  qed
  have 1: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> carrier Q\<^sub>p \<Longrightarrow> 
              val y \<ge> val (g1 x) \<longleftrightarrow> val (y \<div> (c2 x \<ominus> c1 x)) \<ge> eint (- N)"
  proof- 
    fix x y assume A: "x \<in> A" "y \<in> carrier Q\<^sub>p"
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using A A_closed by blast 
    have 00: "g1 x = \<pp>[^](-N) \<otimes> h x"
      unfolding g1_def using h_closed x_closed SA_smult_formula p_intpow_closed by blast
    have 01: "val (\<pp>[^]-N) = eint (-N)"
      by (metis val_p_int_pow)
    have 02: "\<And> a b c. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                  (val a \<ge> val (b \<otimes>c) \<longleftrightarrow> val (a \<div> c) \<ge> val b)"
      by (metis (no_types, opaque_lifting) Qp.cring_simprules(14) Qp.cring_simprules(5) Qp.nonzero_memE(1) local.fract_cancel_right nonzero_inverse_Qp val_ineq_cancel_leq val_ineq_cancel_leq')
    have 03: "h x = c2 x \<ominus> c1 x"
      unfolding h_def 
      by (metis (no_types, opaque_lifting) A(1) SA_minus_eval \<C>_cell \<C>_def assms c1_closed h_def is_cell_conditionE(1) is_semialgebraic_closed subsetD)
    have " (val y \<ge> val (g1 x)) = (val (y \<div> c2 x \<ominus> c1 x) \<ge> val (\<pp>[^]-N)) "
      unfolding 00 03 
      apply(rule 02, rule A)
      using p_intpow_closed(1) apply blast
      using A assms(8)[of x] c1_closed assms SA_car_closed 
      by (metis Qp.not_eq_diff_nonzero x_closed)
    thus "(val (g1 x) \<le> val y) = (eint (- int N) \<le> val (y \<div> c2 x \<ominus> c1 x))"
      unfolding 01 by auto  
  qed
  have 2: "{xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
           tl xs \<in> A \<and>
           eint (- int N) \<le> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) \<and>
           val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) < eint (int N)} = 
            condition_to_set \<C>"
    apply(rule equalityI')
    unfolding mem_Collect_eq \<C>_def condition_to_set.simps
     apply(rule cell_memI)
    apply blast
    apply blast
     apply(rule left_closed_interval_memI)
    using 1 
    apply (metis Qp.cring_simprules(4) Qp_pow_ConsE(1) Qp_pow_ConsE(2) \<C>_cell \<C>_def assms(4) center.simps is_cell_condition_closure'(1))
    using 0 
    apply (metis Qp.cring_simprules(4) Qp_pow_ConsE(1) Qp_pow_ConsE(2) \<C>_cell \<C>_def assms(4) center.simps is_cell_condition_closure'(1))
    apply(rule conjI)
    using cell_def apply blast
    apply(rule conjI)
    using cell_def apply blast
    apply(rule conjI)
    using 1 cell_memE(3)[of _ m A c2 g1 g2 left_closed_interval]
            left_closed_interval_memE(1)
    apply (metis Qp.cring_simprules(4) Qp_pow_ConsE(1) Qp_pow_ConsE(2) \<C>_cell \<C>_def assms(4) cell_memE(1) cell_memE(2) cell_memE(3) is_cell_condition_closure'(1) padic_fields.condition_decomp(3) padic_fields_axioms)
    using 0 cell_memE(3)[of _ m A c2 g1 g2 left_closed_interval]
            left_closed_interval_memE(2)
    by (metis Qp.cring_simprules(4) Qp_pow_ConsE(1) Qp_pow_ConsE(2) \<C>_cell \<C>_def assms(4) cell_memE(1) cell_memE(2) cell_memE(3) is_cell_condition_closure'(1) padic_fields.condition_decomp(3) padic_fields_axioms)
  obtain \<A>1 where \<A>1_def: "is_cell_condition \<A>1 \<and> arity \<A>1 = m \<and> center \<A>1 = c1 \<and> fibre_set \<A>1 = A \<inter> A \<and>condition_to_set \<A>1 = condition_to_set \<A> \<inter> condition_to_set \<C>"
    using cell_intersection_same_center'[of \<A> \<C> m A c1 a1 a2 I A g1 g2 left_closed_interval] 
          \<C>_cell assms \<C>_def params by blast 
  have 3: " is_cell_condition \<A>1 \<and>
          arity \<A>1 = arity \<A> \<and>
          center \<A>1 = center \<A>"
    using \<A>1_def unfolding assms arity.simps center.simps by blast 
  have 4: "is_cell_condition \<A>1 \<and>
          arity \<A>1 = arity \<A> \<and>
          center \<A>1 = center \<A> \<and>
          condition_to_set \<A>1 =
          condition_to_set \<A> \<inter>
          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>).
           tl xs \<in> A \<and>
           eint (- int N) \<le> val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) \<and>
           val (hd xs \<ominus> center \<A> (tl xs) \<div> c2 (tl xs) \<ominus> center \<A> (tl xs)) < eint (int N)}"
    using 3 \<A>1_def unfolding 2 by blast 
  thus ?thesis using \<A>1_def by blast 
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection\<open>Completing the Reduction\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context two_preparable_to_one_preparable_reduction
begin

definition \<A> where \<A>_def: "\<A> = \<B>1 f"

definition C where C_def: "C = fibre_set \<A>"

lemma C_sub: "C \<subseteq> carrier (Q\<^sub>p\<^bsup>m\<^esup>) - {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). c1 x = c2 x}"
  unfolding C_def \<A>_def \<B>1_def refine_fibres_2_def  refine_fibres_def fibre_set.simps Y1_def Y0_def
  by auto 

lemma \<A>_cell: "is_cell_condition \<A>"
  unfolding \<A>_def using \<B>1_cond f_def by blast

lemma \<A>_arity: "arity \<A> = m"
  unfolding \<A>_def by(rule \<B>1_arity, rule f_def)

lemma \<A>_center: "center \<A> = c1"
  unfolding \<A>_def by(rule \<B>1_center, rule f_def)

lemma \<A>_fibres: "fibre_set \<A> = C"
  unfolding C_def by auto 

definition a1 where a1_def: "a1 = l_bound \<A>"
definition a2 where a2_def: "a2 = u_bound \<A>"
definition I where I_def: "I = boundary_condition \<A>"

lemma \<A>_eq: "\<A> = Cond m C c1 a1 a2 I"
  using \<A>_center unfolding a1_def a2_def I_def C_def 
  by (metis \<A>_arity condition_decomp')

definition \<C>1 where \<C>1: "\<C>1 = (SOME \<C>1. is_cell_condition \<C>1 \<and> arity \<C>1 = arity \<A> \<and> center \<C>1 = center \<A> \<and>  fibre_set \<C>1 = C \<and>
                                    condition_to_set \<C>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- (int N))  })"

lemma \<C>1_def: "is_cell_condition \<C>1 \<and> arity \<C>1 = arity \<A> \<and> center \<C>1 = center \<A> \<and>  fibre_set \<C>1 = C \<and>
                                    condition_to_set \<C>1 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N)  }"
  apply(rule some_fact[of \<C>1], rule \<C>1, rule bottom_cell_cut_ex[of n _ _ c1], 
              intro locale_assms, rule N_def, rule \<A>_cell, rule \<A>_center, rule \<A>_arity, rule \<A>_fibres, rule c2_closed)
  by (simp add: C_def Y0_def Y1_def \<A>_def \<B>1_def refine_fibres_2_params(6))


definition \<C>2 where \<C>2: "\<C>2 = (SOME \<C>2. is_cell_condition \<C>2 \<and> arity \<C>2 = arity \<A> \<and> center \<C>2 = center \<A> \<and>fibre_set \<C>2 = C \<and>
                                    condition_to_set \<C>2 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N  })"

lemma \<C>2_def: "is_cell_condition \<C>2 \<and> arity \<C>2 = arity \<A> \<and> center \<C>2 = center \<A> \<and>fibre_set \<C>2 = C \<and>
                                    condition_to_set \<C>2 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N  }"
  apply(rule some_fact[of \<C>2], rule \<C>2, rule top_cell_cut_ex[of n _ _ c1], 
              intro locale_assms, rule N_def, rule \<A>_cell, rule \<A>_center, rule \<A>_arity, rule \<A>_fibres, rule c2_closed)
  by (simp add: C_def Y0_def Y1_def \<A>_def \<B>1_def refine_fibres_2_params(6))

definition \<C>3 where \<C>3: "\<C>3 = (SOME \<C>3. is_cell_condition \<C>3 \<and> arity \<C>3 = arity \<A> \<and> center \<C>3 = center \<A> \<and> fibre_set \<C>3 = C \<and>
                                    condition_to_set \<C>3 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint (-N) \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < N  })"

lemma \<C>3_def: "is_cell_condition \<C>3 \<and> arity \<C>3 = arity \<A> \<and> center \<C>3 = center \<A> \<and> fibre_set \<C>3 = C \<and>
                                    condition_to_set \<C>3 = condition_to_set \<A> \<inter> 
                                          {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint (-N) \<and>
             val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < N  }"
  apply(rule some_fact[of \<C>3], rule \<C>3, rule middle_cell_cut_ex[of n _ _ c1], 
              intro locale_assms, rule N_def, rule \<A>_cell, rule \<A>_center, rule \<A>_arity, rule \<A>_fibres, rule c2_closed)
  by (simp add: C_def Y0_def Y1_def \<A>_def \<B>1_def refine_fibres_2_params(6))

lemma \<C>1_eq: "condition_to_set \<C>1 = condition_to_set \<A> \<inter> 
                                        {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < eint (- N)  }"
  using \<C>1_def by blast 

lemma \<C>2_eq: "condition_to_set \<C>2 = condition_to_set \<A> \<inter> 
                                        {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and> val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> N  }"
  using \<C>2_def by blast 

lemma \<C>3_eq: "  condition_to_set \<C>3 = condition_to_set \<A> \<inter> 
                                        {xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>). (tl xs) \<in> C \<and>
           val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) \<ge> eint (-N) \<and>
           val ((hd xs \<ominus> (center \<A>) (tl xs)) \<div> (c2 (tl xs) \<ominus> (center \<A>) (tl xs))) < N  } "
  using \<C>3_def by blast 

lemma \<C>1_cell: "is_cell_condition \<C>1"
  using \<C>1_def by auto 

lemma \<C>2_cell: "is_cell_condition \<C>2"
  using \<C>2_def by auto 

lemma \<C>3_cell: "is_cell_condition \<C>3"
  using \<C>3_def by auto 

lemma \<C>1_center: "center \<C>1 = c1"
  using \<C>1_def unfolding \<A>_center by auto 

lemma \<C>2_center: "center \<C>2 = c1"
  using \<C>2_def unfolding \<A>_center by auto 

lemma \<C>3_center: "center \<C>3 = c1"
  using \<C>3_def unfolding \<A>_center by auto 

lemma \<C>1_arity: "arity \<C>1 = m"
  using \<C>1_def unfolding \<A>_arity by auto 

lemma \<C>2_arity: "arity \<C>2 = m"
  using \<C>2_def unfolding \<A>_arity by auto 

lemma \<C>3_arity: "arity \<C>3 = m"
  using \<C>3_def unfolding \<A>_arity by auto 

definition q1 where q1_def: "q1 = l_bound \<C>1"
definition q2 where q2_def: "q2 = u_bound \<C>1"
definition J1 where J1_def: "J1 = boundary_condition \<C>1"

lemma \<C>1_params: "\<C>1 = Cond m C c1 q1 q2 J1"
  using \<C>1_center unfolding q1_def q2_def J1_def C_def 
  by (metis C_def \<C>1_arity \<C>1_def condition_decomp')

definition w1 where w1_def: "w1 = l_bound \<C>2"
definition w2 where w2_def: "w2 = u_bound \<C>2"
definition J2 where J2_def: "J2 = boundary_condition \<C>2"

lemma \<C>2_params: "\<C>2 = Cond m C c1 w1 w2 J2"
  using \<C>2_center unfolding w1_def w2_def J2_def C_def 
    by (metis C_def \<C>2_arity \<C>2_def condition_decomp')

definition e1 where e1_def: "e1 = l_bound \<C>3"
definition e2 where e2_def: "e2 = u_bound \<C>3"
definition J3 where J3_def: "J3 = boundary_condition \<C>3"

lemma \<C>3_params: "\<C>3 = Cond m C c1 e1 e2 J3"
  using \<C>3_center unfolding e1_def e2_def J3_def C_def 
    by (metis C_def \<C>3_arity \<C>3_def condition_decomp')

lemma \<C>1_closed: "condition_to_set \<C>1 \<subseteq> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  unfolding \<C>1_eq by auto 

lemma \<C>2_closed: "condition_to_set \<C>2 \<subseteq> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  unfolding \<C>2_eq by auto 

lemma \<C>3_closed: "condition_to_set \<C>3 \<subseteq> (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
  unfolding \<C>3_eq by auto 

lemma \<C>1_subset: "condition_to_set \<C>1 \<subseteq> condition_to_set \<A>"
  unfolding \<C>1_eq by auto 

lemma \<C>2_subset: "condition_to_set \<C>2 \<subseteq> condition_to_set \<A>"
  unfolding \<C>2_eq by auto 

lemma \<C>3_subset: "condition_to_set \<C>3 \<subseteq> condition_to_set \<A>"
  unfolding \<C>3_eq by auto 

lemma \<C>1_memE: 
  assumes "(t#x) \<in> condition_to_set \<C>1" 
  shows "val ((t \<ominus> c1 x) \<div> (c2 x \<ominus> c1 x)) < eint (-N)"
  using assms unfolding \<C>1_eq Int_iff mem_Collect_eq list_tl list_hd \<A>_center by auto 

lemma \<C>2_memE: 
  assumes "(t#x) \<in> condition_to_set \<C>2" 
  shows "val ((t \<ominus> c1 x) \<div> (c2 x \<ominus> c1 x)) \<ge> N"
  using assms unfolding \<C>2_eq Int_iff mem_Collect_eq list_tl list_hd \<A>_center by auto 

lemma \<C>3_memE: 
  assumes "(t#x) \<in> condition_to_set \<C>3" 
  shows "(val ((t \<ominus> c1 x) \<div> (c2 x \<ominus> c1 x)) \<ge> eint (-N) \<and>  
                                                   val ((t \<ominus> c1 x) \<div> (c2 x \<ominus> c1 x)) < N)"
  using assms unfolding \<C>3_eq Int_iff mem_Collect_eq list_tl list_hd \<A>_center by auto 

lemma \<C>1_int_\<C>2: "condition_to_set \<C>1 \<inter> condition_to_set \<C>2 = {}"
  apply(rule equalityI')
  unfolding Int_iff mem_Collect_eq \<C>1_eq \<C>2_eq  eint_ord_code(1) eint_ord_trans
  using eint_iless apply force
  by blast 

lemma \<C>1_int_\<C>3: "condition_to_set \<C>1 \<inter> condition_to_set \<C>3 = {}"
  apply(rule equalityI')
  unfolding Int_iff mem_Collect_eq \<C>1_eq \<C>3_eq 
  using eint_ord_code(1) eint_ord_trans 
  apply (meson linorder_not_less)
  by blast 

lemma \<C>2_int_\<C>3: "condition_to_set \<C>2 \<inter> condition_to_set \<C>3 = {}"
  apply(rule equalityI')
  unfolding Int_iff mem_Collect_eq \<C>2_eq \<C>3_eq 
  using  eint_ord_code(1) eint_ord_trans 
  apply (meson linorder_not_less)     
  by blast 

lemma triple_cut_disjoint:
 "disjoint (condition_to_set ` {\<C>1, \<C>2, \<C>3})"
proof(rule disjointI)
  fix A B 
  assume A: " A \<in> condition_to_set ` {\<C>1, \<C>2, \<C>3}" " B \<in> condition_to_set ` {\<C>1, \<C>2, \<C>3}" " A \<noteq> B"
show "A \<inter> B = {}"
  apply(cases "A = condition_to_set \<C>1")
   apply(cases "B = condition_to_set \<C>2")
  using \<C>1_int_\<C>2 apply blast
  apply(cases "B = condition_to_set \<C>3")
  using \<C>1_int_\<C>3 apply blast
  using A apply blast
  apply(cases "A = condition_to_set \<C>2")
  apply(cases "B = condition_to_set \<C>1")
  using \<C>1_int_\<C>2 apply blast
  apply(cases "B = condition_to_set \<C>3")
  using \<C>2_int_\<C>3 apply blast
  using A apply blast
  apply(cases "A = condition_to_set \<C>3")
  apply(cases "B = condition_to_set \<C>1")
  using \<C>1_int_\<C>3 apply blast
  apply(cases "B = condition_to_set \<C>2")
  using \<C>2_int_\<C>3 apply blast
  using A apply blast     
  using A by blast 
qed

lemma triple_cut_covers:
 "condition_to_set \<A> = (\<Union> C \<in> condition_to_set ` {\<C>1, \<C>2, \<C>3}. C)"
proof(rule equalityI')
  fix x assume A: " x \<in> condition_to_set \<A>"
  have 0: "tl x \<in> C"
    using A unfolding \<A>_eq condition_to_set.simps cell_def by blast 
  show "x \<in> (\<Union>C\<in>condition_to_set ` {\<C>1, \<C>2, \<C>3}. C)"
    apply(cases "x \<in> condition_to_set \<C>1")
    apply blast
    apply(cases "x \<in> condition_to_set \<C>2")
    apply blast
  proof- 
    assume A2: " x \<notin> condition_to_set \<C>1" "x \<notin> condition_to_set \<C>2"
    have "x \<in> condition_to_set \<C>3"
      unfolding \<C>3_eq Int_iff
      apply(rule conjI)
      using A apply blast
      unfolding mem_Collect_eq 
      apply(rule conjI)
      using A unfolding \<A>_eq condition_to_set.simps cell_def mem_Collect_eq apply blast
      apply(rule conjI)
      using A unfolding \<A>_eq condition_to_set.simps cell_def mem_Collect_eq apply blast
      apply(rule conjI)
      using A A2 
      unfolding \<A>_eq \<C>1_eq \<C>2_eq condition_to_set.simps cell_def mem_Collect_eq Int_iff
      using notin_closed apply blast
      using A A2 
      unfolding \<A>_eq \<C>1_eq \<C>2_eq condition_to_set.simps cell_def mem_Collect_eq Int_iff
      using notin_closed by blast
    thus "x \<in> (\<Union>C\<in>condition_to_set ` {\<C>1, \<C>2, \<C>3}. C) "
      by blast 
  qed
next 
  show " \<And>x. x \<in> (\<Union>C\<in>condition_to_set ` {\<C>1, \<C>2, \<C>3}. C) \<Longrightarrow> x \<in> condition_to_set \<A>"
    using \<C>1_eq \<C>2_eq \<C>3_eq by blast 
qed

lemma triple_cut_cell_decomp: 
"is_cell_decomp m {\<C>1, \<C>2, \<C>3} (condition_to_set \<A>)"
  apply(rule is_cell_decompI, blast,rule is_partitionI, rule triple_cut_disjoint)
  using triple_cut_covers apply blast 
    using \<C>1_def \<C>2_def \<C>3_def unfolding arity.simps \<A>_arity apply blast
    unfolding \<A>_eq  condition_to_set.simps cell_def apply blast
    using \<C>1_int_\<C>2 \<C>1_int_\<C>3 \<C>2_int_\<C>3 by blast 

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Preparing Our Set, One Cut at a Time\<close>
(**************************************************************************************************)
(**************************************************************************************************)
definition B11 where B11_def: "B11 = (condition_to_set \<C>1 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g)))"

definition B12 where B12_def: "B12 = (condition_to_set \<C>2 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g)))"

definition B13 where B13_def: "B13 = (condition_to_set \<C>3 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g)))"

lemma B1_eq1: "B1 = condition_to_set (\<B>1 f) \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g))"
  unfolding B1_def using f_def by auto 

lemma B1_eq2: "B1 = (condition_to_set \<C>1 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g))) \<union>
                 (condition_to_set \<C>2 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g))) \<union>
                  (condition_to_set \<C>3 \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (\<B>1 g)))"
  unfolding B1_eq1 using triple_cut_covers unfolding \<A>_def by blast 

lemma B1_un: "B1 = B11 \<union> B12 \<union> B13"
  unfolding B11_def B12_def B13_def B1_eq2 by blast 

lemma triple_cut_disjoint': "\<And> s s'. s \<in> {\<C>1, \<C>2, \<C>3} \<Longrightarrow> s' \<in> {\<C>1, \<C>2, \<C>3} \<Longrightarrow>s \<noteq> s' \<Longrightarrow> condition_to_set s \<inter> condition_to_set s' = {}"
  using is_cell_decompE(5)[of m "{\<C>1, \<C>2, \<C>3}" "condition_to_set \<A>"] triple_cut_cell_decomp
        is_partitionE(1)[of "condition_to_set ` {\<C>1, \<C>2, \<C>3}" "condition_to_set \<A>"] disjointE
  by blast

lemma Bij_disjoint: "disjoint {B11, B12, B13}"
  apply(rule triple_disjointI)
  unfolding B11_def B12_def B13_def 
  using triple_cut_disjoint disjointE Inf_set_def \<C>1_int_\<C>2 \<C>1_int_\<C>3 \<C>2_int_\<C>3 
  by auto
  
lemma Bij_intersections: "B11 \<inter> B12 = {}" "B12 \<inter> B13 = {}" "B11 \<inter> B13 = {}"
  using B11_def B12_def \<C>1_int_\<C>2 B12_def B13_def \<C>2_int_\<C>3 B11_def B13_def \<C>1_int_\<C>3 by auto

definition F1 where F1_def: "F1 = (\<lambda>g. if g = f then \<C>1 else \<B>1 g)"

definition F2 where F2_def: "F2 = (\<lambda>g. if g = f then \<C>2 else \<B>1 g)"

definition F3 where F3_def: "F3 = (\<lambda>g. if g = f then \<C>3 else \<B>1 g)"

lemma F1_f: "F1 f = \<C>1"
  using F1_def by simp

lemma F2_f: "F2 f = \<C>2"
  using F2_def by simp

lemma F3_f: "F3 f = \<C>3"
  using F3_def by simp    

lemma F1_not_f: "\<And>g. g \<noteq> f \<Longrightarrow> F1 g = \<B>1 g"
  using F1_def by simp

lemma F2_not_f: "\<And>g. g \<noteq> f \<Longrightarrow> F2 g = \<B>1 g"
  using F2_def by simp

lemma F3_not_f: "\<And>g. g \<noteq> f \<Longrightarrow> F3 g = \<B>1 g"
  using F3_def by simp

lemma F1_cell: "\<And>g. g \<in> fs \<Longrightarrow> is_cell_condition (F1 g)"
  using f_def \<C>1_cell F1_f F1_not_f 
  by (metis \<B>1_cond)
 
lemma F2_cell: "\<And>g. g \<in> fs \<Longrightarrow> is_cell_condition (F2 g)"
  using f_def \<C>2_cell F2_f F2_not_f 
   by (metis \<B>1_cond)

lemma F3_cell: "\<And>g. g \<in> fs \<Longrightarrow> is_cell_condition (F3 g)"
  using f_def \<C>3_cell F3_f F3_not_f 
   by (metis \<B>1_cond)

lemma B11_eq: "B11 = (\<Inter> g \<in> fs. condition_to_set (F1 g))"
proof- 
  have 0: "(\<Inter> g \<in> fs. condition_to_set (F1 g)) = condition_to_set (F1 f) \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (F1 g))"
    using f_def by blast 
  show ?thesis 
    unfolding 0 B11_def F1_f using F1_not_f 
    by (smt Sup.SUP_cong mem_simps(6) singleton_mem)
qed

lemma B12_eq: "B12 = (\<Inter> g \<in> fs. condition_to_set (F2 g))"
proof- 
  have 0: "(\<Inter> g \<in> fs. condition_to_set (F2 g)) = condition_to_set (F2 f) \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (F2 g))"
    using f_def by blast 
  show ?thesis 
    unfolding 0 B12_def F2_f using F2_not_f Sup.SUP_cong mem_simps(6) singleton_mem
    by auto 
qed

lemma B13_eq: "B13 = (\<Inter> g \<in> fs. condition_to_set (F3 g))"
proof- 
  have 0: "(\<Inter> g \<in> fs. condition_to_set (F3 g)) = condition_to_set (F3 f) \<inter> (\<Inter> g \<in> fs - {f}. condition_to_set (F3 g))"
    using f_def by blast 
  show ?thesis 
    unfolding 0 B13_def F3_f using F3_not_f 
    by (smt Sup.SUP_cong mem_simps(6) singleton_mem)
qed

lemma F1_sub: "\<And>g. g \<in> fs \<Longrightarrow> condition_to_set (F1 g) \<subseteq>condition_to_set (\<B>1 g)"
  using \<C>1_subset unfolding \<A>_def using F1_f F1_not_f 
  by (metis Set.basic_monos(1))

lemma F2_sub: "\<And>g. g \<in> fs \<Longrightarrow> condition_to_set (F2 g) \<subseteq>condition_to_set (\<B>1 g)"
  using \<C>2_subset unfolding \<A>_def using F2_f F2_not_f 
  by (metis Set.basic_monos(1))

lemma F3_sub: "\<And>g. g \<in> fs \<Longrightarrow> condition_to_set (F3 g) \<subseteq>condition_to_set (\<B>1 g)"
  using \<C>3_subset unfolding \<A>_def using F3_f F3_not_f 
  by (metis Set.basic_monos(1))

lemma B1_Int_B2_partition: "{B11 \<inter> B2, B12 \<inter> B2, B13 \<inter> B2} partitions (B1 \<inter> B2)"
  apply(rule is_partitionI)
   apply(rule triple_disjointI)
  unfolding B1_un
  using Bij_intersections apply blast
  using Bij_intersections apply blast
  using Bij_intersections apply blast
  by auto 

lemma centers_neq: "\<And>x t. t#x \<in> condition_to_set (\<B>1 f) \<Longrightarrow> c1 x \<noteq> c2 x"
  unfolding \<B>1_def refine_fibres_2_def refine_fibres_def condition_to_set.simps cell_def
            fibre_set.simps mem_Collect_eq list_tl Y1_def Int_iff Y0_def by blast 

lemma centers_neq': "\<And>x . x \<in> C \<Longrightarrow> c1 x \<noteq> c2 x"
  using \<A>_def \<A>_eq  unfolding \<B>1_def refine_fibres_2_def refine_fibres_def condition_to_set.simps cell_def
            fibre_set.simps mem_Collect_eq list_tl Y1_def Int_iff Y0_def 
  by simp

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Preparing the Bottom Cut\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma bottom_cut_is_preparable: "is_r_preparable m n 1 (fs \<union> gs) (B11 \<inter> B2)"
proof-
  have B11_closed: "condition_to_set \<C>1 \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding B12_def using \<C>1_closed by blast 
  have b0: "\<And>x t. t#x \<in> condition_to_set \<C>1  \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> (c2 x) = (t \<ominus> c1 x) \<otimes> u [^] n"
    apply(rule Case_ii[of ])
        apply(rule N_def )
    using B11_closed apply (metis (no_types, lifting) IntD1 Qp_pow_ConsE(2) list_hd subsetD)
      apply(rule SA_car_closed[of _ m], rule c1_closed)   
        apply (metis (no_types, lifting) B11_closed IntD1 Qp_pow_ConsE(1) list_tl subsetD)
      apply(rule SA_car_closed[of _ m], rule c2_closed)   
        apply (metis (no_types, lifting) B11_closed IntD1 Qp_pow_ConsE(1) list_tl subsetD)
    using centers_neq \<C>1_subset unfolding \<A>_def B11_def apply blast
    using \<C>1_memE apply blast by(rule locale_assms)
  obtain u0 where u0_def: "u0 = (\<lambda>xs. if xs \<in> condition_to_set \<C>1  then (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> u [^] n) else \<one>)"
    by blast 
  have u0_in: "\<And>xs. xs \<in> condition_to_set \<C>1  \<Longrightarrow> u0 xs \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and>  (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> (u0 xs) [^] n"
  proof- 
    fix xs assume A: "xs \<in> condition_to_set \<C>1 "
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A B11_closed by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have a0: "\<exists>u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> u [^] n"
      using A b0[of t x] unfolding tx_def list_tl list_hd by blast 
    have a1: "u0 xs = (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> u [^] n)"
      using u0_def A by presburger
    show "u0 xs \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and>  (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> (u0 xs) [^] n"
      using a0 a1 by (smt SomeE)
  qed
  have val_eq: "\<And>xs. xs \<in> condition_to_set \<C>1  \<Longrightarrow> val ((hd xs) \<ominus> (c2 (tl xs))) = val ((hd xs) \<ominus> (c1 (tl xs)))"
  proof- fix xs assume A: "xs \<in> condition_to_set \<C>1"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A \<C>1_closed by blast
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have 0: " (hd xs) \<ominus> (c2 (tl xs)) = ((hd xs) \<ominus> (c1 (tl xs))) \<otimes> (u0 xs) [^] n"
      using A u0_in by blast 
    have 1: " u0 xs \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0"
      using A u0_in by blast 
    have 2: "(hd xs) \<ominus> (c2 (tl xs)) \<in> carrier Q\<^sub>p"
      unfolding tx_def list_hd list_tl using t_closed c2_closed x_closed SA_car_closed by blast 
    have 3: "(hd xs) \<ominus> (c1 (tl xs)) \<in> carrier Q\<^sub>p"
      unfolding tx_def list_hd list_tl using t_closed c1_closed x_closed SA_car_closed by blast
    have 4: "val (u0 (t # x) [^] n) = 0"
      using locale_assms 1 
      by (smt Qp.nat_pow_closed Qp.nat_pow_one Qp.nonzero_pow_nonzero Qp.one_closed Qp_nonzero_nat_pow equal_val_imp_equal_ord(1) equal_val_imp_equal_ord(2) finite_val_imp_nonzero nonzero_nat_pow_ord tx_def val_one val_ord')
    show "val (lead_coeff xs \<ominus> c2 (tl xs)) = val (lead_coeff xs \<ominus> c1 (tl xs)) "
      using 2 3 1 4 unfolding 0 unfolding tx_def list_tl list_hd 
      using val_mult[of "(t \<ominus> c1 x)" "u0 (t # x) [^] n"] unfolding 4 
      by (metis Qp.nat_pow_closed add_0_right)
  qed
  have u0_notin: "\<And>xs. xs \<notin> condition_to_set \<C>1  \<Longrightarrow> u0 xs = \<one>"
    using u0_def by metis 
  have u0_closed: "u0 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    apply(rule )
    using u0_in u0_notin Qp.one_closed by metis 
  show "is_r_preparable m n 1 (fs \<union> gs) (B11 \<inter> B2)"
  proof(cases "B11 \<inter> B2 = {}")
    case True
    show ?thesis unfolding True 
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule empty_is_1_prepared)
      using fs1 gs1  apply blast
      using fs_nonempty apply blast
      using locale_assms by blast
  next
    case a_nonempty: False
    have b1: "\<And>g. g \<in> gs \<Longrightarrow> 
              \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                   condition_to_set \<D> = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g)"
    proof- 
      fix l assume A: "l \<in> gs"
      obtain C1 f1 f2 I1 where \<B>2_params: "\<B>2 l = Cond m C1 c2 f1 f2 I1"
        unfolding \<B>2_def refine_fibres_2_def refine_fibres_def 
        using  A gs_defs(3) gs_defs(5) by blast
      have 00: "B11 \<inter> B2 \<subseteq> condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l)"
      proof- 
        have " (\<Inter>f\<in>gs. condition_to_set (\<B>2 f)) \<subseteq> condition_to_set (\<B>2 l)"
          using A by blast 
        thus ?thesis unfolding   B2_def B11_def A by blast 
      qed
      have \<B>2_cell_cond: "is_cell_condition (\<B>2 l)"
        using A by (simp add: \<B>2_cond)
      obtain \<D> where \<D>_def: "\<D> = Cond m C1 c1 f1 f2 I1"
        by blast 
      have \<D>_cell_cond: "is_cell_condition \<D>"
        unfolding \<D>_def apply(rule is_cell_conditionI')
            apply(rule is_cell_conditionE[of m C1 c2 f1 f2 I1])
        using \<B>2_cell_cond unfolding \<B>2_params apply blast
           apply(rule c1_closed)
          apply(rule is_cell_conditionE[of m C1 c2 f1 f2 I1])
        using \<B>2_cell_cond unfolding \<B>2_params apply blast
         apply(rule is_cell_conditionE[of m C1 c2 f1 f2 I1])
        using \<B>2_cell_cond unfolding \<B>2_params apply blast
        apply(rule is_cell_conditionE[of m C1 c2 f1 f2 I1])
        using \<B>2_cell_cond unfolding \<B>2_params by blast
      have 01: "condition_to_set \<C>1 \<inter> condition_to_set \<D> = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l)"
        apply(rule equalityI')
         apply(rule IntI)
        apply blast
        unfolding \<B>2_params condition_to_set.simps apply(rule cell_memI)
        using B11_closed apply blast
        unfolding \<D>_def condition_to_set.simps cell_def apply blast
        using val_eq 
        apply (metis (mono_tags, lifting) Int_iff eval_hom_def mem_Collect_eq)
        using val_eq 
        by (metis (no_types, lifting) Int_iff mem_simps(7))
      have " \<exists>\<C>''. is_cell_condition \<C>'' \<and>
         arity \<C>'' = m \<and> center \<C>'' = c1 \<and> fibre_set \<C>'' = C \<inter> C1 \<and> condition_to_set \<C>'' = condition_to_set \<C>1 \<inter> condition_to_set \<D>"
        apply(rule  cell_intersection_same_center_fixed[of \<C>1 \<D> m C c1 q1 q2 J1 C1 f1 f2 I1])
        using \<C>1_cell apply blast
        using \<D>_cell_cond apply blast
        unfolding \<C>1_params apply blast
        unfolding \<D>_def 
        by blast 
      hence " \<exists>\<C>''. is_cell_condition \<C>'' \<and>
         arity \<C>'' = m \<and> center \<C>'' = c1 \<and> fibre_set \<C>'' = C \<inter> C1 \<and> condition_to_set \<C>'' = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l)"
        unfolding 01 by blast 
      then obtain \<D>' where \<D>'_def: "is_cell_condition \<D>' \<and> arity \<D>' = m \<and> center \<D>' = c1 \<and> 
              condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l) = condition_to_set \<D>'"
        using 01 by blast 
      have \<D>'_alt_def: "condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l) =condition_to_set \<C>1 \<inter> condition_to_set \<D>'"
        using \<D>'_def by blast  
      thus "\<exists>\<D>. is_cell_condition \<D> \<and>  arity \<D> = m \<and>  center \<D> = c1 \<and>
                  condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 l) \<and> condition_to_set \<D> =
                                                   condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 l)"

        using \<D>'_def \<D>_def by blast 
    qed
    obtain G where G_def: "G = (\<lambda>g \<in> gs.(SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g)) )"
      by blast 
    have GE: "\<And>g. g \<in> gs \<Longrightarrow>is_cell_condition (G g) \<and> arity (G g) = m \<and> center (G g) = c1 \<and> (condition_to_set (G g) \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set (G g) = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g)"
    proof- 
      fix g assume A: "g \<in> gs"
      have 0: " \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g)"
        using b1 A by blast 
      have 1: "G g = (SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g))"
        using A G_def unfolding restrict_apply 
        by presburger
      show "is_cell_condition (G g) \<and> arity (G g) = m \<and> center (G g) = c1 \<and> (condition_to_set (G g) \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set (G g) = condition_to_set \<C>1 \<inter> condition_to_set (\<B>2 g)"
      using A b1 1 SomeE by smt 
    qed
    have b2: "condition_to_set \<C>1 \<inter> (\<Inter>g \<in> gs. condition_to_set (\<B>2 g)) =
              condition_to_set \<C>1 \<inter> (\<Inter>g \<in> gs. condition_to_set (G g))"
      using GE by blast 
    have a_alt: "B11 \<inter> B2 = B11 \<inter> (\<Inter>g\<in>gs. condition_to_set (G g))"
      unfolding  B11_def B2_def 
      apply(rule equalityI')
      using b2 apply blast using b2 by blast
    obtain H where H_def: "H = (\<lambda> f. if f \<in> fs then F1 f else G f)"
      by blast 
    have b3: "\<And>f. f \<in> fs \<Longrightarrow> H f = F1 f"
      using H_def by metis 
    have b4: "\<And>f. f \<in> gs \<Longrightarrow> H f = G f"
      using H_def locale_assms by (smt Int_iff mem_simps(2))
    have b5: "B11 \<inter> B2 = (\<Inter>f \<in> fs. condition_to_set (H f)) \<inter> (\<Inter>g\<in>gs. condition_to_set (H g))"
      using b3 b4 unfolding a_alt 
      by (smt B11_eq Sup.SUP_cong)
    have b6: "\<And>f. f \<in> fs \<Longrightarrow> center (H f) = c1"
      unfolding b3 using F1_def center.simps \<C>1_params 
      by (simp add: \<B>1_center)
    have b7: "\<And>f. f \<in> gs \<Longrightarrow> center (H f) = c1"
      unfolding b4 using GE center.simps \<C>1_params 
      by blast
    have b8: "center ` (H ` (fs \<union> gs)) = {c1}"
      apply(rule equalityI')
      using b6 b7 apply blast
      using fs_nonempty b6 
      by (metis Un_iff ex_in_conv imageI singleton_mem)
    have b9: "card {c1} = 1"
      by auto 
    have b10: "\<And>f. f \<in> fs \<Longrightarrow> is_cell_condition (H f)"
      unfolding b3 using F1_cell by blast
    have b11: "\<And>f. f \<in> gs \<Longrightarrow> is_cell_condition (H f)"
      unfolding b4 using GE  by blast
    have b12: "\<And>f. f \<in> fs \<Longrightarrow> arity (H f) = m"
      unfolding b3 
      by (metis F1_f F1_not_f \<B>1_arity \<C>1_arity)
    have b13: "\<And>f. f \<in> gs \<Longrightarrow> arity (H f) = m"
      unfolding b4 using GE by blast
    have b14: "\<And>f. f \<in> gs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
    proof- 
      fix l assume A: "l \<in> gs"
      have c0: "condition_to_set (H l) \<subseteq> condition_to_set (\<B>2 l)"
        using A GE[of l] b11[of l] b4 by metis    
      have c1: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set (\<B>2 l)) u h k"
        apply(rule SA_poly_factors_subset[of m n l c2 "condition_to_set (\<C>\<^sub>2 l)"]) 
        using A gs_defs(6)[of l] gs_defs(3)[of l]  apply metis 
        unfolding \<B>2_def by(rule refine_fibres_2_subset)
      have c1: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set (H l)) u h k"
        apply(rule SA_poly_factors_subset[of m n l c2 "condition_to_set (\<B>2 l)"]) 
        using c1 gs_defs(6)[of l] gs_defs(3)[of l] apply blast
        by(rule c0 )
      then obtain u k h where uhk_def: "SA_poly_factors p m n l c2 (condition_to_set (H l)) u h k"
        by blast 
      obtain u1 where u1_def: "u1 = (\<lambda>xs. u xs \<otimes> (u0 xs)[^]k)"
        by blast 
      have u1_closed: "u1 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
        apply(rule )
        unfolding u1_def apply(rule Qp.ring_simprules)
        using uhk_def  SA_poly_factors_def SA_poly_factors_axioms_def Q\<^sub>p_def Z\<^sub>p_def 
        apply (meson SA_poly_factors_closure(5))                    
        apply(rule Qp.nat_pow_closed) using u0_closed by blast 
      have "SA_poly_factors p m n l c1 (condition_to_set (H l)) u1 h k"
        apply(rule SA_poly_factorsI)
        using b10 b11 b12 b13 condition_decomp'
            apply (metis A cell_condition_to_set_subset)
        apply(rule u1_closed)
          apply(rule c1_closed)
        using uhk_def SA_poly_factors_def SA_poly_factors_axioms_def apply blast 
      proof- 
        fix x t 
        assume A0: " t \<in> carrier Q\<^sub>p" "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"  "t # x \<in> condition_to_set (H l)"
        have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using A A0 b13 condition_decomp' condition_to_set_memE(1) by blast
        have b0: "H l = G l"
          using A  by (simp add: A b4)
        have A1: "condition_to_set (H l) \<subseteq> condition_to_set \<C>1" 
          unfolding b0 
          using GE[of l] A  by blast 
        have A2: "SA_poly_to_Qp_poly m x l \<bullet> t = u (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c2 x) [^] k"
          using A0 uhk_def SA_poly_factorsE[of m n l c2  "condition_to_set (H l)" u h k t x] by blast 
        have A3: "t \<ominus> (c2 x) = (t \<ominus> (c1 x)) \<otimes> (u0 (t#x)) [^] n"
          using u0_in[of "t#x"] A0 A1 unfolding list_tl list_hd by blast 
        have R: "\<And> a b c d. \<lbrakk>a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p;d \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
                      a[^]n \<otimes> b \<otimes> (c \<otimes> d[^]n)[^]k = (a \<otimes> d[^]k)[^]n \<otimes> b \<otimes> c[^]k"
        proof- 
          fix a b c d assume a: "a \<in> carrier Q\<^sub>p" "b \<in> carrier Q\<^sub>p" "c \<in> carrier Q\<^sub>p" "d \<in> carrier Q\<^sub>p"
          have 0: "(a \<otimes> d[^]k)[^]n = a[^]n \<otimes> (d[^]k)[^]n"
            using locale_assms a 
            by (meson Qp.nat_pow_closed Qp.nat_pow_distrib)
          show " a[^]n \<otimes> b \<otimes> (c \<otimes> d[^]n)[^]k = (a \<otimes> d[^]k)[^]n \<otimes> b \<otimes> c[^]k"
            unfolding 0 using a 
            by (smt Groups.mult_ac(2) Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.cring_simprules(5) Qp.nat_pow_closed Qp.nat_pow_distrib Qp_nat_pow_pow)
        qed
        have A4: "u (t # x) [^] n \<otimes> h x \<otimes> ((t \<ominus> c1 x) \<otimes> u0 (t # x) [^] n) [^] k = (u (t # x) \<otimes> u0 (t # x) [^] k) [^] n \<otimes> h x \<otimes> (t \<ominus> c1 x)[^] k "
          apply(rule R[of "u (t#x)" "h x" "t \<ominus> c1 x" "u0 (t#x)" ])
          using uhk_def SA_poly_factorsE(3) A0 apply blast
          using uhk_def SA_car_closed unfolding SA_poly_factorsE  A0 
            apply (metis Qp_pow_ConsE(1) SA_poly_factors_closure(4) list_tl tx_closed)
          using A0 c1_closed SA_car_closed apply blast
          using tx_closed u0_closed by blast 
        have A5: "val (u (t # x)) = 0"
          using A0 SA_poly_factorsE uhk_def by blast 
        have A6: "val (u0 (t # x)) = 0"
          using u0_in[of "t#x"] A0 A1 unfolding list_tl list_hd by blast 
        have a: "u (t # x) \<in> carrier Q\<^sub>p"
          using uhk_def A0 SA_poly_factorsE(3) by blast 
        have b: "u0 (t # x) \<in> carrier Q\<^sub>p"
          using u0_closed tx_closed by blast 
        have A7: "val (u0(t#x)[^]k) = 0"
          apply(induction k) 
          apply (metis Group.nat_pow_0 val_one)                     
          using A6 b tx_closed val_mult 
          by (metis Group.nat_pow_Suc Qp.nat_pow_closed arith_simps(50))
        have A8: "val (u (t # x) \<otimes> u0 (t # x) [^] k) = 0"
          using val_mult[of "u (t # x)" "u0(t#x)[^]k"] a b
          unfolding A6 A7 by (metis Qp.nat_pow_closed A5 add.comm_neutral)
        show "val (u1 (t # x)) = 0 \<and> SA_poly_to_Qp_poly m x l \<bullet> t = u1 (t # x) [^] n \<otimes> h x \<otimes> (t \<ominus> c1 x) [^] k"
          unfolding  A2 A3 A4 u1_def using A8 by blast 
      qed
      thus " \<exists>u h k. SA_poly_factors p m n l (center (H l)) (condition_to_set (H l)) u h k"
        using A b7 by auto 
    qed
    have b15: "\<And>f. f \<in> fs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
    proof-
      fix f assume A: "f \<in> fs"
      have d0: "\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k"
        using fs_defs  A by blast 
      have d1: "center (\<C>\<^sub>1 f) = c1"
        using A fs_defs(3) by blast
      have d2: "center (H f) = c1"
        using A b6 by blast
      have d3: "condition_to_set (H f) = condition_to_set (F1 f)"
        using A by (simp add: A b3)
      have d4: "condition_to_set (H f) \<subseteq> condition_to_set (\<C>\<^sub>1 f)"
        unfolding d3 using F1_sub[of f] A b3 using refine_fibres_2_subset unfolding \<B>1_def
        by blast 
      show "\<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
        apply(rule SA_poly_factors_subset[of _ _ _ _ "condition_to_set (\<C>\<^sub>1 f)"])
        using d0 unfolding d1 d2 apply blast
        by(rule d4)
    qed
    show ?thesis 
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _ H "H ` (fs \<union> gs)"]) 
      using fs1 gs1 apply blast
      using locale_assms apply blast
           apply blast
      unfolding b8 b9 apply simp  
      using b10 b11 apply blast
      using b12 b13 apply blast
      using b14 b15 apply blast
      unfolding b5 by blast 
  qed
qed

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Preparing the Top Cut\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma top_cut_is_preparable: "is_r_preparable m n 1 (fs \<union> gs) (B12 \<inter> B2)"
proof-
  have B12_closed: "condition_to_set \<C>2 \<subseteq> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding B12_def using \<C>2_closed by blast 
  have b0: "\<And>x t. t#x \<in> condition_to_set \<C>2  \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> (c2 x) = \<ominus> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
    apply(rule Case_i[of N n _])
        apply(rule N_def )
    using B12_closed apply (metis (no_types, lifting) IntD1 Qp_pow_ConsE(2) list_hd subsetD)
      apply(rule SA_car_closed[of _ m], rule c1_closed)   
        apply (metis (no_types, lifting) B12_closed IntD1 Qp_pow_ConsE(1) list_tl subsetD)
      apply(rule SA_car_closed[of _ m], rule c2_closed)   
        apply (metis (no_types, lifting) B12_closed IntD1 Qp_pow_ConsE(1) list_tl subsetD)
    using centers_neq \<C>2_subset unfolding \<A>_def B12_def apply blast
    using \<C>2_memE apply blast by(rule locale_assms)
  obtain u0 where u0_def: "u0 = (\<lambda>xs. if xs \<in> condition_to_set \<C>2  then (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n) else \<one>)"
    by blast 
  have u0_in: "\<And>xs. xs \<in> condition_to_set \<C>2  \<Longrightarrow> u0 xs \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and>  (hd xs) \<ominus> (c2 (tl xs)) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
  proof- 
    fix xs assume A: "xs \<in> condition_to_set \<C>2 "
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A B12_closed by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have a0: "\<exists>u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
      using A b0 unfolding tx_def list_tl list_hd by blast 
    have a1: "u0 xs = (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> (c2 (tl xs)) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n)"
      using u0_def A by presburger
    show "u0 xs \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and>  (hd xs) \<ominus> (c2 (tl xs)) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
      using a0 a1 by (smt SomeE)
  qed
  have u0_notin: "\<And>xs. xs \<notin> condition_to_set \<C>2  \<Longrightarrow> u0 xs = \<one>"
    using u0_def by metis 
  have u0_closed: "u0 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
    apply(rule )
    using u0_in u0_notin Qp.one_closed by metis 
  obtain g where g_def: "g = \<ominus>\<^bsub>SA m\<^esub>(c2 \<ominus>\<^bsub>SA m\<^esub>c1)"
    by blast 
  have g_closed: "g \<in> carrier (SA m)"
    unfolding g_def 
    by(rule R.ring_simprules, rule R.ring_simprules, rule c2_closed, rule c1_closed)
  have g_eval: "\<And>xs. xs \<in> condition_to_set \<C>2  \<Longrightarrow> g (tl xs) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs))"
  proof- fix xs assume A: "xs \<in> condition_to_set \<C>2 "
    have 00: "tl xs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using B12_closed Qp_pow_ConsE A by blast 
    show "g (tl xs) = \<ominus> (c2 (tl xs) \<ominus> c1 (tl xs))" 
      unfolding g_def using 00 B12_closed c1_closed c2_closed 
      using R.cring_simprules(4) SA_minus_eval SA_u_minus_eval by presburger
  qed
  have u0_factor: "\<And>xs. xs \<in> condition_to_set \<C>2  \<Longrightarrow>(hd xs) \<ominus> (c2 (tl xs)) = g (tl xs) \<otimes> (u0 xs) [^] n"
    using u0_in unfolding g_eval by blast 
  show "is_r_preparable m n 1 (fs \<union> gs) (B12 \<inter> B2)"
  proof(cases "(B12 \<inter> B2) = {}")
    case True
    show ?thesis unfolding True 
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule empty_is_1_prepared)
      using fs1 gs1  apply blast
      using fs_nonempty apply blast
      using locale_assms by blast
  next
    case a_nonempty: False
    have b1: "\<And>g. g \<in> gs \<Longrightarrow> 
              \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                   condition_to_set \<D> = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g)"
    proof- 
      fix l assume A: "l \<in> gs"
      obtain C1 f1 f2 I1 where \<B>2_params: "\<B>2 l = Cond m C1 c2 f1 f2 I1"
        unfolding \<B>2_def refine_fibres_2_def refine_fibres_def 
        using  A gs_defs(3) gs_defs(5) by blast
      have 00: "(B12 \<inter> B2) \<subseteq> condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l)"
      proof- 
        have " (\<Inter>f\<in>gs. condition_to_set (\<B>2 f)) \<subseteq> condition_to_set (\<B>2 l)"
          using A by blast 
        thus ?thesis unfolding  B2_def B12_def A by blast 
      qed
      have 01: "\<exists>\<B>. is_cell_condition \<B> \<and> arity \<B> = m \<and> center \<B> = c1 \<and> condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l) = condition_to_set \<B>"
        apply(rule change_centers_same_set_ii[of "\<B>2 l" m C1 c2 f1 f2 I1 c1 g u0 "condition_to_set \<C>2" \<C>2 C w1 w2 J2 n N])
        unfolding \<B>2_params apply blast using A unfolding \<B>2_params 
        apply (metis \<B>2_cond \<B>2_params)
        apply(rule c1_closed, rule g_closed, rule u0_closed)
        using a_nonempty A  00 unfolding B12_def  B2_def A \<B>2_params apply blast
        apply blast
        using \<C>2_params apply blast
        using \<C>2_cell apply blast
        using locale_assms apply blast
        using N_def apply blast
        using u0_in  apply (metis list_hd list_tl u0_factor)
        using centers_neq' by blast
      obtain \<D> where \<D>_def: "is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> 
              condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l) = condition_to_set \<D>"
        using 01 by blast 
      have \<D>_alt_def: "condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l) =condition_to_set \<C>2 \<inter> condition_to_set \<D>"
        using \<D>_def by blast 
      obtain \<D>' where \<D>'_def: "is_cell_condition \<D>' \<and> arity \<D>' = m \<and> center \<D>' = c1 \<and>  
                  fibre_set \<D>' = C \<inter> fibre_set \<D> \<and> 
                  condition_to_set \<D>' = condition_to_set \<C>2 \<inter> condition_to_set \<D>"
        using cell_intersection_same_center_fixed[of \<C>2 \<D> m C c1 w1 w2 J2 "fibre_set \<D>" "l_bound \<D>" "u_bound \<D>" "boundary_condition \<D>" ]
              condition_decomp' \<D>_def \<C>2_params \<C>2_cell by metis
      have "condition_to_set \<C>2 \<inter> condition_to_set \<D>' = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l)"
        using \<D>_def \<D>'_def by blast 
      thus "\<exists>\<D>. is_cell_condition \<D> \<and>  arity \<D> = m \<and>   center \<D> = c1 \<and>
           condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 l) \<and> condition_to_set \<D> =
                                                   condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 l)"
        using \<D>'_def \<D>_def by blast 
    qed
    obtain G where G_def: "G = (\<lambda>g \<in> gs.(SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g)) )"
      by blast 
    have GE: "\<And>g. g \<in> gs \<Longrightarrow>is_cell_condition (G g) \<and> arity (G g) = m \<and> center (G g) = c1 \<and> (condition_to_set (G g) \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set (G g) = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g)"
    proof- 
      fix g assume A: "g \<in> gs"
      have 0: " \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g)"
        using b1 A by blast 
      have 1: "G g = (SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set \<D> = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g))"
        using A G_def unfolding restrict_apply 
        by presburger
      show "is_cell_condition (G g) \<and> arity (G g) = m \<and> center (G g) = c1 \<and> (condition_to_set (G g) \<subseteq> condition_to_set (\<B>2 g)) \<and>
                  condition_to_set (G g) = condition_to_set \<C>2 \<inter> condition_to_set (\<B>2 g)"
      using A b1 1 SomeE by smt 
    qed
    have b2: "condition_to_set \<C>2 \<inter> (\<Inter>g \<in> gs. condition_to_set (\<B>2 g)) =
              condition_to_set \<C>2 \<inter> (\<Inter>g \<in> gs. condition_to_set (G g))"
      using GE by blast 
    have a_alt: "(B12 \<inter> B2) = B12 \<inter> (\<Inter>g\<in>gs. condition_to_set (G g))"
      unfolding  B12_def B2_def 
      apply(rule equalityI')
      using b2 apply blast using b2 by blast
    obtain H where H_def: "H = (\<lambda> f. if f \<in> fs then F2 f else G f)"
      by blast 
    have b3: "\<And>f. f \<in> fs \<Longrightarrow> H f = F2 f"
      using H_def by metis 
    have b4: "\<And>f. f \<in> gs \<Longrightarrow> H f = G f"
      using H_def locale_assms by (smt Int_iff mem_simps(2))
    have b5: "(B12 \<inter> B2) = (\<Inter>f \<in> fs. condition_to_set (H f)) \<inter> (\<Inter>g\<in>gs. condition_to_set (H g))"
      using b3 b4 unfolding a_alt 
      by (smt B12_eq Sup.SUP_cong)
    have b6: "\<And>f. f \<in> fs \<Longrightarrow> center (H f) = c1"
      unfolding b3 using F2_def center.simps \<C>2_params 
      by (simp add: \<B>1_center)
    have b7: "\<And>f. f \<in> gs \<Longrightarrow> center (H f) = c1"
      unfolding b4 using GE center.simps \<C>2_params 
      by (simp add: \<B>1_center)
    have b8: "center ` (H ` (fs \<union> gs)) = {c1}"
      apply(rule equalityI')
      using b6 b7 apply blast
      using fs_nonempty b6 
      by (metis Un_iff f_def image_eqI singletonD)
    have b9: "card {c1} = 1"
      by auto 
    have b10: "\<And>f. f \<in> fs \<Longrightarrow> is_cell_condition (H f)"
      unfolding b3 using F2_cell by blast
    have b11: "\<And>f. f \<in> gs \<Longrightarrow> is_cell_condition (H f)"
      unfolding b4 using GE  by blast
    have b12: "\<And>f. f \<in> fs \<Longrightarrow> arity (H f) = m"
      unfolding b3 
      by (simp add: F2_def \<B>1_arity \<C>2_arity)
    have b13: "\<And>f. f \<in> gs \<Longrightarrow> arity (H f) = m"
      unfolding b4 using GE by blast
    have b14: "\<And>f. f \<in> gs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
    proof- 
      fix l assume A: "l \<in> gs"
      have c0: "condition_to_set (H l) \<subseteq> condition_to_set (\<B>2 l)"
        using A GE[of l] b11[of l] b4 by metis    
      have c1: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set (\<B>2 l)) u h k"
        apply(rule SA_poly_factors_subset[of m n l c2 "condition_to_set (\<C>\<^sub>2 l)"]) 
        using A gs_defs(6)[of l] gs_defs(3)[of l] apply metis
        unfolding \<B>2_def by(rule refine_fibres_2_subset)
      have c1: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set (H l)) u h k"
        apply(rule SA_poly_factors_subset[of m n l c2 "condition_to_set (\<B>2 l)"]) 
        using c1 gs_defs(6)[of l] gs_defs(3)[of l] apply blast
        by(rule c0 )
      have c2: "\<exists>u h k. SA_poly_factors p m n l c1 (condition_to_set (H l)) u h k"
        apply(rule SA_poly_factors_change_of_center[of _ _ _ c2 _ _ g u0 0])
            apply(rule c1, rule c1_closed, rule g_closed, rule u0_closed)
      proof- 
        fix x t 
        assume A0: " t \<in> carrier Q\<^sub>p" " t # x \<in> condition_to_set (H l)"  "t # x \<in> condition_to_set (H l)"
        have tx_closed: "t#x \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
          using A A0 b13 condition_decomp' condition_to_set_memE(1) by blast
        have b0: "H l = G l"
          using A  by (simp add: A b4)
        have A1: "condition_to_set (H l) \<subseteq> condition_to_set \<C>2" 
          unfolding b0 
          using GE[of l] A  by blast 
        have A2: " g x = \<ominus> (c2 x \<ominus> c1 x)"
          using g_eval[of "t#x"] A0 A1 unfolding list_tl list_hd by blast 
        have A3:  "val (u0 (t # x)) = 0 \<and> t \<ominus> c2 x = g x \<otimes> u0 (t # x) [^] n"
          unfolding A2 
          using A0 u0_in[of "t#x"] g_eval[of "t#x"] A1
          unfolding list_tl list_hd by blast 
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using tx_closed 
          by (metis Qp_pow_ConsE(1) list_tl)
        have A4: "g x \<in> carrier Q\<^sub>p"
          using g_closed  x_closed SA_car_closed by blast 
        have A5: "u0 (t # x) [^] n \<in> carrier Q\<^sub>p"
          apply(rule Qp.nat_pow_closed)
          using u0_closed tx_closed  by blast 
        have A6: "(t \<ominus> c1 x) [^] (0::nat) = \<one>"
          using Qp.nat_pow_0 by blast
        have A7: "(t \<ominus> c1 x) [^] (0::nat) \<otimes> g x \<otimes> u0 (t # x) [^] n = g x \<otimes> u0 (t # x) [^] n"
          unfolding A6 using A4 A5 Qp.ring_simprules by metis 
        show "val (u0 (t # x)) = 0 \<and> t \<ominus> c2 x = (t \<ominus> c1 x) [^] (0::nat) \<otimes> g x \<otimes> u0 (t # x) [^] n"
          using A3 x_closed A4 A5 unfolding A7  by blast 
      qed
      show " \<exists>u h k. SA_poly_factors p m n l (center (H l)) (condition_to_set (H l)) u h k"
        using c2 b7[of l] A by auto  
    qed
    have b15: "\<And>f. f \<in> fs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
    proof-
      fix f assume A: "f \<in> fs"
      have d0: "\<exists>u h k. SA_poly_factors p m n f (center (\<C>\<^sub>1 f)) (condition_to_set (\<C>\<^sub>1 f)) u h k"
        using fs_defs  A by blast 
      have d1: "center (\<C>\<^sub>1 f) = c1"
        using A fs_defs(3) by blast
      have d2: "center (H f) = c1"
        using A b6 by blast
      have d3: "condition_to_set (H f) = condition_to_set (F2 f)"
        using A by (simp add: A b3)
      have d4: "condition_to_set (H f) \<subseteq> condition_to_set (\<C>\<^sub>1 f)"
        unfolding d3 using F2_sub[of f] A b3 using refine_fibres_2_subset unfolding \<B>1_def
        by blast 
      show "\<exists>u h k. SA_poly_factors p m n f (center (H f)) (condition_to_set (H f)) u h k"
        apply(rule SA_poly_factors_subset[of _ _ _ _ "condition_to_set (\<C>\<^sub>1 f)"])
        using d0 unfolding d1 d2 apply blast
        by(rule d4)
    qed
      show ?thesis 
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _ H "H ` (fs \<union> gs)"]) 
      using fs1 gs1 apply blast
      using locale_assms apply blast
           apply blast
      unfolding b8 b9 apply simp  
      using b10 b11 apply blast
      using b12 b13 apply blast
      using b14 b15 apply blast
      unfolding b5 by blast 
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Preparing the Middle Cut\<close>
(**************************************************************************************************)
(**************************************************************************************************)


  lemma B13_c1_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> c1 (tl xs) \<in> carrier Q\<^sub>p"
     apply(rule SA_car_closed[of _ m])
     apply(rule c1_closed)
    apply(rule Qp_pow_ConsE )
    using \<C>3_closed  unfolding B13_def 
    by blast
  lemma B13_c2_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> c2 (tl xs) \<in> carrier Q\<^sub>p"
     apply(rule SA_car_closed[of _ m])
     apply(rule c2_closed)
    apply(rule Qp_pow_ConsE )
    using \<C>3_closed  unfolding B13_def 
    by blast
  definition numer_2 where numer_2_def: "numer_2 = (\<lambda> xs. (hd xs) \<ominus> c2 (tl xs))"

  lemma numer_2_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> numer_2 xs \<in> carrier Q\<^sub>p"
    unfolding numer_2_def apply(rule Qp.ring_simprules)
    unfolding B13_def using \<C>3_closed 
    using cell_hd_closed apply blast
    apply(rule SA_car_closed[of _ m])
     apply(rule c2_closed)
    apply(rule Qp_pow_ConsE )
    using \<C>3_closed c2_closed SA_car_closed Qp_pow_ConsE  by blast

  definition denom where denom_def: "denom = (\<lambda>xs. (c2 (tl xs) \<ominus> c1 (tl xs)))"

  lemma denom_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> denom xs \<in> carrier Q\<^sub>p"
    unfolding denom_def apply(rule Qp.ring_simprules)
    unfolding B13_def 
     apply(rule SA_car_closed[of _ m])
     apply(rule c2_closed)
    apply(rule Qp_pow_ConsE )
    using \<C>3_closed c2_closed SA_car_closed Qp_pow_ConsE apply blast
     apply(rule SA_car_closed[of _ m])
     apply(rule c1_closed)
    apply(rule Qp_pow_ConsE )
    using \<C>3_closed c2_closed SA_car_closed Qp_pow_ConsE by blast

  lemma denom_nonzero: "\<And>xs. xs \<in> B13 \<Longrightarrow> denom xs \<in> nonzero Q\<^sub>p" 
    apply(rule nonzero_memI, rule denom_closed, blast)
   unfolding denom_def    unfolding B13_def   unfolding \<A>_def                 
  proof- fix xs assume A: "xs \<in> condition_to_set \<C>3 \<inter> (\<Inter>g\<in>fs - {f}. condition_to_set (\<B>1 g))"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      using A unfolding \<C>3_params condition_to_set.simps cell_def by blast 
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have 0: " c1 x \<noteq> c2 x"
      using A centers_neq[of t x]  B13_c1_closed[of "t#x"]  B13_c2_closed[of "t#x"]   \<C>3_subset
      unfolding tx_def list_tl list_hd \<A>_def  by blast 
    have 1: " c1 x \<in> carrier Q\<^sub>p"
      using A centers_neq[of t x]  B13_c1_closed[of "t#x"]  B13_c2_closed[of "t#x"]   \<C>3_subset
      unfolding tx_def list_tl list_hd \<A>_def B13_def  by blast 
    show "c2 (tl xs) \<ominus> c1 (tl xs) \<noteq> \<zero>"
      using A centers_neq[of t x]  B13_c1_closed[of "t#x"]  B13_c2_closed[of "t#x"]   \<C>3_subset
      unfolding tx_def list_tl list_hd \<A>_def B13_def 
      using "0" Qp.r_right_minus_eq by presburger
  qed

  lemma m0: "\<And> xs. xs \<in> B13 \<Longrightarrow> (\<pp> [^] N \<div> (c2 (tl xs) \<ominus> c1 (tl xs))) \<otimes> (hd xs \<ominus> c1 (tl xs)) 
        = (\<pp> [^] N \<div> (c2 (tl xs) \<ominus> c1 (tl xs))) \<otimes> (hd xs \<ominus> c2 (tl xs)) \<oplus> \<pp>[^]N  "
    apply(rule equation_6)
    unfolding B13_def using \<C>3_closed Qp_pow_ConsE 
    apply (meson cell_hd_closed mem_simps(4))
    using B13_c1_closed unfolding B13_def apply blast
    using B13_c2_closed unfolding B13_def apply blast
    using centers_neq \<C>3_subset list_tl list_hd unfolding B13_def 
  proof-
    fix xs :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list"
    assume a1: "xs \<in> condition_to_set \<C>3 \<inter> (\<Inter>g\<in>fs - {f}. condition_to_set (\<B>1 g))"
    have "condition_to_set \<C>3 \<subseteq> condition_to_set (\<B>1 f)"
      using F3_f F3_sub f_def by metis
    then have "xs \<in> condition_to_set (\<B>1 f)"
      using a1 by blast
    then show "c2 (tl xs) \<noteq> c1 (tl xs)"
      by (metis (no_types) cell_conditon_mem_decomp centers_neq)
  qed

  lemma B13_hd: "\<And> xs. xs \<in> B13 \<Longrightarrow> hd xs \<in> carrier Q\<^sub>p"
    unfolding B13_def using \<C>3_closed Qp_pow_ConsE 
    by (meson cell_hd_closed mem_simps(4))

  definition D where D_D0ef: "D = (\<lambda> xs. (\<pp> [^] N \<div> (c2 (tl xs) \<ominus> c1 (tl xs))) \<otimes> (hd xs \<ominus> c1 (tl xs)))"

  definition E where E_def: "E = (\<lambda> xs. (\<pp> [^] N \<div> (c2 (tl xs) \<ominus> c1 (tl xs))) \<otimes> (hd xs \<ominus> c2 (tl xs)))"

  lemma D_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> D xs \<in> carrier Q\<^sub>p"
    using denom_nonzero B13_c1_closed B13_c2_closed B13_hd 
    unfolding D_D0ef denom_def 
    using Qp.cring_simprules(4) Qp.cring_simprules(5) fract_closed p_natpow_closed(1) by presburger

  lemma E_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> E xs \<in> carrier Q\<^sub>p"
    using denom_nonzero B13_c1_closed B13_c2_closed B13_hd 
    unfolding E_def denom_def 
    by (meson Qp.cring_simprules(4) Qp.cring_simprules(5) fract_closed p_natpow_closed(1))

  lemma D_alt: "\<And>xs. xs \<in> B13 \<Longrightarrow> D xs =  (\<pp> [^] N \<otimes> ((hd xs \<ominus> c1 (tl xs)) \<div>(c2 (tl xs) \<ominus> c1 (tl xs))))"
    using B13_c1_closed B13_c2_closed B13_hd  numer_2_closed denom_closed denom_nonzero unfolding D_D0ef 
    using Qp.cring_simprules(14) Qp.cring_simprules(24) Qp.minus_closed Qp.nonzero_memE(1) denom_def fract_closed nonzero_inverse_Qp p_natpow_closed(1) 
    by smt 

  definition numer_1 where numer_1_def: "numer_1 = (\<lambda> xs. (hd xs) \<ominus> c1 (tl xs))"

  lemma numer_1_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> numer_1 xs \<in> carrier Q\<^sub>p"
    unfolding numer_1_def using B13_c1_closed B13_hd Qp.ring_simprules by blast 

  lemma E_alt: "\<And>xs. xs \<in> B13 \<Longrightarrow> E xs =  (\<pp> [^] N \<otimes> ((hd xs \<ominus> c2 (tl xs)) \<div>(c2 (tl xs) \<ominus> c1 (tl xs))))"
    using B13_c1_closed B13_c2_closed B13_hd  numer_1_closed denom_closed denom_nonzero unfolding E_def 
    using Qp.cring_simprules(14) Qp.cring_simprules(24) Qp.minus_closed Qp.nonzero_memE(1) denom_def fract_closed nonzero_inverse_Qp p_natpow_closed(1) 
    by smt

  lemma DB_eq: "\<And>xs. xs \<in> B13 \<Longrightarrow> D xs = E xs \<oplus> \<pp>[^]N"
    using m0 unfolding D_D0ef E_def by blast 

  lemma m1: "\<And>xs. xs \<in> B13 \<Longrightarrow> eint (- int N) \<le> val ((hd xs) \<ominus> c1 (tl xs) \<div> c2 (tl xs) \<ominus> c1 (tl xs)) \<and> val ((hd xs) \<ominus> c1 (tl xs) \<div> c2 (tl xs) \<ominus> c1 (tl xs)) < eint (int N)"
    using \<C>3_memE unfolding B13_def 
    by (metis cell_conditon_mem_decomp mem_simps(4))

  lemma p_pow: "val (\<pp>[^]N) = eint N"
    by (metis int_pow_int val_p_int_pow)

  definition D0 where D0_def: "D0 = (\<lambda> xs. (hd xs) \<ominus> c1 (tl xs) \<div> c2 (tl xs) \<ominus> c1 (tl xs))"

  lemma D0_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> D0 xs \<in> carrier Q\<^sub>p"
    unfolding D0_def using numer_1_closed denom_closed 
    unfolding numer_1_def denom_def 
    using denom_def denom_nonzero fract_closed  by auto

  definition B0 where B0_def: "B0 = (\<lambda> xs. (hd xs) \<ominus> c2 (tl xs) \<div> c2 (tl xs) \<ominus> c1 (tl xs))"

  lemma B0_closed: "\<And>xs. xs \<in> B13 \<Longrightarrow> B0 xs \<in> carrier Q\<^sub>p"
    unfolding B0_def using numer_2_closed denom_closed 
    unfolding numer_2_def denom_def 
    using denom_def denom_nonzero fract_closed 
    by force

  lemma D_D0: "\<And>xs. xs \<in> B13 \<Longrightarrow> D xs = \<pp>[^]N \<otimes> D0 xs"
    unfolding D_alt D0_def by blast 

  lemma B_B0: "\<And>xs. xs \<in> B13 \<Longrightarrow> E xs = \<pp>[^]N \<otimes> B0 xs"
    unfolding E_alt B0_def by blast 

  lemma d_val_1: "\<And> xs. xs \<in> B13 \<Longrightarrow> val (D0 xs) \<ge> eint (- int N)"
    using m1 unfolding D0_def by blast 

  lemma d_val_2: "\<And> xs. xs \<in> B13 \<Longrightarrow> val (D0 xs) < N"
    using m1 unfolding D0_def by blast 

  lemma D_val_d: "\<And>xs. xs \<in> B13 \<Longrightarrow> val (D xs) = N + val (D0 xs)"
    unfolding D_D0 using val_mult D0_closed p_pow 
    using p_natpow_closed(1) by presburger      

  lemma B_val_b: "\<And>xs. xs \<in> B13 \<Longrightarrow> val (E xs) = N + val (B0 xs)"
    unfolding B_B0 using val_mult  B0_closed p_pow 
    using p_natpow_closed(1) by presburger

  lemma m2: "\<And>xs. xs \<in> B13 \<Longrightarrow> val (D xs) \<ge> 0"
    unfolding D_val_d using d_val_1 
  proof -
    fix xs :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set list"
    assume a1: "xs \<in> B13"
    have "\<forall>i e ia. eint (ia + i) \<le> e + eint i \<or> \<not> eint ia \<le> e"
      by (metis (no_types) add_right_mono plus_eint_simps(1))
    then show "0 \<le> eint (int N) + val (D0 xs)"
      using a1 by (metis (no_types) d_val_1 add.commute add.left_neutral add.right_inverse add_cancel_eint_geq)
  qed

  lemma D_val_ring: "\<And> xs. xs \<in> B13 \<Longrightarrow>  D xs \<in> \<O>\<^sub>p"
    by(rule val_ring_memI, rule D_closed, blast, rule m2, blast)

  lemma DB_eq': "\<And>xs. xs \<in> B13 \<Longrightarrow>  E xs = D xs \<ominus> \<pp>[^]N"
    unfolding DB_eq a_minus_def using E_closed 
    by (metis Qp.add.inv_solve_right' Qp.add.m_closed p_natpow_closed(1))

  lemma d_times: "\<And>xs. xs \<in> B13 \<Longrightarrow> denom xs \<otimes> D0 xs = numer_1 xs"
    using D0_closed denom_closed numer_1_closed 
    unfolding denom_def D0_def numer_1_def 
    using denom_def denom_nonzero local.fract_cancel_right by force

  lemma b_times: "\<And>xs. xs \<in> B13 \<Longrightarrow> denom xs \<otimes> B0 xs = numer_2 xs"
    using denom_closed numer_2_closed 
    unfolding denom_def D0_def numer_2_def 
    by (metis Qp.cring_simprules(14) B0_closed B0_def denom_def denom_nonzero local.fract_cancel_left)

  definition T where T_def: "T = (\<lambda> a::int. c2 \<oplus>\<^bsub>SA m\<^esub> (c2 \<ominus>\<^bsub>SA m\<^esub> c1)\<otimes>\<^bsub>SA m\<^esub>\<cc>\<^bsub>m\<^esub>(\<pp>[^](-N) \<otimes>[a]\<cdot>\<one>))"

  lemma T_closed: "\<And> a. T a \<in> carrier (SA m)"
    unfolding T_def apply(rule R.ring_simprules)
     apply(rule c2_closed)
    apply(rule R.ring_simprules)
    using c1_closed c2_closed apply blast
    using Qp.int_inc_closed constant_fun_closed 
    using Qp.m_closed p_intpow_closed(1) by presburger
  lemma T_eval: "\<And>a x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> T a x = c2 x \<oplus> (c2 x \<ominus> c1 x)\<otimes>(\<pp>[^](-N)\<otimes>[a]\<cdot>\<one>)"
    unfolding T_def using c2_closed c1_closed SA_plus SA_mult 
    using Qp.int_inc_closed Qp_constE SA_minus_eval SA_add Qp.m_closed p_intpow_closed(1) by presburger               
 
  definition g where g: "g = (SOME g. g \<in> gs)"

  lemma g_def: "g \<in> gs"
    unfolding g using gs_nonempty  
    by (simp add: some_in_eq)
  
  lemma m3: "is_cell_condition (\<B>2 g)"
    using g_def \<B>2_cond  by blast
  
  definition f1 where f1_def: "f1 = l_bound (\<B>2 g)"
  definition f2 where f2_def: "f2 = u_bound (\<B>2 g)"
  definition I1 where I1_def: "I1 = boundary_condition (\<B>2 g)"
  definition b2 where b2_def: "b2 = fibre_set (\<B>2 g)"

  lemma \<B>2_g_params: "\<B>2 g = Cond m b2 c2 f1 f2 I1"
    using g_def unfolding f1_def f2_def I1_def b2_def 
    by (metis \<B>2_arity \<B>2_center condition_decomp')

  lemma B2_sub: "b2 \<subseteq> Y1"
    using \<B>2_g_params unfolding \<B>2_def refine_fibres_2_def  refine_fibres_def by blast
  definition lb where lb_def: "lb = \<pp>[^](N) \<odot>\<^bsub>SA m\<^esub> (c2 \<ominus>\<^bsub>SA m\<^esub> c1)"


  lemma lb_closed: "lb \<in> carrier (SA m)"
    unfolding lb_def using c2_closed c1_closed 
    by (meson SA_minus_closed SA_smult_closed p_natpow_closed(1))

  lemma lb_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> lb x = \<pp>[^](N) \<otimes> (c2 x \<ominus> c1 x)"
    unfolding lb_def 
    using SA_minus_eval SA_smult_formula c1_closed c2_closed p_natpow_closed(1) padic_fields.SA_minus_closed padic_fields_axioms by presburger
  
  definition S where S_def: "S = (\<lambda> a. Cond m b2 (T a) lb (\<zero>\<^bsub>SA m\<^esub>)  closed_interval)  "

  lemma S_cell_cond: "\<And> a. is_cell_condition (S a)"
    unfolding S_def apply(rule is_cell_conditionI')
    using m3 unfolding \<B>2_g_params using is_cell_conditionE''(1) apply blast
       apply(rule T_closed, rule lb_closed)
    apply blast
    by (simp add: is_convex_condition_def)

  lemma T_0: "T 0 = c2"
  proof- 
    have a: "([(0::int)] \<cdot> \<one>) = \<zero>"
      using Qp.int_inc_zero by blast
    have 0: " constant_function (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<zero> = \<zero>\<^bsub>SA m\<^esub>"
      unfolding a using SA_zero function_zero_as_constant by presburger                  
    have 1: "(c2 \<ominus>\<^bsub>SA m\<^esub> c1) \<otimes>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> = \<zero>\<^bsub>SA m\<^esub>"
      by(intro R.cring_simprules c1_closed c2_closed)      
    have 2: "(\<pp> [^] - int N) \<otimes> [(0::int)] \<cdot> \<one> = \<zero>"
      unfolding a 
      using Qp.r_null p_intpow_closed(1) by blast
    show ?thesis 
     unfolding T_def 2 0 1  
     using R.r_zero c2_closed by blast
  qed

  definition \<D>0 where \<D>0: "\<D>0 = (SOME \<D>0. is_cell_condition \<D>0 \<and> arity \<D>0 = m \<and> center \<D>0 = c2 \<and> fibre_set \<D>0 = b2  \<and> condition_to_set \<D>0 = condition_to_set (S 0) \<inter> condition_to_set (\<B>2 g))"

  lemma \<D>0_def: "is_cell_condition \<D>0 \<and> arity \<D>0 = m \<and> center \<D>0 = c2 \<and> fibre_set \<D>0 = b2  \<and> condition_to_set \<D>0 = condition_to_set (S 0) \<inter> condition_to_set (\<B>2 g)"
  apply(rule some_fact[of \<D>0], rule \<D>0)
    using \<D>0 cell_intersection_same_center_fixed[of "S 0" "\<B>2 g" m b2 c2 lb "\<zero>\<^bsub>SA m\<^esub>""closed_interval"
                                            b2 f1 f2 I1] S_cell_cond[of 0] m3  unfolding S_def T_0 \<B>2_g_params
      using IntE IntI equalityI subsetI by auto

  definition G where G_def: "G = (\<lambda>f. if f = g then \<D>0 else \<B>2 f)"

  lemma G_g: "G g = \<D>0"
    using G_def by metis 

  lemma G_not_g: "\<And>f. f \<noteq> g \<Longrightarrow> G f = \<B>2 f"
    using G_def by metis 

  lemma G_cell: "\<And>f. f \<in> gs \<Longrightarrow> is_cell_condition (G f)"
    using G_g G_not_g g_def \<D>0_def by (metis \<B>2_cond)

  lemma G_arity: "\<And>f. f \<in> gs \<Longrightarrow> arity (G f) = m"
    using G_g G_not_g g_def \<D>0_def  by (metis \<B>2_arity)

  lemma G_center: "\<And>f. f \<in> gs \<Longrightarrow> center (G f) = c2"
    using G_g G_not_g g_def \<D>0_def 
    by (metis \<B>2_center)
  definition B21 where B21_def: "B21 = (\<Inter> g \<in> gs. condition_to_set (G g))"
   

  lemma m4: "\<And> l. l \<in> fs \<Longrightarrow> \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> fibre_set \<D> \<subseteq> C \<and> 
                          condition_to_set \<D> = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
  proof- 
    fix l assume A: "l \<in> fs"
    obtain Bl al bl Il where F3_params: "F3 l = Cond m Bl c1 al bl Il"
      using A 
      by (metis F3_def \<B>1_arity \<B>1_center \<C>3_params condition_decomp')

    obtain \<D> where \<D>_def: "is_cell_condition \<D> \<and>
   arity \<D> = m \<and> center \<D> = c1 \<and> fibre_set \<D> = C \<inter> Bl \<and> condition_to_set \<D> = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
      using cell_intersection_same_center_fixed[of "\<C>3" "F3 l" m C c1 e1 e2 J3 Bl al bl Il]
      using \<C>3_params F3_params A 
      by (meson F3_cell \<C>3_cell)

    thus "\<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> fibre_set \<D> \<subseteq> C \<and>
                          condition_to_set \<D> = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
      by blast 
  qed

  definition K0 where K0_def: "K0 = (\<lambda> l. (SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c1 \<and> fibre_set \<D> \<subseteq> C \<and> 
                          condition_to_set \<D> = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)))"
    

  lemma m5: "\<And>l. l \<in> fs \<Longrightarrow>  is_cell_condition (K0 l) \<and> arity (K0 l) = m \<and> center (K0 l) = c1 \<and> fibre_set (K0 l) \<subseteq> C \<and> 
                          condition_to_set (K0 l) = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
  proof- fix l assume A: "l \<in> fs"
    show "is_cell_condition (K0 l) \<and> arity (K0 l) = m \<and> center (K0 l) = c1 \<and> fibre_set (K0 l) \<subseteq> C \<and> 
                          condition_to_set (K0 l) = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
      apply(rule some_fact[of "K0 l"])
      unfolding K0_def apply blast 
      by(rule m4, rule A)
  qed

  definition K where K_def: "K = (\<lambda>l. if l = f then \<C>3 else K0 l)"

  lemma K_f: "K f = \<C>3"
    using K_def by metis 

  lemma K_not_f: "\<And>l. l \<in> fs \<Longrightarrow> l \<noteq> f \<Longrightarrow>  is_cell_condition (K l) \<and> arity (K l) = m \<and> center (K l) = c1 \<and> fibre_set (K l) \<subseteq> C \<and> 
                          condition_to_set (K l) = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
    using K_def m5 by smt 

  lemma K_cell: "\<And>l. l \<in> fs \<Longrightarrow> is_cell_condition (K l)"
    using K_f K_not_f \<C>3_cell by metis  
  lemma K_arity: "\<And>l. l \<in> fs \<Longrightarrow> arity (K l) = m"
    using K_f K_not_f \<C>3_arity by metis
  lemma K_center: "\<And>l. l \<in> fs \<Longrightarrow> center (K l) = c1"
    using K_f K_not_f \<C>3_center by metis
  lemma K_fibres: "\<And>l. l \<in> fs \<Longrightarrow> fibre_set (K l) \<subseteq> C"
    using K_f K_not_f \<C>3_params fibre_set.simps 
    by (metis subsetI)
  lemma K_set: "\<And>l. l \<in> fs \<Longrightarrow> condition_to_set (K l) = condition_to_set \<C>3 \<inter> condition_to_set (F3 l)"
    using K_f K_not_f F3_f 
    by (metis Int_absorb)
  lemma helper: "B13 = condition_to_set \<C>3 \<inter> (\<Inter> l \<in> fs. condition_to_set (F3 l))"
    using B13_def B13_eq by blast 
  lemma K_inter: "B13 = (\<Inter> l \<in> fs. condition_to_set (K l))"
    apply(rule equalityI)
    unfolding helper using K_set apply blast
    using K_set fs_nonempty by blast
  lemma centers_neq'': "\<And>x t. t#x \<in> condition_to_set (\<B>2 g) \<Longrightarrow> c1 x \<noteq> c2 x"
    unfolding \<B>2_def refine_fibres_2_def refine_fibres_def condition_to_set.simps cell_def
        fibre_set.simps mem_Collect_eq list_tl Y1_def Int_iff Y0_def by blast 
  lemma centers_neq''': "\<And>x . x \<in> b2 \<Longrightarrow> c1 x \<noteq> c2 x"
    using \<B>2_g_params  unfolding \<B>2_def refine_fibres_2_def refine_fibres_def condition_to_set.simps cell_def
        fibre_set.simps mem_Collect_eq list_tl Y1_def Int_iff Y0_def by blast 
 
  lemma S0_factor: "\<And> xs l.  xs \<in> condition_to_set (S 0) \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
  proof-
    fix xs  assume a0:  "xs \<in> condition_to_set (S 0)"
    have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
      apply(intro cell_condition_set_memE(1)[of "S 0" m b2 "T 0" lb "\<zero>\<^bsub>SA m\<^esub>" closed_interval]
                  S_cell_cond )
      using a0 S_def apply metis by(rule a0)
    obtain t x where tx_def: "xs = t#x"
      using xs_closed Qp_pow_Suc_decomp by blast  
    have t_closed: "t \<in> carrier Q\<^sub>p"
      using xs_closed unfolding tx_def  
      by (metis Qp_pow_ConsE list_hd)
    have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
      using xs_closed unfolding tx_def 
      by (metis Qp_pow_ConsE(1) list_tl)
    have p0: "lb x = \<pp>[^](N) \<otimes> (c2 x \<ominus> c1 x)"
      by(rule lb_eval, rule x_closed)
    have p1: "val (t \<ominus> c2 x) \<ge> val (\<pp>[^](N) \<otimes> (c2 x \<ominus> c1 x))"
      using a0 unfolding S_def T_0 condition_to_set.simps cell_def 
                        mem_Collect_eq list_tl list_hd tx_def closed_interval_def p0 by blast 
    have p2: "(c2 x \<noteq> c1 x)"
      using a0 centers_neq''' 
      unfolding S_def condition_to_set.simps cell_def tx_def mem_Collect_eq list_tl by blast 
    have p3: "(c2 x \<ominus> c1 x) \<in> nonzero Q\<^sub>p"
      using p2 c2_closed c1_closed x_closed SA_car_closed 
      unfolding nonzero_def 
      by (smt Qp.cring_simprules(4) Qp.r_right_minus_eq mem_Collect_eq)
    have p4: "(t \<ominus> c2 x) \<in> carrier Q\<^sub>p"
      using t_closed x_closed c2_closed SA_car_closed by blast 
    have p5: "val ((t \<ominus> c2 x) \<div> (c2 x \<ominus> c1 x)) \<ge> val (\<pp>[^](N))"
      using p1 p3 p4 
      by (metis Qp.cring_simprules(14) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right p_natpow_closed(1) val_ineq_cancel_leq)
    have p6: "(t \<ominus> c1 x) \<in> carrier Q\<^sub>p"
      using t_closed x_closed c1_closed SA_car_closed by blast 
    have p7: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
      using equation_6[of t "c1 x" "c2 x" N] p3 p6 p2 t_closed c2_closed c1_closed SA_car_closed 
      by (meson x_closed)
    have alt_2: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = \<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
      using p6 p3 
      by (metis Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1))
    have alt_1: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) = \<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)"
      using p4 p3 
      by (metis Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1))
    have fr_1_closed: "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
      using fract_closed p3 p6 by blast
    have fr_2_closed: "(t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
      using fract_closed p3 p4 by blast
    have R0: "\<And>a b. a \<in> carrier Q\<^sub>p \<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> 
              val a \<le> val b \<longleftrightarrow> val (\<pp>[^]N \<otimes> a) \<le> val (\<pp>[^]N \<otimes> b) "
    proof- fix a b assume A: "a \<in> carrier Q\<^sub>p" " b \<in> carrier Q\<^sub>p "
      show " val a \<le> val b \<longleftrightarrow> val (\<pp>[^]N \<otimes> a) \<le> val (\<pp>[^]N \<otimes> b) "
        using A val_mult[of "\<pp>[^]N" a] val_mult[of "\<pp>[^]N" b] unfolding p_pow 
          by (metis add.commute add_cancel_eint_geq add_right_mono p_natpow_closed(1))
    qed
    have p8: "val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) \<ge> val (\<pp>[^]N \<otimes>\<pp>[^](N))"
      using p5 fr_2_closed val_mult using R0 
      by (meson Qp.m_closed p_natpow_closed(1))                  
    have p9: "val (\<pp>[^]N \<otimes>\<pp>[^](N)) = eint N + eint (N)"
      using val_mult 
      by (smt Qp.add_pow_ldistr_int Qp.cring_simprules(12) Qp.int_inc_closed Qp.nat_pow_one 
          Qp.nonzero_pow_nonzero Qp.not_nonzero_memI Qp.one_closed eint.inject more_arith_simps(11) 
          nonzero_nat_pow_ord of_nat_mult p_natpow_closed(1) p_pow p_times_square_not_square' val_nonzero' val_ord')                 
    have p9: "val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) \<ge> eint N + eint (N)"
      using p8 unfolding p9 by blast 

    have p11: "val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<ge>eint (N)"
      using p8 R0 
      by (metis add_cancel_eint_geq fr_2_closed p9 p_natpow_closed(1) p_pow val_mult)
    have p12: "val (\<pp> [^] N \<otimes>(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)) \<ge> min (val (\<pp>[^]N)) (val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x))) "
    proof- 
      have p120: "(\<pp> [^] N \<otimes>(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)) \<in> carrier Q\<^sub>p"
        using fr_1_closed  p_natpow_closed(1) by blast
      have p121: "(\<pp> [^] N \<otimes>(t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) \<in> carrier Q\<^sub>p"
        using fr_2_closed  p_natpow_closed(1) by blast
      show ?thesis using p120 p121 p7 unfolding alt_2 alt_1
        using Qp.a_ac(2) p_natpow_closed(1) val_ultrametric by presburger
    qed
    have a: "eint N \<le> eint (2*N)"
      using N_def 
      by (metis eint_ord_simps(1) le_refl more_arith_simps(5) mult_le_mono of_nat_mono one_le_numeral val_p_int_pow)
    have p13: "val (\<pp> [^] N \<otimes>(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)) \<ge> N"
    proof- 
      have "eint (int N) + eint (int (N)) \<ge> eint N"
        using eint_ord_simps(1) plus_eint_simps(1) by presburger
      hence 0: " (val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x))) \<ge> eint N"
        using p9 eint_ord_trans by blast 
      have 0: "min (eint (int N)) (val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x))) = eint N"
      proof- 
        have 00: "\<And> a (b::eint). a \<le> b \<Longrightarrow> min a b = a"
          by (simp add: min_absorb1)
        show ?thesis by(rule 00, rule 0)
      qed
      thus ?thesis 
        using p12 a p11 unfolding 0 p_pow 0 by blast  
    qed
    have p14: "val (\<pp> [^] N \<otimes>(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)) = val (\<pp>[^]N) + val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
      apply(rule val_mult )
       apply blast
      using fr_1_closed by blast
    have p15: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<ge> 0"
      using p13 unfolding p14 
      by (metis add_cancel_eint_geq arith_simps(50) p_pow)
    have p16: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<ge> eint (-N)"
      using p15 N_def 
    proof -
      have "\<exists>i. i + - int N \<le> i"
        by (metis (no_types) more_arith_simps(4) of_nat_0_le_iff)
      then show ?thesis
        by (metis (no_types) arith_simps(50) eint_ord_code(1) eint_ord_trans p15 padic_fields.add_cancel_eint_geq padic_fields_axioms plus_eint_simps(1))
    qed
    have p17: "eint N + eint (2*N) = eint (3*N)"
      by (metis mult_Suc numeral_nat(3) of_nat_add plus_eint_simps(1))
    have R: "\<And>x. x \<in> carrier Q\<^sub>p \<Longrightarrow> val x \<ge> 2*N \<Longrightarrow> Qp_res x (2*N) = 0"
    proof- 
      fix x assume A: "x \<in> carrier Q\<^sub>p" "val x \<ge> 2*N"
      have "eint (int (2 * N)) \<ge> 0"
        by (metis eint_defs(1) eint_ord_simps(1) of_nat_0_le_iff)
      hence R0: "val x \<ge> 0"
        using A N_def eint_ord_trans by blast
      have R1: "x \<in> \<O>\<^sub>p"
        using A R0 val_ring_memI by blast 
      show "Qp_res x (2*N) = 0" apply(rule Qp_res_eq_zeroI)
        using R1 apply blast
        by(rule A)
    qed
    have p18: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 x = (c2 x \<ominus> c1 x) \<otimes> u [^] n"
      apply(rule  Case_iii[of N n t "c1 x" "c2 x"])
      using N_def apply blast
      using t_closed apply blast
      using c1_closed SA_car_closed x_closed apply blast
      using c2_closed SA_car_closed x_closed apply blast
      using p2 apply blast
      using p16 apply blast
      apply(rule R)
      using fr_2_closed apply blast
       apply (smt R0 a eint_nat_times_2 eint_ord_trans fr_2_closed p11 p_natpow_closed(1) p_pow two_times_eint val_mult)
      using locale_assms by blast 
    show "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> lead_coeff xs \<ominus> c1 (tl xs) = (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
      unfolding tx_def list_hd list_tl using p18 by blast 
  qed

  definition u0 where u0_def: "u0 = (\<lambda>xs. (SOME u. u \<in> carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n))"

  lemma m6: "\<And>xs. xs \<in> condition_to_set (S 0) \<Longrightarrow> (u0 xs) \<in> carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
    using u0_def S0_factor SomeE by smt 

  definition u1 where u1_def: "u1 = (\<lambda>xs. if xs \<in> condition_to_set (S 0) then u0 xs else \<one>)"


  lemma u1_closed: "\<And>xs. xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<Longrightarrow> u1 xs \<in> carrier Q\<^sub>p"
    using u1_def m6 Qp.cring_simprules(6) by presburger

  lemma u1E: "\<And>xs. xs \<in> condition_to_set (S 0) \<Longrightarrow>(u1 xs) \<in> carrier Q\<^sub>p \<and> val (u1 xs) = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u1 xs) [^] n"
    using u1_def m6 by presburger

  definition h where h_def: "h = c2 \<ominus>\<^bsub>SA m\<^esub> c1"

  lemma h_closed: "h \<in> carrier (SA m)"
    unfolding h_def using c2_closed c1_closed by blast 
  lemma h_eval: "\<And>xs. xs \<in> condition_to_set (S 0) \<Longrightarrow> h (tl xs) = c2 (tl xs) \<ominus> c1 (tl xs)"
    unfolding S_def condition_to_set.simps cell_def mem_Collect_eq h_def 
    using Qp_pow_ConsE(1) SA_minus_eval c1_closed c2_closed by blast

  lemma case_iii: "is_r_preparable m n 1 (fs \<union> gs) (B13 \<inter> B21)"
  proof(cases "B13 \<inter> B21 = {}")
    case True 
    show ?thesis
      unfolding True
      apply(rule is_r_prepared_imp_is_r_preparable, rule empty_is_1_prepared)
        apply (simp add: fs1 gs1)
      using fs_nonempty apply blast
      using locale_assms by blast 
  next
    case nonempty: False
    have b1: "\<And>l. l \<in> fs \<Longrightarrow> 
              \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c2 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (K l)) \<and>
                   condition_to_set \<D> = condition_to_set \<D>0 \<inter> condition_to_set (K l)"
    proof- 
      fix l assume A: "l \<in> fs"
      obtain B1 g1 g2 J1 where K_params: "K l = Cond m B1 c1 g1 g2  J1"                   
        using K_arity K_center A condition_decomp' by metis
      obtain  h1 h2 Jd where \<D>0_params: "\<D>0 = Cond m b2 c2 h1 h2 Jd"
        using \<D>0_def equal_CondI by metis
      have u1E': "\<And>t x. t \<in> carrier Q\<^sub>p \<Longrightarrow> x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> t # x \<in> condition_to_set \<D>0 \<Longrightarrow> val (u1 (t # x)) = 0 \<and> t \<ominus> c1 x = h x \<otimes> u1 (t # x) [^] n"
      proof- fix t x assume A: "t \<in> carrier Q\<^sub>p"" x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)""t # x \<in> condition_to_set \<D>0"
        have 00: "h x = c2 x \<ominus> c1 x"
          using A unfolding h_def 
          using SA_minus_eval c1_closed c2_closed by blast
        show "val (u1 (t # x)) = 0 \<and> t \<ominus> c1 x = h x \<otimes> u1 (t # x) [^] n"
          using u1E[of "t#x"] A \<D>0_def unfolding list_tl list_hd 00 by blast 
      qed      
      have helper: "(\<Inter>l\<in>fs. condition_to_set (K l)) \<inter> (\<Inter>g\<in>gs. condition_to_set (G g)) \<subseteq>
                    condition_to_set \<D>0 \<inter> condition_to_set (K l)"
        apply(rule subsetI)
        unfolding Int_iff apply(rule conjI)
        using   A  G_g g_def   apply fastforce
        using   A  G_g g_def   by fastforce
      have 01: "\<exists>\<B>. is_cell_condition \<B> \<and> arity \<B> = m \<and> center \<B> = c2 \<and> condition_to_set \<D>0 \<inter> condition_to_set (K l) = condition_to_set \<B>"
        apply(rule change_centers_same_set_ii[of _ _ B1 c1 g1 g2 J1 _ h u1 "condition_to_set \<D>0" _ b2 h1 h2 Jd n N])
        using K_params apply blast
        using A K_cell apply blast
                  apply(rule c2_closed)
                 apply(rule h_closed)
        using u1_closed apply blast
        using helper nonempty unfolding B21_def K_inter apply blast               
        apply blast
        using \<D>0_params apply blast
        using \<D>0_def apply blast
        using locale_assms apply blast
        using N_def apply blast
        apply(rule u1E', blast, blast, blast)
        using centers_neq''' by blast
      thus "  \<exists>\<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c2 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (K l)) \<and>
                   condition_to_set \<D> = condition_to_set \<D>0 \<inter> condition_to_set (K l)" by blast 
    qed
    obtain L where L_def: "L = (\<lambda>l. (SOME \<D>. is_cell_condition \<D> \<and> arity \<D> = m \<and> center \<D> = c2 \<and> (condition_to_set \<D> \<subseteq> condition_to_set (K l)) \<and>
                   condition_to_set \<D> = condition_to_set \<D>0 \<inter> condition_to_set (K l) ))"
      by blast 
    have LE: "\<And>l. l \<in> fs \<Longrightarrow> is_cell_condition (L l) \<and> arity (L l) = m \<and> center (L l) = c2 \<and> (condition_to_set (L l) \<subseteq> condition_to_set (K l)) \<and>
                   condition_to_set (L l) = condition_to_set \<D>0 \<inter> condition_to_set (K l) "
      using b1 L_def SomeE by smt 
    have b2: "B13 \<inter> B21 = (\<Inter> l \<in> fs. condition_to_set (L l)) \<inter> (\<Inter> l \<in> gs. condition_to_set (G l))"
      unfolding B21_def K_inter 
      apply(rule equalityI')
      using G_g g_def LE apply auto[1]
      
      using G_g g_def LE by blast
    obtain M where M_def: "M = (\<lambda>l. if l \<in> fs then L l else G l )"
      by blast 
    have M_fs: "\<And>l. l \<in> fs \<Longrightarrow> M l = L l"
      using M_def by metis 
    have M_gs: "\<And>l. l \<in> gs \<Longrightarrow> M l = G l"
      using locale_assms M_def by (smt IntI empty_iff)
    have M_inter: "B13 \<inter> B21 = (\<Inter> l \<in> fs \<union> gs. condition_to_set (M l))"
    proof-
      have 0: "(\<Inter>l\<in>fs. condition_to_set (L l)) = (\<Inter>l\<in>fs. condition_to_set (M l))"
        using M_fs by (smt Sup.SUP_cong)
      have 1: "(\<Inter>l\<in>gs. condition_to_set (G l)) = (\<Inter>l\<in>gs. condition_to_set (M l))"
        using M_gs by (smt Sup.SUP_cong)
      show ?thesis unfolding 0 1 b2 by blast 
    qed
    have M_center_fs: "\<And>l. l \<in> fs \<Longrightarrow> center (M l) = c2"
      unfolding M_fs using LE by blast 
    have M_center_gs: "\<And>l. l \<in> gs \<Longrightarrow> center (M l) = c2"
      unfolding M_gs using G_center by blast 
    have M_arity_fs: "\<And>l. l \<in> fs \<Longrightarrow> arity (M l) = m"
      unfolding M_fs using LE by blast 
    have M_arity_gs: "\<And>l. l \<in> gs \<Longrightarrow> arity (M l) = m"
      unfolding M_gs using G_arity by blast 
    have M_cell_fs: "\<And>l. l \<in> fs \<Longrightarrow> is_cell_condition (M l)"
      unfolding M_fs using LE by blast 
    have M_cell_gs: "\<And>l. l \<in> gs \<Longrightarrow> is_cell_condition (M l)"
      unfolding M_gs using G_cell by blast 
    have 0: "(center ` M ` (fs \<union> gs)) = {c2}"
      apply(rule equalityI')
      using M_center_fs M_center_gs fs_nonempty apply blast
      unfolding image_iff 
      apply(rule bexI[of _ "M f"])
      using M_center_fs[of f] M_center_gs fs_nonempty f_def
      by auto 
    have b3: "\<And>l. l \<in> fs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n l c1 (condition_to_set (M l)) u h k"
    proof- fix l assume A: "l \<in> fs"
      show "\<exists>u h k. SA_poly_factors p m n l c1 (condition_to_set (M l)) u h k" 
        apply(rule SA_poly_factors_subset[of _ _ _ _ "condition_to_set (\<B>1 l)"])
        apply(rule SA_poly_factors_subset[of _ _ _ _ "condition_to_set (\<C>\<^sub>1 l)"])
        using fs_defs(6)[of l] fs_defs(4)[of l] A 
        using fs_defs(3) apply smt 
        using \<B>1_def refine_fibres_2_subset apply smt
        using M_fs LE K_f K_not_f \<C>3_subset F3_f F3_not_f 
       by (smt (z3) A F3_sub IntE subsetD subsetI)
    qed
    have b4: "\<And>l t x.
              l \<in> fs \<Longrightarrow>
              t \<in> carrier Q\<^sub>p \<Longrightarrow>
              t # x \<in> condition_to_set (M l) \<Longrightarrow>
              t # x \<in> condition_to_set (M l) \<Longrightarrow> val (u1 (t # x)) = 0 \<and> t \<ominus> c1 x = (t \<ominus> center (M l) x) [^] (0::nat) \<otimes> h x \<otimes> u1 (t # x) [^] n"
    proof-
      fix l t x 
      assume a: " l \<in> fs" " t \<in> carrier Q\<^sub>p" " t # x \<in> condition_to_set (M l)"
        " t # x \<in> condition_to_set (M l)"
      have 0: "M l = L l"
        using a M_fs by blast 
      have 1: "condition_to_set (M l) \<subseteq> condition_to_set \<D>0"
        unfolding 0 using LE[of l] a by blast 
      have 2: "condition_to_set (M l) \<subseteq> condition_to_set (S 0)"
        using 1 \<D>0_def by blast 
      have 3: "h x = c2 x \<ominus> c1 x"
        using h_eval[of "t#x"] a 2 unfolding list_tl by blast 
      have 4: "(t \<ominus> center (M l) x) [^] (0::nat)= \<one>"
        using Qp.nat_pow_0 by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using a M_arity_fs 
        by (metis condition_to_set_memE(2) list_tl)
      have 5: " \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u1 (t # x) [^] n = (c2 x \<ominus> c1 x) \<otimes> u1 (t # x) [^] n"
        using c2_closed c1_closed SA_car_closed x_closed a 
        by (metis "3" Qp.cring_simprules(12) h_closed)
      show "val (u1 (t # x)) = 0 \<and> t \<ominus> c1 x = (t \<ominus> center (M l) x) [^] (0::nat) \<otimes> h x \<otimes> u1 (t # x) [^] n"
        using u1E[of "t#x"] a 2  unfolding 4 3 list_tl list_hd 5 by blast 
    qed
    have 1: "\<And>l. l \<in> fs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n l (center (M l)) (condition_to_set (M l)) u h k"
      apply(rule SA_poly_factors_change_of_center[of _ _ _ c1 _ _ h u1 "0::nat"])
          apply(rule b3, blast) unfolding M_center_fs apply(rule c2_closed)
        apply(rule h_closed)
      using u1_closed apply blast
      using b4  M_center_fs by presburger
    have 2: "\<And>l. l \<in> gs \<Longrightarrow> \<exists>u h k. SA_poly_factors p m n l (center (M l)) (condition_to_set (M l)) u h k"
    proof- fix l assume A: "l \<in> gs"
      have 20: "center (M l) = c2"
        using A M_center_gs by blast 
      have 21: "center (\<C>\<^sub>2 l) = c2"
        using A gs_defs(3) by blast
      have 22: "M l = G l"
        using A M_gs by blast 
      have 23: "condition_to_set (M l) \<subseteq> condition_to_set (\<B>2 l)"
        unfolding 22 apply(cases "l = g")
        using G_g \<D>0_def apply simp
        unfolding  G_not_g by blast                    
      show " \<exists>u h k. SA_poly_factors p m n l (center (M l)) (condition_to_set (M l)) u h k"
        unfolding 20 
        apply(rule SA_poly_factors_subset[of _ _ _ _  "condition_to_set (\<B>2 l)"])
         apply(rule SA_poly_factors_subset[of _ _ _ _  "condition_to_set (\<C>\<^sub>2 l)"])
        using gs_defs(6)[of l] A unfolding 21 apply blast
        using \<B>2_def refine_fibres_2_subset apply smt
        by(rule 23)
    qed
    show "is_r_preparable m n 1 (fs \<union> gs) (B13 \<inter> B21)"
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _  M "M ` (fs \<union> gs)"]) 
      using fs1 gs1 apply blast
      using locale_assms apply blast
           apply blast
      unfolding 0 apply simp
      using M_cell_fs M_cell_gs apply blast
      using M_arity_fs M_arity_gs apply blast
      using 1 2 apply blast
      unfolding M_inter by blast 
  qed

  lemma m7: "is_c_decomposable m c2 (B2 - B21)"
    apply(rule diff_is_c_decomposable) unfolding B2_def
     apply(rule finite_int_is_c_decomposable)
        apply(rule c2_closed)
    using gs1 apply blast
    using gs_nonempty apply blast
  proof- 
    fix A assume A: "A \<in> (\<lambda>f. condition_to_set (\<B>2 f)) ` gs"
    then obtain g where g_def: "g \<in> gs \<and> A = condition_to_set (\<B>2 g)"
      by blast 
    obtain B f1 f2 J where params: "\<B>2 g = Cond m B c2 f1 f2 J"
      using g_def 
      by (metis \<B>2_arity \<B>2_center condition_decomp')
    have 0: "A = condition_to_set (\<B>2 g)"
      using g_def by blast 
    show "is_c_decomposable m c2 A"
      unfolding 0 params apply(rule c_cell_is_c_decomposable)
      using  g_def  unfolding params 
      by (metis \<B>2_cond params)      
  next 
    show "is_c_decomposable m c2 B21"
      unfolding B21_def 
     apply(rule finite_int_is_c_decomposable)
         apply(rule c2_closed)
      using gs1 apply blast
      using gs_nonempty apply blast
    proof- 
      fix A assume A: " A \<in> (\<lambda>g. condition_to_set (G g)) ` gs"
    then obtain g where g_def: "g \<in> gs \<and> A = condition_to_set (G g)"
      by blast 
    obtain B f1 f2 J where params: "G g = Cond m B c2 f1 f2 J"
      using g_def G_center G_arity 
      by (metis condition_decomp')
    have 0: "A = condition_to_set (G g)"
      using g_def by blast 
    show "is_c_decomposable m c2 A"
      unfolding 0 params apply(rule c_cell_is_c_decomposable)
      using G_cell[of g] g_def  unfolding params by blast           
  qed
  qed

  definition Xs where Xs: "Xs = (SOME Xs. is_cell_decomp m Xs (B2 - B21) \<and> Xs \<noteq> {} \<and> (\<forall>C \<in> Xs. center C = c2))"

  lemma Xs_def: "is_cell_decomp m Xs (B2 - B21) \<and> Xs \<noteq> {} \<and> (\<forall>C \<in> Xs. center C = c2)"
    apply(rule some_fact[of Xs], rule Xs)
    using m7 unfolding is_c_decomposable_def by blast 

  definition Ps where Ps_def: "Ps = insert B21 (condition_to_set  ` Xs)"

  lemma C0: "\<And>x . x \<in> Ps  \<Longrightarrow> x \<noteq> B21 \<Longrightarrow> x \<inter> B21 = {}"
    unfolding Ps_def 
    using Xs_def is_cell_decomp_subset[of m Xs "B2 - B21"] image_iff 
    by blast

  lemma C1: "\<And>x y . x \<in> Ps  \<Longrightarrow> y \<in> Ps \<Longrightarrow> x \<noteq> B21 \<Longrightarrow> y \<noteq> B21 \<Longrightarrow> x \<noteq> y \<Longrightarrow>  x \<inter> y = {}"
    apply(rule disjointE[of "condition_to_set  `Xs"])
       apply(rule is_partitionE[of _ "B2 - B21"])
       apply(rule is_cell_decompE[of m "Xs"])
    using Xs_def apply blast
    unfolding Ps_def apply blast
    unfolding Ps_def apply blast
    by blast 

  lemma C2: "disjoint Ps"
    apply(rule disjointI)
    using C0 C1 by blast

  lemma C3: " \<Union> (condition_to_set ` Xs) = B2 - B21"
    using Xs_def is_cell_decompE(2)[of m Xs "B2 - B21"]
                        is_partitionE(2)[of "condition_to_set ` Xs" "B2 - B21"] by blast 

  lemma C4: "\<Union> (insert B21 (condition_to_set ` Xs)) = B21 \<union> \<Union> (condition_to_set ` Xs)"
    by blast 

  lemma C5: "\<And>g. g \<in> gs \<Longrightarrow> condition_to_set (G g) \<subseteq> condition_to_set (\<B>2 g)"
    using G_g \<D>0_def G_not_g 
    by (metis Int_iff subsetI)

  lemma C6: "B21 \<subseteq> B2"
    unfolding B21_def B2_def using C5 by blast 

  lemma C7: "Ps partitions B2"
    apply(rule is_partitionI, rule C2)
    unfolding Ps_def C4 C3 g_def using C6 by blast 

  definition Qs where Qs_def: "Qs = (\<inter>) B13 ` Ps"

  lemma Qs_partitions: "Qs partitions (B13 \<inter> B2)"
    apply(rule is_partitionI)
     apply(rule disjointI)
    unfolding Qs_def using is_partitionE disjointE C7 
     apply blast
    unfolding Qs_def using is_partitionE[of Ps B2] C7
    by blast

lemma middle_cut_is_preparable: "is_r_preparable m n 1 (fs \<union> gs) (B13 \<inter> B2)"
  apply(rule is_r_preparable_partition[of Qs])
  using Qs_def Ps_def Xs_def 
    apply (metis finite.insertI finite_imageI is_cell_decompE(1))
  using Qs_partitions Xs_def apply blast 
proof- 
  fix a assume A: "a \<in> Qs"
  then obtain P where P_def: "P \<in> Ps \<and> a = B13 \<inter> P"
    unfolding Qs_def  by blast 
  show "is_r_preparable m n 1 (fs \<union> gs) a"
  proof(cases "a = B13 \<inter> B21")
    case True
    then show ?thesis using case_iii by blast 
  next
    case a_neq: False
    have p0: "P \<in> condition_to_set  ` Xs"
      using P_def a_neq unfolding Ps_def by blast 
    then obtain \<D> where \<D>_def: "\<D> \<in> Xs \<and> P = condition_to_set \<D>"
      by blast 
    have \<D>_arity: "arity \<D> = m"
      using \<D>_def Xs_def is_cell_decompE(4) by blast
    have \<D>_center: "center \<D> = c2"
      using \<D>_def Xs_def by blast 
    obtain D1 d1 d2 Jd where \<D>_params: "\<D> = Cond m D1 c2 d1 d2 Jd"
      using \<D>_arity \<D>_center condition_decomp' by smt
    have \<D>_sub: "condition_to_set \<D> \<subseteq> condition_to_set (\<B>2 g)"
      using \<D>_def P_def C7 is_partitionE \<D>0_def g_def unfolding B2_def by blast 
    have \<D>_disj: "condition_to_set \<D> \<inter> B21 = {}"
      using \<D>_def \<D>_sub p0 Xs_def is_cell_decomp_subset by blast 
    have \<D>_disj': "condition_to_set \<D> \<inter> condition_to_set \<D>0 = {}"
    proof- 
      have 0: "condition_to_set \<D> \<subseteq> B2"
        using G_not_g  \<D>_def P_def C7 is_partitionE \<D>0_def g_def unfolding B2_def 
        by blast 
      have 1: "condition_to_set \<D> \<subseteq> (\<Inter>f\<in>gs - {g}. condition_to_set (G f))"
        apply(rule subset_trans[of _ "(\<Inter>f\<in>gs. condition_to_set (\<B>2 f))"])
        using 0 unfolding B2_def apply blast 
        using G_not_g 
       by (simp add: INF_superset_mono)
      have 2: "condition_to_set \<D>0 = condition_to_set (G g)"
        unfolding G_g by blast 
      show ?thesis 
      using \<D>_disj 1 unfolding B21_def 2   by blast 
    qed
    have \<D>_disj'': "condition_to_set \<D> \<inter> condition_to_set (S 0) = {}"
      using \<D>_sub \<D>_disj' using \<D>0_def by blast 
    obtain \<D>' where \<D>'_def: "\<D>' = refine_fibres_2 \<D> b2"
      by blast 
    have \<D>'_set: "condition_to_set \<D> = condition_to_set \<D>'"
      unfolding \<D>'_def apply(rule equalityI')
      using \<D>_sub unfolding \<B>2_g_params \<D>_params condition_to_set.simps refine_fibres_2_def 
              refine_fibres_def cell_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
       apply blast
      using refine_fibres_2_subset 
          by blast 
    have \<D>'_params: "\<D>' = Cond m (D1 \<inter> b2) c2 d1 d2 Jd" 
      unfolding \<D>_params \<D>'_def refine_fibres_2_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
      by blast 
    have one_c1_cell: "\<exists>\<C>'. is_cell_condition \<C>' \<and> center \<C>' = c1 \<and> arity \<C>' = m \<and> 
        fibre_set \<C>' = \<Inter> (fibre_set ` (K ` fs)) \<and> condition_to_set \<C>' = \<Inter> (condition_to_set ` (K ` fs))"
      apply(rule cell_finite_intersection_same_center[of _ c1 m])
      using fs1 apply blast
      using K_cell apply blast
      using K_center apply blast
      using K_arity apply blast
      using fs_nonempty by blast 
    then obtain \<C> where \<C>_def: "is_cell_condition \<C> \<and> center \<C> = c1 \<and> arity \<C> = m \<and> 
        fibre_set \<C> = \<Inter> (fibre_set ` (K ` fs)) \<and> condition_to_set \<C> = \<Inter> (condition_to_set ` (K ` fs))"
      by blast 
    have \<C>_eq: "condition_to_set \<C> = \<Inter> (condition_to_set ` (K ` fs))"
      using \<C>_def by blast 
    have B13_as_cell: "B13 = condition_to_set \<C>"
      unfolding K_inter \<C>_eq by blast 
    have a_inter: "a = condition_to_set \<C> \<inter> condition_to_set \<D>"
      using P_def unfolding B13_as_cell using \<D>_def by blast 
    obtain C1 r1 r2 Jc where \<C>_params: "\<C> = Cond m C1 c1 r1 r2 Jc"
      using \<C>_def condition_decomp' by smt
    have q0: "\<And>t x. t#x \<in> condition_to_set \<D> \<Longrightarrow> c1 x \<noteq> c2 x"
      unfolding \<D>'_set \<D>'_params condition_to_set.simps cell_def mem_Collect_eq list_tl 
      by (meson Int_iff centers_neq''')
    have q1: "\<And>t x. t#x \<in> condition_to_set \<D> \<Longrightarrow> c1 x \<in> carrier Q\<^sub>p"
      apply(rule SA_car_closed[of _ m], rule c1_closed)
      unfolding \<D>_params 
      by (metis Qp_pow_ConsE(1) \<D>_arity \<D>_params condition_to_set_memE(1) list_tl)
    have q2: "\<And>t x. t#x \<in> condition_to_set \<D> \<Longrightarrow> c2 x \<in> carrier Q\<^sub>p"
      apply(rule SA_car_closed[of _ m], rule c2_closed)
      unfolding \<D>_params 
      by (metis Qp_pow_ConsE(1) cell_memE(1) condition_to_set.simps list_tl)
    have q3:  "\<And>t x. t#x \<in> condition_to_set \<D> \<Longrightarrow>c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
      using q0 q1 q2 Qp.not_eq_diff_nonzero by blast
    have q4: "\<And>t x. t#x \<in> a \<Longrightarrow> eint (- int N) \<le> val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have 0:"a \<subseteq> B13"
        using local.P_def by blast
      have 1: "t#x \<in> condition_to_set \<C>3"
        using 0 A unfolding helper by blast 
      show " eint (- int N) \<le> val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        using \<C>3_memE 1  by metis 
    qed
    have q5:  "\<And>t x. t#x \<in> a\<Longrightarrow>  val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) < eint (int N)"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have 0:"a \<subseteq> B13"
        using local.P_def by blast
      show "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) < eint (int N)"
        using 0 \<C>3_memE unfolding B13_def 
        by (metis A \<open>\<And>thesis. (\<And>P. P \<in> Ps \<and> a = B13 \<inter> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> helper mem_simps(4))
    qed
    have q6: "\<And>t x. t#x \<in> a \<Longrightarrow>  (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) \<in> \<O>\<^sub>p"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using P_def A unfolding helper \<C>3_params condition_to_set.simps cell_def Int_iff mem_Collect_eq 
        by (metis (no_types, lifting) B13_hd \<open>\<And>thesis. (\<And>P. P \<in> Ps \<and> a = B13 \<inter> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> list_hd mem_simps(4))
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using P_def A unfolding helper \<C>3_params condition_to_set.simps cell_def Int_iff mem_Collect_eq 
        by (metis (no_types, lifting) B13_eq Qp_pow_ConsE(1) list_tl mem_Collect_eq mem_simps(4))
      have 00: " (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
        apply(rule equation_6[of t "c1 x" "c2 x" N])
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      obtain A where A_def: "A = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x)"
        by blast 
      obtain B where B_def: "B = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x)"
        by blast 
      have E_alt: "B =  \<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)"
        unfolding B_def   apply(rule equation_6_alt[of t "c1 x" "c2 x" "c2 x" N]) 
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      have A_alt: "A =  \<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        unfolding A_def   apply(rule equation_6_alt[of t "c1 x" "c2 x" "c1 x" N]) 
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
         apply(rule q1[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      have A_closed: "A \<in> carrier Q\<^sub>p"
        unfolding A_def apply(rule Qp.ring_simprules) apply(rule fract_closed)
          apply blast
         apply(rule q3[of t])
        using A unfolding a_inter apply blast
       apply(rule Qp.ring_simprules, rule t_closed, rule q1[of t])
        using A unfolding a_inter by blast 
      have B_closed: "B \<in> carrier Q\<^sub>p"
        unfolding B_def apply(rule Qp.ring_simprules) apply(rule fract_closed)
          apply blast
         apply(rule q3[of t])
        using A unfolding a_inter apply blast
       apply(rule Qp.ring_simprules, rule t_closed, rule q2[of t])
        using A unfolding a_inter by blast
      have A_eq: "A = B \<oplus> \<pp>[^]N"
        unfolding A_def B_def 
        using "00" by blast
      have 01: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
        apply(rule q3[of t])
        using A unfolding a_inter by blast
      have 02: "c1 x \<in> carrier Q\<^sub>p"
        apply(rule q1[of t])   
        using A unfolding a_inter by blast
      have 03: "c2 x \<in> carrier Q\<^sub>p"
        apply(rule q2[of t])   
        using A unfolding a_inter by blast
      have B_eq: "B = A \<ominus> \<pp>[^]N"
        unfolding A_eq a_minus_def using B_closed 
        by (metis Qp.add.inv_solve_right' Qp.add.m_closed p_natpow_closed(1))
      have 04: " eint (- int N) \<le> val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        apply(rule q4)
        by(rule A)
      have 05: "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
        using 01 02 03 t_closed Qp.cring_simprules(4) fract_closed by blast
      have A_val: "val A \<ge> 0"
        unfolding A_alt 
        using val_mult[of "\<pp> [^] N " "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"]
        unfolding p_pow using 04 05 
        by (metis A_alt add.right_inverse add_left_mono eint_defs(1) p_natpow_closed(1) plus_eint_simps(1))
      have A_in: "A \<in> \<O>\<^sub>p"
        using A_val A_closed val_ring_memI by blast 
      have 06: "\<ominus>\<pp>[^]N \<in> \<O>\<^sub>p"
        using val_ring_ainv_closed val_ring_int_inc_closed val_ring_nat_pow_closed by presburger
      have 07: "B \<in> \<O>\<^sub>p"
        unfolding B_eq a_minus_def using A_in 06 
        by (metis A_eq Q\<^sub>p_def Qp.cring_simprules(15) Zp_def \<iota>_def p_inc padic_fields.val_ring_minus_closed padic_fields_axioms val_ring_int_inc_closed val_ring_nat_pow_closed)
      show "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
        using 07 unfolding E_alt by blast 
    qed
    have q7: "\<And>t x. t#x \<in> a \<Longrightarrow>  Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<in> carrier (Zp_res_ring (2*N))"
      using q6 Qp_res_closed by blast
    have q7': "\<And>t x. t#x \<in> a \<Longrightarrow>  Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<in> carrier (Zp_res_ring (3*N))"
      using q6 Qp_res_closed by blast
    
    have q8: "\<And>t x. t#x \<in> a \<Longrightarrow>  Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> 0"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using P_def A unfolding helper \<C>3_params condition_to_set.simps cell_def Int_iff mem_Collect_eq 
        by (metis (no_types, lifting) B13_hd \<open>\<And>thesis. (\<And>P. P \<in> Ps \<and> a = B13 \<inter> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> list_hd mem_simps(4))
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using P_def A unfolding helper \<C>3_params condition_to_set.simps cell_def Int_iff mem_Collect_eq 
        by (metis (no_types, lifting) B13_eq Qp_pow_ConsE(1) list_tl mem_Collect_eq mem_simps(4))
      have 00: " (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
        apply(rule equation_6[of t "c1 x" "c2 x" N])
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      obtain A where A_def: "A = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x)"
        by blast 
      obtain B where B_def: "B = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x)"
        by blast 
      have E_alt: "B =  \<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)"
        unfolding B_def   apply(rule equation_6_alt[of t "c1 x" "c2 x" "c2 x" N]) 
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      have A_alt: "A =  \<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        unfolding A_def   apply(rule equation_6_alt[of t "c1 x" "c2 x" "c1 x" N]) 
           apply(rule t_closed, rule q1[of t])
        using A unfolding a_inter apply blast
         apply(rule q2[of t])
        using A unfolding a_inter apply blast
         apply(rule q1[of t])
        using A unfolding a_inter apply blast
        using  q0[of t]  A unfolding a_inter by blast
      have A_closed: "A \<in> carrier Q\<^sub>p"
        unfolding A_def apply(rule Qp.ring_simprules) apply(rule fract_closed)
          apply blast
         apply(rule q3[of t])
        using A unfolding a_inter apply blast
       apply(rule Qp.ring_simprules, rule t_closed, rule q1[of t])
        using A unfolding a_inter by blast 
      have B_closed: "B \<in> carrier Q\<^sub>p"
        unfolding B_def apply(rule Qp.ring_simprules) apply(rule fract_closed)
          apply blast
         apply(rule q3[of t])
        using A unfolding a_inter apply blast
       apply(rule Qp.ring_simprules, rule t_closed, rule q2[of t])
        using A unfolding a_inter by blast
      have A_eq: "A = B \<oplus> \<pp>[^]N"
        unfolding A_def B_def 
        using "00" by blast
      have 01: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
        apply(rule q3[of t])
        using A unfolding a_inter by blast
      have 02: "c1 x \<in> carrier Q\<^sub>p"
        apply(rule q1[of t])   
        using A unfolding a_inter by blast
      have 03: "c2 x \<in> carrier Q\<^sub>p"
        apply(rule q2[of t])   
        using A unfolding a_inter by blast
      have B_eq: "B = A \<ominus> \<pp>[^]N"
        unfolding A_eq a_minus_def using B_closed 
        by (metis Qp.add.inv_solve_right' Qp.add.m_closed p_natpow_closed(1))
      have 04: " eint (- int N) \<le> val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        apply(rule q4)
        by(rule A)
      have 05: "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
        using 01 02 03 t_closed Qp.cring_simprules(4) fract_closed by blast
      have A_val: "val A \<ge> 0"
        unfolding A_alt 
        using val_mult[of "\<pp> [^] N " "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"]
        unfolding p_pow using 04 05 
        by (metis A_alt add.right_inverse add_left_mono eint_defs(1) p_natpow_closed(1) plus_eint_simps(1))
      have A_in: "A \<in> \<O>\<^sub>p"
        using A_val A_closed val_ring_memI by blast 
      have 06: "\<ominus>\<pp>[^]N \<in> \<O>\<^sub>p"
        using val_ring_ainv_closed val_ring_int_inc_closed val_ring_nat_pow_closed by presburger
      have 07: "B \<in> \<O>\<^sub>p"
        unfolding B_eq a_minus_def using A_in 06 
        by (metis Q\<^sub>p_def Qp.cring_simprules(15) Zp_def \<iota>_def p_inc padic_fields.val_ring_minus_closed padic_fields_axioms val_ring_int_inc_closed val_ring_nat_pow_closed)
      have 08: "val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) < eint (int N)"
        apply(rule q5) 
        by(rule A)
      have 09: "val A = N + val (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
        unfolding A_alt 
        using val_mult[of "\<pp> [^] N " "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"]
        unfolding p_pow 
        using "05" by blast
      have 10: "t#x \<in> B13"
        using A helper local.P_def by blast
      have 11: "t#x \<in> B2 - B21"
        using p0 P_def A Xs_def is_cell_decomp_subset 
        by (smt \<open>\<And>thesis. (\<And>\<D>. \<D> \<in> Xs \<and> P = condition_to_set \<D> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> basic_trans_rules(31) mem_simps(4))
      have 12: "t#x \<notin> condition_to_set \<D>0"
        using 11 B21_def G_g g_def A \<D>_def \<D>_disj' local.P_def by blast
      have 13: "t#x \<in> condition_to_set (\<B>2 g)"
        by (metis A IntD2 \<D>_sub a_inter subsetD)
      hence 14: "t#x \<notin> condition_to_set (S 0)"
        using \<D>0_def 12 by blast 
      hence 15: "val (t \<ominus> T 0 x) \<notin> I[val (lb x) val (\<zero>\<^bsub>SA m\<^esub> x)]"
        using 14 13 unfolding S_def condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
          \<B>2_g_params by blast 
      have 16: "val (t \<ominus> T 0 x) \<le> val (\<zero>\<^bsub>SA m\<^esub> x)"
        using x_closed SA_zeroE[of x m] val_zero 
        using eint_ord_simps(3) by presburger
      have 17: "val (t \<ominus> T 0 x) < val (lb x)"
        using 15 16 unfolding closed_interval_def mem_Collect_eq 
        using notin_closed by blast
      have 18: "lb x = \<pp> [^] (N) \<otimes> (c2 x \<ominus> c1 x)"
        apply(rule lb_eval[of x]) by(rule x_closed)
      have 19: "t \<ominus> T 0 x = t \<ominus> c2 x"
        using T_0 by presburger
      have R: "\<And> a b. a \<in> carrier Q\<^sub>p\<Longrightarrow> b \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                                    val a <val (\<pp>[^](N) \<otimes> b) \<Longrightarrow> val (a \<div> b) < val(\<pp>[^](N)) "
        by (metis Qp.cring_simprules(14) Qp.nonzero_memE(1) fract_closed local.fract_cancel_right p_natpow_closed(1) val_ineq_cancel_le)
      have R': "\<And> c. c \<in> carrier Q\<^sub>p \<Longrightarrow> val c < val(\<pp>[^](N)) \<Longrightarrow> val(\<pp>[^](N) \<otimes> c) < val (\<pp>[^]N \<otimes> \<pp>[^]N)"
        using val_mult[of "\<pp>[^]N"] unfolding p_pow 
        by (metis p_natpow_closed(1) p_natpow_closed(2) p_pow val_ineq_cancel_le' val_p_int_pow)
      have 20: "val (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) < val (\<pp>[^]N \<otimes> \<pp>[^]N)"
        apply(rule R') 
        using 01 02 03 t_closed Qp.cring_simprules(4) fract_closed apply blast
        apply(rule R)
        using 02 03 t_closed Qp.cring_simprules(4) apply blast
         apply(rule 01)
        using 17 unfolding 18 19 by blast 
      have 21: "val (\<pp>[^]N \<otimes> \<pp>[^]N) = 2*N"
        using val_mult[of "\<pp>[^]N" "\<pp>[^]N"] unfolding p_pow 
        using eint_nat_times_2 p_natpow_closed(1) two_times_eint by presburger
      have R'': "\<And>a. a \<in> \<O>\<^sub>p \<Longrightarrow> val a < 2*N \<Longrightarrow> Qp_res a (2*N) \<noteq> 0"
        using Qp_res_eqE[of _ \<zero> "2*N"] 
        by (metis Qp.minus_zero Qp_res_neqI Qp_res_zero val_ring_memE zero_in_val_ring)
      show "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> 0 "
        apply(rule R'' )
        using 01 02 03 t_closed Qp.cring_simprules(4) fract_closed "07" E_alt apply force
        using 20 unfolding 21 by blast 
     qed
    have q8': "\<And>t x. t#x \<in> a \<Longrightarrow>  Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<noteq> 0"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have R: "\<And>b n k. b \<in> \<O>\<^sub>p \<Longrightarrow> n < k \<Longrightarrow>  Qp_res b n \<noteq> 0 \<Longrightarrow> Qp_res b k \<noteq> 0"
        by (smt Qp_res_def equal_res_imp_res_diff_zero equal_res_mod to_Zp_closed val_ring_memE(2) val_ring_minus_closed)
      show "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<noteq> 0"
        apply(rule R[of _ "2*N"], rule q6, rule A) 
        using N_def apply linarith 
        by(rule q8, rule A)
    qed
    have q9: "\<And>t x. t#x \<in> a \<Longrightarrow>  Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> Qp_res (\<ominus> (\<pp> [^] N)) (2 * N)"
    proof- fix t x assume A: "t#x \<in> a"
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using P_def A unfolding helper \<C>3_params condition_to_set.simps cell_def Int_iff mem_Collect_eq 
        by (metis (no_types, lifting) B13_hd \<open>\<And>thesis. (\<And>P. P \<in> Ps \<and> a = B13 \<inter> P \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> list_hd mem_simps(4))               
      have 01: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
        apply(rule q3[of t])
        using A unfolding a_inter by blast
      have 02: "c1 x \<in> carrier Q\<^sub>p"
        apply(rule q1[of t])   
        using A unfolding a_inter by blast
      have 03: "c2 x \<in> carrier Q\<^sub>p"
        apply(rule q2[of t])   
        using A unfolding a_inter by blast
      show"Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> Qp_res (\<ominus> (\<pp> [^] N)) (2 * N)"
        apply(rule not_Case_i_or_Case_ii_or_Case_iii_imp_Case_iv[of n])
        using locale_assms apply blast
        using N_def apply blast
              apply(rule t_closed, rule 02, rule 03)
        using 01 02 03 
        apply (metis Qp.not_nonzero_memI Qp.r_right_minus_eq)
          apply(rule q5, rule A)
         apply(rule q4, rule A)
        by(rule q8, rule A)
    qed
    have p_pow': "val (\<pp>[^](2*N)) = 2*N"
      using ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
    have p_nat: "\<And>n::nat. val (\<pp>[^]n) = n"
      using ord_p_pow_nat p_natpow_closed(2) val_ord by presburger
    have p_int: "\<And>n::int. val (\<pp>[^]n) = n"
      using ord_p_pow_int p_intpow_closed  val_ord by presburger
    obtain lb' where lb'_def: "lb' = \<pp>[^](2*N) \<odot>\<^bsub>SA m\<^esub> (c2 \<ominus>\<^bsub>SA m\<^esub> c1)"
      by blast 
    have lb'_closed: "lb' \<in> carrier (SA m)"
      unfolding lb'_def using c2_closed c1_closed 
      by (meson SA_minus_closed SA_smult_closed p_natpow_closed(1))
    have lb'_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> lb' x = \<pp>[^](2*N) \<otimes> (c2 x \<ominus> c1 x)"
      unfolding lb'_def 
      using SA_minus_eval SA_smult_formula c1_closed c2_closed p_natpow_closed(1) padic_fields.SA_minus_closed padic_fields_axioms by presburger
    obtain S' where S'_def: "S' = (\<lambda> a. Cond m b2 (T a) lb' (\<zero>\<^bsub>SA m\<^esub>)  closed_interval)  "
      by blast 
    have S'_cell_cond: "\<And> a. is_cell_condition (S' a)"
      unfolding S'_def apply(rule is_cell_conditionI')
      using m3 unfolding \<B>2_g_params using is_cell_conditionE''(1) apply blast 
         apply(rule T_closed, rule lb'_closed)
       apply blast
      by (simp add: is_convex_condition_def)
    have in_S': "\<And>t x b. t#x \<in> a \<Longrightarrow> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b \<Longrightarrow> 
                  t#x \<in> condition_to_set (S' b)"
    proof- 
      fix t x b assume A: " t # x \<in> a" "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using A unfolding \<D>_params condition_to_set.simps cell_def mem_Collect_eq list_hd list_tl 
        using A(1) cell_cond_head_closure unfolding a_inter by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A unfolding \<D>_params condition_to_set.simps cell_def mem_Collect_eq list_hd list_tl a_inter Int_iff
        by (metis Qp_pow_ConsE list_tl)
      have p0: "val (lb' x) \<le> val (t \<ominus> T b x)"
      proof- 
        have w0: "lb' x =  \<pp> [^] (2*N) \<otimes> (c2 x \<ominus> c1 x)"
          using lb'_eval[of x] x_closed by blast 
        have w1: "T b x = c2 x \<oplus> (c2 x \<ominus> c1 x) \<otimes> (\<pp>[^](-N) \<otimes>[b] \<cdot> \<one>)"
          using T_eval[of x b] x_closed by blast 
        have c2: "c2 x \<in> carrier Q\<^sub>p"
          using c2_closed SA_car_closed x_closed by blast 
        have c1: "c1 x \<in> carrier Q\<^sub>p"
          using c1_closed SA_car_closed x_closed by blast 
        have R0: "\<And> a b c. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
              t \<ominus> (a \<oplus> (a \<ominus> b)\<otimes>c) = (t \<ominus> a) \<ominus> (a \<ominus> b)\<otimes>c"
          unfolding a_minus_def using t_closed Qp.a_ac(1) Qp.cring_simprules(1) 
            Qp.cring_simprules(20) Qp.cring_simprules(3) Qp.cring_simprules(5) by presburger
        have w2: "(t \<ominus> T b x) = (t \<ominus> (c2 x)) \<ominus> (c2 x \<ominus>c1 x)\<otimes>(\<pp>[^](-N) \<otimes>[b] \<cdot> \<one>)"
          unfolding w1 using R0  Qp.int_inc_closed c1 c2 
          using Qp.m_closed p_intpow_closed(1) by presburger
        have w3: "(c2 x \<ominus>c1 x) \<in> nonzero Q\<^sub>p"
          apply(rule q3)
          using A unfolding a_inter by blast 
        have R1:  "\<And> a b c d. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> nonzero Q\<^sub>p; c \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
            ((a \<ominus> (b \<otimes> c)) \<div> b) = (a \<div> b) \<ominus> c"
          by (smt Qp.cring_simprules(24) Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.nonzero_memE(1) Qp.not_nonzero_memI Qp.r_minus_distr Qp.r_one field_inv(1) nonzero_inverse_Qp)
        have w4: "((t \<ominus> T b x)\<div>(c2 x \<ominus> c1 x)) =( (t \<ominus> (c2 x))\<div>(c2 x \<ominus> c1 x)) \<ominus> (\<pp>[^]-N \<otimes>[b] \<cdot> \<one>)"
          unfolding w2 apply(rule R1)
          using c2 t_closed apply blast
           apply(rule w3)
          using p_intpow_closed(1) by blast
        have w5: "(lb' x \<div>(c2 x \<ominus> c1 x)) = \<pp>[^](2*N)"
          unfolding w0 using w3 
          using Qp.int_inc_closed Qp.int_nat_pow_rep Qp.m_assoc Qp.m_comm 
            Qp.nonzero_closed local.fract_cancel_right nonzero_inverse_Qp 
          by metis
        have w6: "val (\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>) \<ge> 3*N"
          apply(rule Qp_res_eqE, rule q6)
          using A apply blast
          using val_ring_int_inc_closed apply blast
          apply(rule Qp_res_equal, rule q6, rule A)
          using A by blast 
        have R2: "\<And> a b. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
                \<pp>[^]-N \<otimes>  (\<pp> [^] N \<otimes> a \<ominus> b) = a \<ominus> (\<pp>[^]-N \<otimes> b)"
          
        proof -
        fix ac :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set" and bb :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"
        assume a1: "ac \<in> carrier Q\<^sub>p"
        assume a2: "bb \<in> carrier Q\<^sub>p"
        have f3: "\<forall>x0. - (x0::int) = - 1 * x0"
          by presburger
        have "- 1 * (- 1 * int N) = int N"
          by presburger
        then have "\<pp> [^] N \<otimes> ac = (ac \<div> \<pp> [^] (- 1 * int N))"
          using f3 a1 by (metis Qp.cring_simprules(14) int_pow_int p_intpow_closed(1) p_intpow_inv'')
        then have f4: "\<pp> [^] N \<otimes> ac \<ominus> bb = (ac \<ominus> \<pp> [^] (- 1 * int N) \<otimes> bb \<div> \<pp> [^] (- 1 * int N))"
          using a2 a1 Qp_int_pow_nonzero R1 p_nonzero by presburger
        have "- int N = - 1 * int N"
          by presburger
        then show "\<pp> [^] - int N \<otimes> (\<pp> [^] N \<otimes> ac \<ominus> bb) = ac \<ominus> \<pp> [^] - int N \<otimes> bb"
          using f4 a2 a1 Qp.cring_simprules(4) Qp.cring_simprules(5) Qp_int_pow_nonzero local.fract_cancel_right p_intpow_closed(1) p_nonzero by presburger
        qed
        have R3: "\<And>a b. a \<in> carrier Q\<^sub>p\<Longrightarrow> b \<in> carrier Q\<^sub>p\<Longrightarrow> val a \<le> val b \<Longrightarrow> val (\<pp>[^](-N) \<otimes> a) \<le> val (\<pp>[^](-N) \<otimes> b)"
          using val_mult 
          by (metis add_right_mono times_p_pow_val)
        have R4: "\<And> a. a \<in> carrier Q\<^sub>p \<Longrightarrow> val a \<ge> 3*N \<Longrightarrow> 
                val (\<pp>[^](-N)\<otimes> a) \<ge> 2*N"
        proof- 
          fix a assume A: "a \<in> carrier Q\<^sub>p" "val a \<ge> 3*N"
          have 00: "\<pp>[^](3*N) = \<pp>[^](int (3*N))"
            unfolding int_pow_int by blast 
          have 0: "val (\<pp>[^](3*N)) = eint (3*N)"
              unfolding 00 val_p_int_pow by blast 
            have 1: "val a \<ge>val (\<pp>[^](3*N))"
              using A unfolding 0 by blast 
            have 2: "val (\<pp>[^](-N) \<otimes> a) \<ge>val (\<pp>[^](-N) \<otimes>\<pp>[^](3*N))"
            apply(rule R3) 
              apply blast
              using A apply blast
              by(rule 1)
            have 3: "(\<pp>[^](-N) \<otimes>\<pp>[^](3*N)) = \<pp>[^](-N + 3*N)"
              using "00" p_intpow_add by presburger
            have 4: "(\<pp>[^](-N) \<otimes>\<pp>[^](3*N)) = \<pp>[^](2*N)"
            proof-
              have a: "- int N + int (3 * N) = 2*N"
                by linarith
              show ?thesis 
                unfolding 3 a using int_pow_int 
                by metis
            qed
            show "eint (int (2*N)) \<le> val (\<pp> [^] - int N \<otimes> a)"
              using 2 unfolding 4 p_pow' by blast
        qed
        have w7: "val (\<pp>[^](-N) \<otimes>(\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>)) \<ge> 2*N"
          apply(rule R4)
           apply (meson Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.int_inc_closed c2 fract_closed p_natpow_closed(1) t_closed w3)
          by(rule w6)
        have w8: "\<pp>[^](-N)\<otimes>(\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>) = ((t \<ominus> T b x)\<div>(c2 x \<ominus> c1 x))"
          unfolding w4   apply(rule R2)
          using Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.nonzero_closed c2 nonzero_inverse_Qp t_closed w3 apply presburger
          by blast
        have w9: "val (((t \<ominus> T b x)\<div>(c2 x \<ominus> c1 x))) \<ge> 2*N"
          using w7 unfolding w8 by blast 
        have w10: "val (lb' x \<div>(c2 x \<ominus> c1 x)) = 2*N"
          unfolding w5  using p_pow' by blast
        have R5: "\<And>a b c. a \<in> carrier Q\<^sub>p\<Longrightarrow> b \<in> carrier Q\<^sub>p \<Longrightarrow> c \<in> nonzero Q\<^sub>p \<Longrightarrow> 
                      val (a \<div> c) \<ge> val (b \<div> c) \<Longrightarrow> val a \<ge> val b"
          by (metis Qp.cring_simprules(14) Qp.nonzero_memE(1) nonzero_inverse_Qp val_ineq_cancel_leq)
        show "val (lb' x) \<le> val (t \<ominus> T b x)"
          apply(rule R5[of _ _ "c2 x \<ominus> c1 x"])
          using T_closed SA_car_closed x_closed t_closed apply blast
          using lb'_closed x_closed SA_car_closed apply blast
          using w3 apply linarith
          using w9 unfolding w10 by blast 
      qed
      have p1: "(\<zero>\<^bsub>SA m\<^esub> x) = \<zero>"
        using x_closed SA_zeroE by blast
      show "t # x \<in> condition_to_set (S' b)"
        unfolding S'_def condition_to_set.simps 
        apply(rule cell_memI)
        using A unfolding \<D>_params condition_to_set.simps cell_def  a_inter Int_iff apply blast
        using A unfolding \<D>'_set \<D>'_params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd a_inter Int_iff
        apply blast
        apply(rule closed_interval_memI)
         apply(rule p0)
        unfolding p1 val_zero 
        using eint_ord_code(3) by blast
    qed
    have N_ineq: "2*N < 3*N"
      using N_def by linarith 
    have N_ineq': "2*N \<le> 3*N"
      using N_def by linarith 
    have p_mod_0: "\<And>a b. a \<in> \<O>\<^sub>p \<Longrightarrow> Qp_res a (3*N) = b \<Longrightarrow> Qp_res a (2*N) = b mod p^(2*N)"
      using N_ineq' to_Zp_closed unfolding Qp_res_def 
      by (metis val_ring_memE p_residue_alt_def p_residue_padic_int)
    have p_mod_1: "\<And>b. b \<in> carrier (Zp_res_ring (3*N)) \<Longrightarrow>  b mod p^(2*N) \<in> carrier (Zp_res_ring (2*N))"
      using mod_in_carrier by blast
    have S'_in: "\<And>t x b. b \<in> carrier (Zp_res_ring (3*N)) \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> b mod p^(2*N) \<noteq> 0 \<Longrightarrow> t#x \<in> condition_to_set (S' b)\<Longrightarrow>val ((t \<ominus> c2 x)) =  val( \<pp>[^](-N)\<otimes>[b]\<cdot>\<one> \<otimes> (c2 x \<ominus> c1 x)) \<and>val (t \<ominus> c2 x) < val (\<pp>[^](N) \<otimes> (c2 x \<ominus> c1 x)) \<and> val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) < N \<and> val (t \<ominus> c2 x) \<ge> val (\<pp>[^](-N) \<otimes> (c2 x \<ominus> c1 x)) \<and>  val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<ge> (-N) \<and> (\<pp>[^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x))) \<in> \<O>\<^sub>p \<and>
                                                                                               Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p^(2*N) \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b  "
    proof- 
      fix t x b assume A: "t#x \<in> condition_to_set (S' b)" "b \<in> carrier (Zp_res_ring (3*N))" "b \<noteq> 0" "b mod p^(2*N) \<noteq> 0 "
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using A unfolding \<D>_params condition_to_set.simps cell_def mem_Collect_eq list_hd list_tl 
        using A(1) cell_cond_head_closure by blast
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using A unfolding S'_def condition_to_set.simps cell_def mem_Collect_eq list_hd list_tl 
        by (metis Qp_pow_ConsE list_tl)
      have 0: "val (lb' x) \<le> val (t \<ominus> T b x)"
        using A unfolding S'_def condition_to_set.simps cell_def  mem_Collect_eq list_tl list_hd closed_interval_def 
        by blast 
      have 1: "c2 x \<noteq> c1 x "
        using A centers_neq'''
        unfolding S'_def condition_to_set.simps cell_def mem_Collect_eq list_hd list_tl 
        by blast 
      have c2: "c2 x \<in> carrier Q\<^sub>p"
        using c2_closed x_closed  SA_car_closed by blast
      have c1: "c1 x \<in> carrier Q\<^sub>p"
        using c1_closed x_closed  SA_car_closed by blast
      have 4: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
        unfolding nonzero_def using 1 c1 c2 
        by (smt Qp.cring_simprules(4) Qp.r_right_minus_eq mem_Collect_eq)
      have 5: "lb' x \<in> carrier Q\<^sub>p"
        using x_closed lb'_closed SA_car_closed 
        by blast
      have 6: "(t \<ominus> T b x) \<in> carrier Q\<^sub>p"
        using t_closed T_closed x_closed SA_car_closed by blast 
      have 7: "val (lb' x \<div> c2 x \<ominus> c1 x ) \<le> val (t \<ominus> T b x \<div> c2 x \<ominus> c1 x)"
        using 5 6 4 0 fract_closed local.fract_cancel_right val_ineq_cancel_leq by presburger
      have R0: "\<And> a b c. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p; c \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
              t \<ominus> (a \<oplus> (a \<ominus> b)\<otimes>c) = (t \<ominus> a) \<ominus> (a \<ominus> b)\<otimes>c"
        unfolding a_minus_def using t_closed Qp.a_ac(1) Qp.cring_simprules(1) 
          Qp.cring_simprules(20) Qp.cring_simprules(3) Qp.cring_simprules(5) by presburger
      have w0: "lb' x =  \<pp> [^] (2*N) \<otimes> (c2 x \<ominus> c1 x)"
        using lb'_eval[of x] x_closed by blast 
      have w1: "T b x = c2 x \<oplus> (c2 x \<ominus> c1 x) \<otimes> (\<pp>[^](-N) \<otimes>[b] \<cdot> \<one>)"
        using T_eval[of x b] x_closed by blast 
      have w2: "(t \<ominus> T b x) = (t \<ominus> (c2 x)) \<ominus> (c2 x \<ominus>c1 x)\<otimes>(\<pp>[^](-N) \<otimes>[b] \<cdot> \<one>)"
        unfolding w1 using R0  Qp.int_inc_closed c1 c2 
        using Qp.m_closed p_intpow_closed(1) by presburger
      have R1:  "\<And> a b c d. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> nonzero Q\<^sub>p; c \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
            ((a \<ominus> (b \<otimes> c)) \<div> b) = (a \<div> b) \<ominus> c"
        by (smt Qp.cring_simprules(24) Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.nonzero_memE(1) Qp.not_nonzero_memI Qp.r_minus_distr Qp.r_one field_inv(1) nonzero_inverse_Qp)
      have w4: "((t \<ominus> T b x)\<div>(c2 x \<ominus> c1 x)) =( (t \<ominus> (c2 x))\<div>(c2 x \<ominus> c1 x)) \<ominus> (\<pp>[^]-N \<otimes>[b] \<cdot> \<one>)"
        unfolding w2 apply(rule R1)
          using c2 t_closed apply blast
           apply(rule 4)
        using p_intpow_closed(1) by blast
      have w5: "(lb' x \<div>(c2 x \<ominus> c1 x)) = \<pp>[^](2*N)"
        unfolding w0 using 4 
        using Qp.int_inc_closed Qp.int_nat_pow_rep Qp.m_assoc Qp.m_comm 
          Qp.nonzero_closed local.fract_cancel_right nonzero_inverse_Qp 
        by metis
      have R2: "\<And> a b. \<lbrakk> a \<in> carrier Q\<^sub>p; b \<in> carrier Q\<^sub>p\<rbrakk> \<Longrightarrow> 
                \<pp>[^]-N \<otimes>  (\<pp> [^] N \<otimes> a \<ominus> b) = a \<ominus> (\<pp>[^]-N \<otimes> b)"
          
        proof -
        fix ac :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set" and bb :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"
        assume a1: "ac \<in> carrier Q\<^sub>p"
        assume a2: "bb \<in> carrier Q\<^sub>p"
        have f3: "\<forall>x0. - (x0::int) = - 1 * x0"
          by presburger
        have "- 1 * (- 1 * int N) = int N"
          by presburger
        then have "\<pp> [^] N \<otimes> ac = (ac \<div> \<pp> [^] (- 1 * int N))"
          using f3 a1 by (metis Qp.cring_simprules(14) int_pow_int p_intpow_closed(1) p_intpow_inv'')
        then have f4: "\<pp> [^] N \<otimes> ac \<ominus> bb = (ac \<ominus> \<pp> [^] (- 1 * int N) \<otimes> bb \<div> \<pp> [^] (- 1 * int N))"
          using a2 a1 Qp_int_pow_nonzero R1 p_nonzero by presburger
        have "- int N = - 1 * int N"
          by presburger
        then show "\<pp> [^] - int N \<otimes> (\<pp> [^] N \<otimes> ac \<ominus> bb) = ac \<ominus> \<pp> [^] - int N \<otimes> bb"
          using f4 a2 a1 Qp.cring_simprules(4) Qp.cring_simprules(5) Qp_int_pow_nonzero local.fract_cancel_right p_intpow_closed(1) p_nonzero by presburger
      qed
      have w6: "\<pp>[^](-N)\<otimes>(\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>) = ((t \<ominus> T b x)\<div>(c2 x \<ominus> c1 x))"
          unfolding w4   apply(rule R2)
          using Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.nonzero_closed c2 nonzero_inverse_Qp t_closed 4 apply presburger
          by blast
      have w7: "val (lb' x \<div> c2 x \<ominus> c1 x) = 2*N"
        unfolding w0 using 4 int_pow_int 
        using p_pow' w0 w5 by presburger
      have w8: "val (\<pp>[^](-N)\<otimes>(\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>)) \<ge> val (\<pp>[^](2*N))"
        using 7  unfolding p_pow' w6 w7 by blast 
      have R3: "\<And> a .  a \<in> carrier Q\<^sub>p \<Longrightarrow>  
          val (\<pp>[^](-N)\<otimes> a) \<ge> val (\<pp>[^](2*N)) \<Longrightarrow> val a \<ge> (3*N)"
      proof- 
        fix a  assume A: "a \<in> carrier Q\<^sub>p"  "val (\<pp>[^](-N)\<otimes> a) \<ge> val (\<pp>[^](2*N))"
        have 0: "val (\<pp>[^]N \<otimes> (\<pp>[^](-N)\<otimes> a)) \<ge> val (\<pp>[^]N \<otimes> \<pp>[^](2*N))"
          using A val_mult[of "\<pp>[^]N" "\<pp>[^](-N)\<otimes> a"] val_mult[of "\<pp>[^]N" "\<pp>[^](2*N)"] unfolding p_pow 
          by (metis Qp.cring_simprules(5) add_left_mono p_intpow_closed(1) p_natpow_closed(1))
        have a: "int (3 * N) = int N + int (2*N)"
          by linarith
        have 1: "(\<pp>[^]N \<otimes> \<pp>[^](2*N)) = \<pp>[^](3*N)"
          using  p_intpow_add[of N "2*N"] unfolding a
            int_pow_int[of Q\<^sub>p "\<pp>" N] int_pow_int[of Q\<^sub>p "\<pp>" "2*N"]
          by (metis (no_types, lifting) Qp.cring_simprules(6) Qp.int_mult_closed Qp.nat_pow_mult add_mult_distrib add_num_simps(2) mult_numeral_1 numeral_add)
        have 2: "\<pp> [^] N \<otimes> (\<pp> [^] - int N \<otimes> a) = a"
          using A int_pow_int[of Q\<^sub>p \<pp> N] 
          by (metis Qp.cring_simprules(14) local.fract_cancel_right p_intpow_closed(1) p_intpow_inv'' val_nonzero' val_p_int_pow)
        have 3: "val a \<ge> val (\<pp>[^](3*N))"
          using 0 unfolding 1 2 by linarith
        have 4: "val(\<pp>[^](3*N)) = 3*N"
          unfolding p_nat by blast 
         show "val a \<ge> (3*N)" using 3 unfolding 4 by blast 
      qed
      have w6: "val (\<pp> [^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) \<ominus> [b]\<cdot>\<one>) \<ge> 3*N"
        apply(rule R3)
        using "4" Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.int_inc_closed c2 fract_closed p_natpow_closed(1) t_closed apply presburger
        using w8 by blast                    
      have w7: "val ([b]\<cdot>\<one>) < 2*N"
        apply(rule val_of_nonzero_residue')
        using A val_of_nonzero_residue by blast
      have w7': "val ([b]\<cdot>\<one>) < 3*N"
        apply(rule val_of_nonzero_residue)
        using A val_of_nonzero_residue apply blast
        using A by blast 
      have w8: "(\<pp>[^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x))) \<in> carrier Q\<^sub>p"
        by (meson "4" Qp.cring_simprules(4) Qp.cring_simprules(5) c2 fract_closed p_natpow_closed(1) t_closed)
      have w9: " val (\<pp>[^] N \<otimes>( (t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x))) =  val( [b]\<cdot>\<one>)"
        using w6 w7' w8                      
        by (smt Qp.int_inc_closed eint_ord_trans notin_closed ultrametric_equal_eq ultrametric_equal_eq' val_ring_int_inc_closed val_ultrametric_noteq' val_val_ring_prod)                    
      have w10: "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
          apply(rule val_ring_memI)
        using w8 apply blast
        unfolding w9 using val_of_int_inc by blast
      have w11: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = Qp_res ([b]\<cdot>\<one>) (2*N)"
        apply(rule Qp_res_eqI')
          apply(rule w10)
        using val_ring_int_inc_closed apply blast
        apply(rule eint_ord_trans[of _ "3*N"]) 
        using N_ineq' eint_ord_simps(1) of_nat_mono apply blast
        by(rule w6)
      have w11': "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = Qp_res ([b]\<cdot>\<one>) (3*N)"
        apply(rule Qp_res_eqI')
          apply(rule w10)
        using val_ring_int_inc_closed apply blast
        apply(rule eint_ord_trans[of _ "3*N"]) 
        using N_ineq' eint_ord_simps(1) of_nat_mono apply blast
        by(rule w6)
      have w13:  "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p ^ (2 * N)"
        unfolding w11   A Qp_res_int_inc[of b "2*N"] by blast 
      have w13':  "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b "
        unfolding w11'   A Qp_res_int_inc[of b "3*N"] using A  
        by (meson p_residue_ring_car_memE(1) p_residue_ring_car_memE(2) unique_euclidean_semiring_numeral_class.mod_less)
      have R4: "\<And> a .  a \<in> carrier Q\<^sub>p \<Longrightarrow>  
          val (\<pp>[^]N \<otimes> a) \<ge> 0 \<Longrightarrow> val a \<ge> -N"
      proof- 
        fix a  assume A: "a \<in> carrier Q\<^sub>p"  "val (\<pp>[^](N)\<otimes> a) \<ge> 0"
        have "val (\<pp>[^](N)\<otimes> a) \<ge> val \<one>"
          using A unfolding val_one by blast 
        hence 0: "val (\<pp>[^]-N \<otimes> (\<pp>[^](N)\<otimes> a)) \<ge> val (\<pp>[^]-N)"
          using A val_mult[of "\<pp>[^]-N" "\<pp>[^](N)\<otimes> a"] val_mult[of "\<pp>[^]-N" "\<one>"] 
          by (meson Qp.cring_simprules(5) p_intpow_closed(1) p_natpow_closed(1) val_ring_memI val_val_ring_prod')
        have 2: "\<pp> [^] -N \<otimes> (\<pp> [^] N \<otimes> a) = a"
          using A int_pow_int[of Q\<^sub>p \<pp> N] 
          by (metis Qp.cring_simprules(14) Qp.cring_simprules(24) Qp.r_one p_intpow_closed(1) p_intpow_inv)
        have 3: "val a \<ge> val (\<pp>[^]-N)"
          using 0 unfolding 1 2 by linarith
        have 4: "val(\<pp>[^](-N)) = -N"
          using val_p_int_pow by blast
        show "val a \<ge> -N" using 3 unfolding 4 by blast 
      qed                    
      have w14: "val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<ge> (-N)"
        apply(rule R4)
        using "4" Qp.cring_simprules(4) c2 fract_closed t_closed apply blast
        using w10 val_ring_memE by blast
      have w15: "val (t \<ominus> c2 x) \<ge> val (\<pp>[^](-N) \<otimes> (c2 x \<ominus> c1 x))"
        using w14 val_p_int_pow 4 t_closed c2 
        by (metis (no_types, lifting) Qp.cring_simprules(14) Qp.cring_simprules(4) Qp.nonzero_memE(1) 
            fract_closed local.fract_cancel_right p_intpow_closed(1) val_ineq_cancel_leq')
      have R5: "\<And> a .  a \<in> carrier Q\<^sub>p \<Longrightarrow>
          val (\<pp>[^]N \<otimes> a) < 2*N \<Longrightarrow> val a < N"
      proof- 
        fix a assume A: "a \<in> carrier Q\<^sub>p" "val (\<pp>[^]N \<otimes> a) < 2*N"
        have 0: "val (\<pp>[^]N \<otimes> \<pp>[^]N) = 2*N"
          using val_mult[of "\<pp>[^]N" "\<pp>[^]N"]
          unfolding p_pow 
          using eint_nat_times_2 p_natpow_closed(1) two_times_eint by presburger
        have 1: "val (\<pp>[^]N \<otimes> a) < val (\<pp>[^]N \<otimes> \<pp>[^]N)"
          using A unfolding 0 by blast 
        have 2: "val ( a) < val (\<pp>[^]N)"
          using 1 A val_mult[of "\<pp>[^]N"]
          by (meson p_natpow_closed(1) p_natpow_closed(2) val_ineq_cancel_le)
        show "val a < N"
          using 2 unfolding p_pow by blast 
      qed
      have R6: "\<And>a . a \<in> carrier Q\<^sub>p \<Longrightarrow> 
            val (\<pp>[^]N \<otimes> a) = val ([b]\<cdot>\<one>) \<Longrightarrow> val a = val (\<pp>[^](-N) \<otimes> [b]\<cdot>\<one>)"
      proof- fix a assume a: "a \<in> carrier Q\<^sub>p" "val (\<pp>[^]N \<otimes> a) = val ([b]\<cdot>\<one>)"
        have 0: "\<pp>[^]-N \<otimes> \<pp>[^]N = \<one>"
          by (metis Qp_int_pow_nonzero angular_component_factors_x 
              angular_component_p_int_pow_factor angular_component_p_nat_pow_factor_right 
              ord_p_pow_int ord_p_pow_nat p_intpow_inv' p_natpow_closed(1) p_natpow_closed(2) p_nonzero)
        have 0: "\<pp>[^]-N \<otimes> (\<pp>[^]N \<otimes> a) = a"
          using A Qp.m_assoc[of "\<pp>[^](-N)" "\<pp>[^]N " a ] unfolding 0  
          by (metis Qp.cring_simprules(12) a(1) p_intpow_closed(1) p_natpow_closed(1))
        have 1: "val (\<pp>[^]-N \<otimes> (\<pp>[^]N \<otimes> a)) = val (\<pp>[^](-N) \<otimes> [b]\<cdot>\<one>)"
          using A Qp.int_inc_closed Qp.m_closed a(1) a(2) p_natpow_closed(1) times_p_pow_val by presburger
        show "val a = val (\<pp>[^](-N) \<otimes> [b]\<cdot>\<one>)" using 1 unfolding 0 by blast 
      qed    
      have w16: "val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) < N"
        apply(rule R5)
        using "4" Qp.cring_simprules(4) c2 fract_closed t_closed apply blast
        using w7 unfolding w9 by blast 
      have w17: "val (t \<ominus> c2 x) < val (\<pp>[^](N) \<otimes> (c2 x \<ominus> c1 x))"
        using w16 val_p_int_pow 4 t_closed c2 
        by (smt Qp.cring_simprules(14) Qp.int_mult_closed Qp.minus_closed Qp.nat_pow_closed Qp.one_closed c1 fract_closed local.fract_cancel_right p_pow val_ineq_cancel_le')
      have w18: "val ((t \<ominus> c2 x)\<div>(c2 x \<ominus> c1 x)) =  val( \<pp>[^](-N)\<otimes>[b]\<cdot>\<one>)"
        apply(rule R6)
        using "4" Qp.cring_simprules(4) c2 fract_closed t_closed apply blast
        by(rule w9)
      have w19: "val ((t \<ominus> c2 x)) =  val( \<pp>[^](-N)\<otimes>[b]\<cdot>\<one> \<otimes> (c2 x \<ominus> c1 x))"
        using w18 4 
        by (metis (no_types, lifting) Qp.cring_simprules(14) Qp.cring_simprules(4) Qp.cring_simprules(5) Qp.int_inc_closed Qp.nonzero_memE(1) c2 p_intpow_closed(1) t_closed val_mult val_nonzero val_nonzero_frac w17)
      thus "val (t \<ominus> c2 x) = val (\<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x)) \<and>
           val (t \<ominus> c2 x) < val (\<pp> [^] N \<otimes> (c2 x \<ominus> c1 x)) \<and>
           val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) < eint (int N) \<and>
           val (\<pp> [^] - int N \<otimes> (c2 x \<ominus> c1 x)) \<le> val (t \<ominus> c2 x) \<and>
            eint (- int N) \<le> val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<and>
             \<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p ^ (2 * N)
            \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b "
        using w10 w13 w13' w14 w15 w16 w17 by blast
    qed
    obtain \<phi> where \<phi>_def: "\<phi> =  (\<lambda>b::int. (\<pp>[^](-N)\<otimes>[b]\<cdot>\<one>) \<odot>\<^bsub>SA m\<^esub>(c2 \<ominus>\<^bsub>SA m\<^esub> c1))"
      by blast 
    have \<phi>_closed: "\<And>b. \<phi> b \<in> carrier (SA m)"
      unfolding \<phi>_def apply(rule SA_smult_closed)
      using c1_closed c2_closed apply blast
      using p_intpow_closed(1) by blast    
    have q10: "is_cell_condition \<D>"
      using \<D>_def Xs_def is_cell_decompE by blast  
    have q11: "is_semialgebraic m (D1 \<inter> C1)"
      apply(rule intersection_is_semialg)
      using q10 unfolding \<D>_params 
      using is_cell_conditionE''(1) apply blast
      using \<C>_def unfolding \<C>_params 
      using is_cell_conditionE''(1) 
      by metis
    obtain Rs where Rs_def: "Rs = {b \<in> carrier (Zp_res_ring (3*N)). \<exists> t x. t#x \<in> a \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b }"
      by blast 
    have Rs_mod: "\<And>b. b \<in> Rs \<Longrightarrow> b mod p^(2*N) \<noteq>0"
    proof- 
      fix b assume A: "b \<in> Rs"
      obtain t x where tx_def: " t#x \<in> a \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
        using A unfolding Rs_def mem_Collect_eq  by blast 
      have 0: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> 0"
        using tx_def  q8 by blast
      have 1: "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
        using tx_def q6 by blast
      have 2: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p^(2*N)"
        using tx_def 1  p_mod_0 by blast
      show "b mod p^(2*N) \<noteq>0" using 0 unfolding 2 by blast 
    qed
    obtain E0 where E0_def: "E0 = (\<lambda>b. {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<phi> b x) \<in> Jd (val (d1 x)) (val (d2 x))})"
      by blast
    have \<D>_cell: "is_cell_condition \<D>"
      using \<D>_def Xs_def is_cell_decompE by blast 
    have D1_semialg: "is_semialgebraic m D1"
      using \<D>_cell unfolding \<D>_params 
      using is_cell_conditionE''(1) by blast
    have C1_semialg: "is_semialgebraic m C1"
      using \<C>_def unfolding \<C>_params 
      using is_cell_conditionE''(1) by metis
    have B_semialg: "is_semialgebraic m b2"
      using \<D>0_def is_cell_conditionE 
      by (metis is_cell_conditionE'(1))
    have E0_semialg: "\<And>b. is_semialgebraic m (E0 b)"
      unfolding E0_def apply(rule cell_cond_semialg)
      using \<D>_cell is_cell_conditionE(5)
      unfolding \<D>_params apply blast
        apply(rule \<phi>_closed)
      using \<D>_cell is_cell_conditionE(3)
      unfolding \<D>_params apply blast
      using \<D>_cell is_cell_conditionE(4)
      unfolding \<D>_params by blast
    obtain E where E_def: "E = (\<lambda>b. (D1 \<inter> b2 \<inter> C1 \<inter> (E0 b)))"
      by blast 
    have E_semialg: "\<And>b. is_semialgebraic m (E b)"
      unfolding E_def apply(rule intersection_is_semialg)
       apply(rule intersection_is_semialg)
      apply(rule intersection_is_semialg)
      apply(rule D1_semialg)
        apply(rule B_semialg)
       apply(rule C1_semialg)
      by(rule E0_semialg)
    obtain \<E> where \<E>_def: "\<E> = (\<lambda> b. Cond m (E b) c2 (\<phi> b) (\<phi> b) closed_interval)"
      by blast 
    have \<E>_cell: "\<And>b. is_cell_condition (\<E> b)"
      unfolding \<E>_def apply(rule is_cell_conditionI')
          apply(rule E_semialg)
         apply(rule c2_closed)
      apply(rule \<phi>_closed)
       apply(rule \<phi>_closed)
      unfolding is_convex_condition_def by blast 
    have q12: "\<And>t x. t#x \<in> a \<Longrightarrow> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<in> Rs"
    proof- 
      fix t x assume A: "t#x \<in> a"
      have 0: "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
        using A q6 by blast
      hence 1: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<in> carrier (Zp_res_ring (3*N))"
        using Qp_res_closed by blast
      thus "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) \<in> Rs"
        unfolding Rs_def mem_Collect_eq using A by blast 
    qed
    have Rs_finite: "finite Rs"
    proof- 
      have 0: "finite (carrier (Zp_res_ring (3*N)))"
        using N_def residue_ring_card by blast 
      show ?thesis 
        apply(rule finite_subset[of _ "(carrier (Zp_res_ring (3*N)))"]) 
        unfolding Rs_def apply blast
        by(rule 0)
    qed
    have q13: "\<And>t x b. t#x \<in> a \<Longrightarrow> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b \<Longrightarrow> 
           t#x \<in> condition_to_set (\<E> b)"
    proof- fix t x b assume A: " t#x \<in> a" "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
       have 0: "b \<noteq> 0"
          using A q8' by blast
        have 1: "b \<in> carrier (Zp_res_ring (3*N))"
          using A q7' by blast
        have 2: "t#x \<in> condition_to_set (S' b)"
          apply(rule in_S')
          using A apply blast
          using A by blast 
        have 3: "val (t \<ominus> c2 x) =  val( \<pp>[^](-N)\<otimes>[b]\<cdot>\<one> \<otimes> (c2 x \<ominus> c1 x))"
          using S'_in 0 1 2 
          by (metis (mono_tags, lifting) A(1) A(2) p_mod_0 q6 q8)
        have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
          using A unfolding a_inter \<C>_params condition_to_set.simps cell_def mem_Collect_eq Int_iff
          by (metis Qp_pow_ConsE(1) list_tl)
        have 4: "\<phi> b x =  \<pp>[^](-N)\<otimes>[b]\<cdot>\<one> \<otimes> (c2 x \<ominus> c1 x)"
          unfolding \<phi>_def using x_closed  c1_closed c2_closed 
          by (metis (no_types, lifting) Qp.cring_simprules(5) Qp.int_inc_closed SA_minus_eval SA_smult_formula h_closed h_def p_intpow_closed(1))
        have 5: "val (\<phi> b x) = val (t \<ominus> c2 x)"
          unfolding 3 4 by blast 
        have 6: "x \<in> E0 b"
          unfolding E0_def mem_Collect_eq 5
          using A unfolding a_inter \<D>_params Int_iff condition_to_set.simps cell_def 
            mem_Collect_eq list_tl list_hd 
          using x_closed by blast
      show " t#x \<in> condition_to_set (\<E> b)"
        unfolding \<E>_def condition_to_set.simps apply(rule cell_memI)
        using A unfolding a_inter \<C>_params condition_to_set.simps cell_def apply blast 
        using A 6 unfolding a_inter \<C>_params \<D>'_set \<D>'_params condition_to_set.simps cell_def 
          mem_Collect_eq Int_iff list_tl E_def apply blast
        unfolding list_hd  E0_def mem_Collect_eq 5 
        apply(rule closed_interval_memI)
         apply blast
        by blast 
    qed
    have q14: "\<And>t x b. t#x \<in> condition_to_set (\<E> b) \<Longrightarrow> b \<in> Rs \<Longrightarrow> t#x \<in> condition_to_set \<C> \<Longrightarrow> 
          t#x \<in> condition_to_set \<D>" 
    proof- 
      fix t x b
      assume A: "t#x \<in> condition_to_set (\<E> b)" "b \<in> Rs" "t#x \<in> condition_to_set \<C>"
      have 1: "val (t \<ominus> c2 x) = val (\<phi> b x)"
        using A(1) unfolding \<E>_def condition_to_set.simps cell_def mem_Collect_eq  list_tl list_hd 
          closed_interval_def 
        using basic_trans_rules(24) by blast
      have 2: "x \<in> E0 b"
        using A unfolding \<E>_def condition_to_set.simps cell_def mem_Collect_eq  list_tl list_hd 
                E_def by blast 
      show " t # x \<in> condition_to_set \<D>"
        unfolding \<D>_params condition_to_set.simps
        apply(rule cell_memI) 
        using A unfolding \<E>_def condition_to_set.simps cell_def mem_Collect_eq apply blast
        using A unfolding \<E>_def condition_to_set.simps cell_def mem_Collect_eq E_def apply blast
        using 2 unfolding list_tl list_hd 1 E0_def mem_Collect_eq by blast 
    qed
    have q15: "a = condition_to_set \<C> \<inter> (\<Union> b \<in> Rs. condition_to_set (\<E> b))" 
    proof(rule equalityI')
      fix xs assume A: "xs \<in> a"
      have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        using A unfolding a_inter \<C>_params condition_to_set.simps cell_def by blast 
      obtain t x where tx_def: "xs = t#x"
        using xs_closed Qp_pow_Suc_decomp by blast  
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using xs_closed unfolding tx_def  
        by (metis Qp_pow_ConsE list_hd)
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using xs_closed unfolding tx_def 
        by (metis Qp_pow_ConsE(1) list_tl)
      obtain b where b_def: "b = Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N)"
        by blast 
      have b_closed: "b \<in> Rs"
        using A b_def q12 unfolding tx_def  by blast 
      have 0: "xs \<in>  condition_to_set (\<E> b)"
        using q13 b_def A unfolding tx_def by blast 
      show "xs \<in> condition_to_set \<C> \<inter> (\<Union>b\<in>Rs. condition_to_set (\<E> b))"
        using A 0 b_closed unfolding a_inter tx_def by blast 
    next 
      fix xs assume A: "xs \<in> condition_to_set \<C>  \<inter> (\<Union>b\<in>Rs. condition_to_set (\<E> b))"
      obtain b where b_def: "b \<in> Rs \<and> xs \<in> condition_to_set (\<E> b)"
        using A by blast 
      have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        using A unfolding \<C>_params condition_to_set.simps cell_def by blast 
      obtain t x where tx_def: "xs = t#x"
        using xs_closed Qp_pow_Suc_decomp by blast  
      have t_closed: "t \<in> carrier Q\<^sub>p"
        using xs_closed unfolding tx_def  
        by (metis Qp_pow_ConsE list_hd)
      have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
        using xs_closed unfolding tx_def 
        by (metis Qp_pow_ConsE(1) list_tl)
      have 0: "xs \<in> condition_to_set \<D>"
        unfolding tx_def apply(rule q14[of _ _ b])

        using b_def unfolding tx_def apply blast
        using b_def apply blast
        using A unfolding tx_def  by blast 
      show " xs \<in> a"
        unfolding a_inter using 0 A by blast 
    qed
    have q16: "\<exists>S. is_cell_decomp m S (\<Union> (condition_to_set ` \<E> ` Rs)) \<and>  (\<forall>\<C>\<in>S. center \<C> = c2) \<and>
      (\<forall>\<C>\<in>S. \<forall>\<C>'\<in>\<E> ` Rs. condition_to_set \<C> \<inter> condition_to_set \<C>' = {} \<or> condition_to_set \<C> \<subseteq> condition_to_set \<C>') \<and>
     (\<forall>\<C>\<in>S. u_bound \<C> = l_bound \<C>) \<and> (\<forall>\<C>\<in>S. boundary_condition \<C> = closed_interval)"
      apply(rule c_cell_finite_union_decomp[of "\<E> ` Rs" c2 m])
      using Rs_finite apply blast
      using c2_closed apply blast
      using \<E>_cell apply blast
      unfolding \<E>_def image_iff using arity.simps apply blast
      unfolding \<E>_def image_iff using center.simps apply blast
      unfolding \<E>_def image_iff using boundary_condition.simps apply blast
      unfolding \<E>_def image_iff using u_bound.simps l_bound.simps by smt 
    then obtain Ss where Ss_def: "is_cell_decomp m Ss (\<Union> (condition_to_set ` \<E> ` Rs)) \<and>  (\<forall>\<C>\<in>Ss. center \<C> = c2) \<and>
      (\<forall>\<C>\<in>Ss. \<forall>\<C>'\<in>\<E> ` Rs. condition_to_set \<C> \<inter> condition_to_set \<C>' = {} \<or> condition_to_set \<C> \<subseteq> condition_to_set \<C>') \<and>
     (\<forall>\<C>\<in>Ss. u_bound \<C> = l_bound \<C>) \<and> (\<forall>\<C>\<in>Ss. boundary_condition \<C> = closed_interval)"
      using q16 by blast 
    have q17: "condition_to_set ` Ss partitions (\<Union> b \<in> Rs. condition_to_set (\<E> b))"
      apply(rule is_cell_decompE(2)[of m] )
      using Ss_def by (metis UN_simps(10))
    have q18: "((\<inter>) (condition_to_set \<C>) ` (condition_to_set ` Ss)) partitions a"
      unfolding q15 by(rule  partition_intersect, rule q17)
    show "is_r_preparable m n 1 (fs \<union> gs) a"
      apply(rule is_r_preparable_partition[of "((\<inter>) (condition_to_set \<C>) ` (condition_to_set ` Ss))"])
      using Ss_def is_cell_decompE apply blast
      using q18 apply blast
    proof-
      fix a0 assume A: " a0 \<in> (\<inter>) (condition_to_set \<C>) ` condition_to_set ` Ss"
      show "is_r_preparable m n 1 (fs \<union> gs) a0"
      proof- 
        obtain \<H> where \<H>_def: "\<H> \<in> Ss \<and> a0 = condition_to_set \<C> \<inter> condition_to_set \<H>"
          using A by blast 
        obtain H \<psi> where \<H>_params: "\<H> = Cond m H c2 \<psi> \<psi> closed_interval"
          using \<H>_def Ss_def 
          by (metis equal_CondI padic_fields.is_cell_decompE(4) padic_fields_axioms)
        have \<H>_cell: "is_cell_condition \<H>"
          using \<H>_def Ss_def is_cell_decompE by blast 
        have H_closed: "is_semialgebraic m H"
          using \<H>_cell unfolding \<H>_params 
          using is_cell_conditionE(1) by blast
        have 1: "\<And>b. is_semialgebraic m ((E b \<inter> D1 \<inter> C1 \<inter> b2 \<inter> H))"
          apply(rule intersection_is_semialg )
           apply(rule intersection_is_semialg )
            apply(rule intersection_is_semialg )
             apply(rule intersection_is_semialg )
          using E_semialg apply blast
          using D1_semialg apply linarith
          using C1_semialg apply linarith
          using B_semialg apply blast
          using H_closed by blast
        have a0_inter: "a0 = condition_to_set \<C> \<inter> condition_to_set \<H>"
          using \<H>_def by blast                       
        obtain \<S> where \<S>_def: "\<S> = (\<lambda>b. refine_fibres_2 (S' b) ( E b \<inter> D1 \<inter> C1 \<inter> b2 \<inter> H))"
          by blast 
        have \<S>_cell: "\<And>b. is_cell_condition (\<S> b)"
          using refine_fibres_2_is_cell 1 S'_cell_cond E_semialg intersection_is_semialg 
          unfolding \<S>_def S'_def 
          by blast
        have \<S>_params: "\<And>b. \<S> b = Cond m (E b \<inter>D1 \<inter> C1 \<inter> b2 \<inter> H) (T b) lb' \<zero>\<^bsub>SA m\<^esub> closed_interval"
          unfolding \<S>_def refine_fibres_2_def  refine_fibres_def S'_def 
            arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
          by blast 
        have \<S>_sub: "\<And>b. condition_to_set (\<S> b) \<subseteq> condition_to_set (S' b)"
          unfolding \<S>_def using refine_fibres_2_subset by blast 
        have Ss_cell_decomp: "is_cell_decomp m Ss (\<Union> b \<in> Rs. condition_to_set (\<E> b))"
          using Ss_def by (metis UN_simps(10))
        have 2: "condition_to_set \<H> \<subseteq> (\<Union> b \<in> Rs. condition_to_set (\<E> b))"
          using \<H>_def Ss_cell_decomp is_cell_decomp_subset[of m Ss "(\<Union> b \<in> Rs. condition_to_set (\<E> b))" \<H>] 
          by blast 
        show "is_r_preparable m n 1 (fs \<union> gs) a0"
        proof(cases "a0 = {}")
          case True
          show ?thesis unfolding True 
            apply(rule is_r_prepared_imp_is_r_preparable)
            apply(rule empty_is_1_prepared)
            using fs1 gs1 apply blast
            using fs_nonempty apply blast
            using locale_assms by blast 
        next
          case a0_nonempty: False
          obtain \<R>s where \<R>s_def: "\<R>s = {b \<in> Rs. \<exists>t x. t#x \<in> condition_to_set \<H> \<inter> condition_to_set (\<S> b)}"
            by blast 
          have b0: "0 \<notin> Rs"
          proof 
            assume A: "0 \<in> Rs"
            obtain t x where tx_def: " t # x \<in> a \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = 0"
              using A unfolding Rs_def mem_Collect_eq  by blast 
            show False using tx_def q8' by blast 
          qed
          have p0: "a0 = (\<Union> b \<in> \<R>s. condition_to_set \<C> \<inter> condition_to_set (\<S> b)) " 
          proof(rule equalityI')
            fix xs assume xs_def: "xs \<in> a0"
            have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
              using xs_def unfolding a0_inter \<H>_params condition_to_set.simps cell_def by blast 
            obtain t x where tx_def: "xs = t#x"
              using xs_closed Qp_pow_Suc_decomp by blast  
            have t_closed: "t \<in> carrier Q\<^sub>p"
              using xs_closed unfolding tx_def  
              by (metis Qp_pow_ConsE list_hd)
            have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
              using xs_closed unfolding tx_def 
              by (metis Qp_pow_ConsE(1) list_tl)
            obtain b where b_def: "b = Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N)"
              by blast 
            have a0_sub: "a0 \<subseteq> a"
              unfolding q15 a0_inter using 2 by blast 
            have 4: "(\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) \<in> \<O>\<^sub>p"
              apply(rule q6) using xs_def a0_sub unfolding tx_def by blast 
            have b_in: "b \<in> Rs"
              unfolding Rs_def mem_Collect_eq b_def apply(rule conjI)
               apply(rule Qp_res_closed, rule 4)
              using a0_sub xs_def unfolding tx_def by blast 
            have 5: "xs \<in> condition_to_set (\<E> b)"
              unfolding tx_def
              apply(rule q13) using xs_def a0_sub unfolding tx_def apply blast
              unfolding b_def by blast 
            have 6: "condition_to_set \<H> \<inter> condition_to_set (\<E> b) \<noteq> {}"
              using xs_def 5 unfolding a0_inter by blast 
            have 7: "condition_to_set \<H> \<subseteq> condition_to_set (\<E> b)"
              using \<H>_def Ss_def b_in 6 by blast                        
            have 8: "xs \<in> condition_to_set (S' b)" 
              unfolding tx_def
              apply(rule in_S') using xs_def a0_sub unfolding tx_def  apply blast
              unfolding b_def by blast 
            have 9: "xs \<in> a"
              using xs_def a0_sub by blast 
            have 10: "xs \<in> condition_to_set \<D>"
              using 9 unfolding a_inter by blast 
            have 11: " t # x \<in> condition_to_set (\<S> b)"
              using 8 10 5 xs_def unfolding a0_inter tx_def \<S>_def condition_to_set.simps refine_fibres_2_def refine_fibres_def S'_def
                cell_def mem_Collect_eq list_tl list_hd arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
              \<H>_params Int_iff \<C>_params \<D>_params \<E>_def by blast 
            have b_in: "b \<in> \<R>s"
              unfolding \<R>s_def mem_Collect_eq  apply(rule conjI)
              using b_in apply blast 
              using xs_def 11 unfolding a0_inter tx_def by blast 
            show "xs\<in> (\<Union>b\<in>\<R>s. condition_to_set \<C> \<inter> condition_to_set (\<S> b))"
              using xs_def b_in 11 unfolding tx_def a0_inter by blast 
          next
            fix xs
            assume A: "xs \<in> (\<Union>b\<in>\<R>s. condition_to_set \<C> \<inter> condition_to_set (\<S> b))"
            show "xs \<in> a0"
              unfolding a0_inter Int_iff apply(rule conjI)
              using A apply blast
            proof-
              have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
                using A unfolding \<C>_params condition_to_set.simps cell_def by blast 
              obtain t x where tx_def: "xs = t#x"
                using xs_closed Qp_pow_Suc_decomp by blast  
              have t_closed: "t \<in> carrier Q\<^sub>p"
                using xs_closed unfolding tx_def  
                by (metis Qp_pow_ConsE list_hd)
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using xs_closed unfolding tx_def 
                by (metis Qp_pow_ConsE(1) list_tl)
              obtain b where b_def: "b \<in> \<R>s \<and> xs \<in>condition_to_set \<C> \<inter> condition_to_set (\<S> b)"
                using A by blast 
              obtain y s where sy_def: "s#y \<in> condition_to_set \<H> \<inter> condition_to_set (\<S> b)"
                using b_def unfolding \<R>s_def by blast 
              have 12: "val (lb' y) \<le> val (s \<ominus> T b y)"
                using sy_def unfolding \<S>_def refine_fibres_def refine_fibres_2_def 
                    condition_to_set.simps S'_def arity.simps fibre_set.simps
                    boundary_condition.simps u_bound.simps l_bound.simps center.simps
                    cell_def Int_iff mem_Collect_eq list_tl list_hd closed_interval_def 
                by blast 
              have s_closed: "s \<in> carrier Q\<^sub>p"
                using sy_def unfolding \<H>_params Int_iff condition_to_set.simps cell_def 
                    mem_Collect_eq  list_tl list_hd 
                using cell_cond_head_closure by blast
              have y_closed: "y \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using sy_def unfolding \<H>_params Int_iff condition_to_set.simps cell_def 
                    mem_Collect_eq  list_tl list_hd 
                by (metis Qp_pow_ConsE(1) list_tl)
              have 13: "s#y \<in> condition_to_set (S' b)"
                using sy_def unfolding \<S>_def using refine_fibres_2_subset by blast 
              have 14: "xs \<in> condition_to_set (S' b)"
                using b_def unfolding tx_def \<S>_def using refine_fibres_2_subset by blast 
              have 15: "b \<noteq> 0"
                using b0 b_def unfolding \<R>s_def by blast 
              have 16: "b \<in> carrier (Zp_res_ring (3*N))"
                using b_def unfolding \<R>s_def Rs_def mem_Collect_eq by blast 
              have 17: " val (s \<ominus> c2 y) = val (\<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 y \<ominus> c1 y))"
                using S'_in[of b s y] 13 15 16 Rs_mod b_def unfolding \<R>s_def mem_Collect_eq 
                by presburger
              have 18: "val (t \<ominus> c2 x) = val (\<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x))"          
                using S'_in[of b t x] 13 15 16 14 Rs_mod b_def unfolding tx_def \<R>s_def mem_Collect_eq 
                using S'_in by blast
              have 19: "(\<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 y \<ominus> c1 y)) = \<phi> b y"
                unfolding \<phi>_def using c2_closed c1_closed y_closed 
                by (metis (no_types, lifting) Qp.cring_simprules(5) Qp.int_inc_closed SA_minus_eval SA_smult_formula h_closed h_def p_intpow_closed(1))
              have 20: "s#y \<in> condition_to_set (\<E> b)"
                unfolding \<E>_def condition_to_set.simps
                apply(rule cell_memI)
                using sy_def unfolding \<H>_params condition_to_set.simps cell_def apply blast
                using sy_def unfolding \<S>_params condition_to_set.simps cell_def list_tl Int_iff 
                  mem_Collect_eq 
                 apply blast
                unfolding list_hd 
                using 17 unfolding 19 closed_interval_def mem_Collect_eq  
                by (metis basic_trans_rules(20) notin_closed)
              hence 21: "condition_to_set \<H> \<subseteq> condition_to_set (\<E> b)"
                using b_def unfolding \<R>s_def mem_Collect_eq 
                using sy_def \<H>_def Ss_def 
                by blast
              have \<psi>_closed: "\<psi> \<in> carrier (SA m)"
                using \<H>_cell unfolding \<H>_params using is_cell_conditionE by blast 
              have 22: "x \<in> H"
                unfolding list_tl using b_def unfolding Int_iff tx_def \<S>_params condition_to_set.simps cell_def list_tl mem_Collect_eq by blast
              then obtain c where c_def: "c = \<psi> x \<oplus> c2 x"
                by blast 
              have c_closed: "c \<in> carrier Q\<^sub>p"
                unfolding c_def  using \<psi>_closed c2_closed x_closed SA_car_closed  
                by blast 
              have 23: "c \<ominus> c2 x = \<psi> x"
                using \<psi>_closed c2_closed x_closed SA_car_closed 
                unfolding c_def a_minus_def 
                by (metis Qp.add.inv_solve_right Qp.add.m_closed)
              have 24: "c#x \<in> condition_to_set \<H>"
                unfolding \<H>_params condition_to_set.simps
                apply(rule cell_memI)
                  apply(rule Qp_pow_ConsI, rule c_closed, rule x_closed)
                unfolding list_tl apply(rule 22)
                unfolding list_hd 23 unfolding closed_interval_def mem_Collect_eq 
                by blast 
              have 25: "c#x \<in> condition_to_set (\<E> b)"
                using 24 21  by blast
              have 26: "val (c \<ominus> c2 x) = val (\<phi> b x)"
                using 25 unfolding \<E>_def condition_to_set.simps cell_def mem_Collect_eq 
                                   list_tl list_hd closed_interval_def 
                using basic_trans_rules(24) by blast
              have 27: "val (c \<ominus> c2 x) = val (\<psi> x)"
                using 24 unfolding \<H>_params condition_to_set.simps cell_def mem_Collect_eq 
                                   list_tl list_hd closed_interval_def 
                using basic_trans_rules(24) by blast
              have 28: "val (\<psi> x) = val (\<phi> b x)"
                using 26 unfolding 27 by blast 
              have 29: "val (t \<ominus> c2 x) = val (\<phi> b x)"
                using t_closed x_closed c2_closed unfolding \<phi>_def 18 
                by (metis (no_types, lifting) Qp.int_inc_closed Qp.m_closed SA_minus_eval SA_smult_formula c1_closed h_closed h_def p_intpow_closed(1))
              hence 30: "val (t \<ominus> c2 x) = val (\<psi> x)"
                unfolding 28 29 by blast 
              show "xs \<in> condition_to_set \<H>"
                unfolding tx_def \<H>_params condition_to_set.simps
                apply(rule cell_memI)
                using xs_closed unfolding tx_def apply blast
                unfolding list_tl using b_def unfolding Int_iff tx_def \<S>_params condition_to_set.simps cell_def list_tl mem_Collect_eq apply blast
                using 30 unfolding closed_interval_def mem_Collect_eq list_hd list_tl 
                by (metis basic_trans_rules(20) notin_closed)
            qed
          qed
          have p1: "\<And>b0 b1. b0 \<in> \<R>s \<Longrightarrow> b1 \<in> \<R>s \<Longrightarrow> b0 \<noteq> b1 \<Longrightarrow> 
                          (condition_to_set \<C> \<inter>  condition_to_set (\<S> b0)) \<inter> (condition_to_set \<C> \<inter>condition_to_set (\<S> b1)) = {}"
          proof- 
            fix b0 b1 assume A0: "b0 \<in> \<R>s" "b1 \<in> \<R>s" "b0 \<noteq> b1"
            have "\<And>a. a \<in>  (condition_to_set \<C> \<inter>  condition_to_set (\<S> b0)) \<inter> (condition_to_set \<C> \<inter>condition_to_set (\<S> b1)) 
  \<Longrightarrow> False"
            proof- 
              fix xs assume A1: "xs \<in>  (condition_to_set \<C> \<inter>  condition_to_set (\<S> b0)) \<inter> (condition_to_set \<C> \<inter>condition_to_set (\<S> b1))"
              have xs_closed: "xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
                using A1 unfolding \<C>_params condition_to_set.simps cell_def by blast 
              obtain t x where tx_def: "xs = t#x"
                using xs_closed Qp_pow_Suc_decomp by blast  
              have t_closed: "t \<in> carrier Q\<^sub>p"
                using xs_closed unfolding tx_def  
                by (metis Qp_pow_ConsE list_hd)
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using xs_closed unfolding tx_def 
                by (metis Qp_pow_ConsE(1) list_tl)
              have b0_neq: "b0 \<noteq> 0"
                using A0(1) unfolding \<R>s_def mem_Collect_eq 
                using b0 by blast
              have b1_neq: "b1 \<noteq> 0"
                using A0(2) unfolding \<R>s_def mem_Collect_eq 
                using b0 by blast
              have 0: " t # x \<in> condition_to_set (S' b0)"
                using A1 unfolding \<S>_def using refine_fibres_2_subset[of "S' b0"] 
                unfolding tx_def
                by blast
              have 1: " t # x \<in> condition_to_set (S' b1)"
                using A1 unfolding \<S>_def using refine_fibres_2_subset[of "S' b1"] 
                unfolding tx_def
                by blast
              have 2: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b0  "
                using 0 S'_in[of b0 t x] 1 A0(1) Rs_mod unfolding \<R>s_def Rs_def mem_Collect_eq 
                using b0_neq by presburger 
              have 3: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b1"
                using 1 S'_in[of b1 t x] 1 A0(2) Rs_mod  unfolding \<R>s_def Rs_def mem_Collect_eq 
                using b1_neq  by presburger
              show False using 2 3 A0 by blast 
            qed
            thus "condition_to_set \<C> \<inter> condition_to_set (\<S> b0) \<inter> (condition_to_set \<C> \<inter> condition_to_set (\<S> b1)) = {}"
              by blast 
          qed
          have p3: "(\<lambda> b. condition_to_set \<C> \<inter> condition_to_set (\<S> b)) ` \<R>s partitions a0"
            apply(rule is_partitionI)
             apply(rule disjointI)
            using p1 apply blast
            unfolding p0 by blast 
          show "is_r_preparable m n 1 (fs \<union> gs) a0"
            apply(rule is_r_preparable_partition[of "(\<lambda> b. condition_to_set \<C> \<inter> condition_to_set (\<S> b)) ` \<R>s"])
            using Rs_finite finite_subset[of "\<R>s" Rs]  \<R>s_def 
              apply blast
             apply(rule p3)
          proof- fix a1 assume a1_def: "a1 \<in> (\<lambda>b. condition_to_set \<C> \<inter> condition_to_set (\<S> b)) ` \<R>s"
            then obtain b where b_def: "b \<in> \<R>s \<and> a1 = condition_to_set \<C> \<inter> condition_to_set  (\<S> b)"
              by blast 
            have 0: " a1 = condition_to_set \<C> \<inter> condition_to_set  (\<S> b)"
              using b_def by blast
            obtain \<eta> where \<eta>_def: "\<eta> = (\<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one>) \<odot>\<^bsub>SA m\<^esub>(c2 \<ominus>\<^bsub>SA m\<^esub> c1)"
              by blast 
            have \<eta>_closed: "\<eta> \<in> carrier (SA m)"
              unfolding \<eta>_def using c1_closed c2_closed 
              using \<phi>_closed \<phi>_def by blast
            have \<eta>_eval: "\<And>x. x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>) \<Longrightarrow> \<eta> x = (\<pp> [^] (-N)\<otimes>[(b + p^N)]\<cdot>\<one>) \<otimes> (c2 x \<ominus> c1 x)"
              unfolding \<eta>_def using c1_closed c2_closed 
              by (metis (no_types, lifting) Qp.cring_simprules(5) Qp.int_inc_closed
                  SA_minus_eval SA_smult_formula h_closed h_def p_intpow_closed(1))
            have 1: "\<And>t x. t#x \<in> a1 \<Longrightarrow> val (t \<ominus> c1 x) = val (\<eta> x)"
            proof- 
              fix t x assume A1: "t#x \<in> a1"
              have t_closed: "t \<in> carrier Q\<^sub>p"
                using A1 unfolding 0 mem_Collect_eq condition_to_set.simps \<C>_params cell_def Int_iff list_hd 
                using cell_cond_head_closure by blast
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using A1 unfolding 0 mem_Collect_eq condition_to_set.simps \<C>_params cell_def Int_iff list_hd list_tl  
                by (metis Qp_pow_ConsE(1) list_tl)
              have a1_sub_a0: "a1 \<subseteq> a0"
                using a1_def p3 is_partitionE by blast 
              have a0_sub_a: "a0 \<subseteq> a"
                using A q18 is_partitionE by blast  
              have a1_sub_a: "a1 \<subseteq> a"
                using a1_sub_a0 a0_sub_a by blast 
              have tx_in_a: "t#x \<in> a"
                using A1 a1_sub_a by blast 
              have tx_in_S: "t#x \<in> condition_to_set (S' b)"
                using 0 A1 unfolding \<S>_def using refine_fibres_2_subset by blast 
              have b_mod: "b mod p^(2*N) \<noteq> 0"
                apply(rule Rs_mod)
                using b_def unfolding \<R>s_def mem_Collect_eq by blast 
              have b_neq_0: "b \<noteq> 0"
                using b_def unfolding \<R>s_def mem_Collect_eq 
                using b0 by blast
              have b_car: "b \<in> carrier (residue_ring (p ^ (3 * N)))"
                using b_def unfolding \<R>s_def Rs_def by blast 
              have 10: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
                using tx_in_S S'_in[of b t x] b_car b_mod b_neq_0 by blast 
              have 11: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                apply(rule Case_iv[of n N t "c1 x" "c2 x" b])
                using locale_assms apply blast
                using N_def apply blast
                using N_def apply blast
                using t_closed apply blast
                using c1_closed SA_car_closed x_closed apply blast
                using c2_closed SA_car_closed x_closed apply blast
                    apply(rule centers_neq''') 
                using tx_in_a unfolding a_inter \<D>'_set \<D>'_params Int_iff condition_to_set.simps mem_Collect_eq list_tl cell_def 
                apply blast
                using tx_in_a q4 apply blast
                using "10" apply blast
                using tx_in_a q8 apply blast
                using tx_in_a q9 by blast                              
              then obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                by blast 
              have 12: "t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                using u_def by blast 
              have 13: "val (u[^]n) = 0"
                using u_def 
                by (metis Qp.int_nat_pow_rep Qp.nat_pow_closed Qp.nat_pow_one Qp.nonzero_one_closed Qp.one_closed locale_assms equal_val_imp_equal_ord(2) finite_val_imp_nonzero int_fun_to_poly_def local.nat_power_eq p_nat transpose_alt_def val_of_power val_one val_p_int_pow val_root)
              have 14: "(c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
                using c2_closed c1_closed x_closed SA_car_closed by blast 
              have 15: "val (t \<ominus> c1 x) = val (\<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x))"
                using val_mult[of "\<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x)" "u[^]n"]
                      u_def 14
                unfolding 12 13 
                by (metis Qp.cring_simprules(5) Qp.int_inc_closed Qp.nat_pow_closed arith_simps(50) p_intpow_closed(1))
              show " val (t \<ominus> c1 x) = val (\<eta> x)"
                unfolding 15 using x_closed \<eta>_eval 
                by presburger
            qed
            have 2: "\<And>xs . xs \<in> a1 \<Longrightarrow> val ((hd xs) \<ominus> c1 (tl xs)) = val (\<eta> (tl xs))"
              apply(rule 1)
              unfolding 0 \<C>_params 
              by (metis Set.basic_monos(7) \<C>_params cell_conditon_mem_decomp inf_aci(1) inf_le1)
            obtain C2 where C2_def: "C2= C1 \<inter> {x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>). val (\<eta> x) \<in> Jc (val (r1 x)) (val (r2 x))}"
              by blast 
            have \<C>_cell: "is_cell_condition \<C>"
              using \<C>_def by blast 
            have C2_semialg: "is_semialgebraic m C2"
              unfolding C2_def apply(rule intersection_is_semialg)
               apply(rule C1_semialg)
              apply(rule cell_cond_semialg)
              using \<C>_cell is_cell_conditionE(5) unfolding  \<C>_params apply blast
                apply(rule \<eta>_closed)
              using \<C>_cell is_cell_conditionE unfolding  \<C>_params apply blast
              using \<C>_cell is_cell_conditionE(4) unfolding  \<C>_params by blast
            have a1_inter': "a1 = condition_to_set (refine_fibres_2 \<C> C2) \<inter> condition_to_set (\<S> b)"                          
              apply(rule equalityI')
              using 2 unfolding 0
              unfolding \<C>_params refine_fibres_2_def condition_to_set.simps cell_def 
                mem_Collect_eq refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                Int_iff C2_def using Qp_pow_ConsE(1) apply metis
              by blast 
            have 3: "\<And>t x. t#x \<in> condition_to_set (refine_fibres_2 (\<S> b) C2) \<Longrightarrow> val (t \<ominus> c1 x) = val (\<eta> x)"
            proof- 
              fix t x assume A1: "t#x \<in> condition_to_set (refine_fibres_2 (\<S> b) C2)"
              have t_closed: "t \<in> carrier Q\<^sub>p"
                using A1 unfolding 0 mem_Collect_eq condition_to_set.simps \<C>_params cell_def Int_iff list_hd 
                using cell_cond_head_closure by blast
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using A1 
                unfolding 0 mem_Collect_eq condition_to_set.simps \<S>_params cell_def Int_iff list_hd list_tl  
                          refine_fibres_2_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                by (metis Qp_pow_ConsE(1) list_tl)
              have tx_in_S: "t#x \<in> condition_to_set (S' b)"
                using 0 A1 unfolding \<S>_def using refine_fibres_2_subset by blast 
              have b_mod: "b mod p^(2*N) \<noteq> 0"
                apply(rule Rs_mod)
                using b_def unfolding \<R>s_def mem_Collect_eq by blast 
              have b_neq_0: "b \<noteq> 0"
                using b_def unfolding \<R>s_def mem_Collect_eq 
                using b0 by blast
              have b_car: "b \<in> carrier (residue_ring (p ^ (3 * N)))"
                using b_def unfolding \<R>s_def Rs_def by blast 
              have b_mod': "b mod p^(2*N) \<noteq> -(p^N) mod p^(2*N)"
              proof- 
                obtain t x where tx_def: "t#x \<in> a \<and>  t # x \<in> a \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
                  using b_def unfolding \<R>s_def Rs_def mem_Collect_eq by blast 
                have 0: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) \<noteq> Qp_res (\<ominus> (\<pp> [^] N)) (2 * N)"
                  using tx_def q9[of t x] by blast 
                have a: "b = Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N)"
                  using tx_def by blast 
                have b: "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
                  using tx_def q6 by blast
                have 1: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p^(2*N)"
                  unfolding a using b N_ineq'  using p_mod_0 by blast
                have 2: "Qp_res (\<ominus> (\<pp> [^] N)) (2 * N) = -(p^N) mod p^(2*N)"
                  by (metis Qp.add.int_pow_neg Qp.int_nat_pow_rep Qp.one_closed Qp_res_int_inc)
                show ?thesis using 0 1 2 by metis 
              qed
              have b_mod'': "Qp_res (\<ominus> (\<pp> [^] N)) (2 * N) = -(p^N) mod p^(2*N)"
                  by (metis Qp.add.int_pow_neg Qp.int_nat_pow_rep Qp.one_closed Qp_res_int_inc)
              have 10: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
                using tx_in_S S'_in[of b t x] b_car b_mod b_neq_0 by blast 
              have b: "val (t \<ominus> c2 x) = val (\<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x)) \<and>
val (t \<ominus> c2 x) < val (\<pp> [^] N \<otimes> (c2 x \<ominus> c1 x)) \<and>
val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) < eint (int N) \<and>
val (\<pp> [^] - int N \<otimes> (c2 x \<ominus> c1 x)) \<le> val (t \<ominus> c2 x) \<and>
eint (- int N) \<le> val (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<and>
\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p \<and>
Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (2 * N) = b mod p ^ (2 * N) \<and> Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
                by(rule S'_in[of b t x], rule b_car, rule b_neq_0, rule b_mod, rule tx_in_S)
              have 11: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = (\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) \<oplus> \<pp> [^] N"
                apply(rule equation_6[of t  "c1 x" "c2 x" N])
                   apply(rule t_closed)
                using c1_closed x_closed SA_car_closed apply blast
                using c2_closed x_closed SA_car_closed apply blast
                using centers_neq'''[of x]  A1
                unfolding refine_fibres_2_def \<S>_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                         S_def  condition_to_set.simps cell_def mem_Collect_eq list_tl by blast 
              have 12: "\<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
              proof- 
                have 0: "c1 x \<noteq> c2 x"
                  using centers_neq'''[of x]  A1
                  unfolding refine_fibres_2_def \<S>_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                         S_def  condition_to_set.simps cell_def mem_Collect_eq list_tl 
                  by blast 
                have 1: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
                  unfolding nonzero_def mem_Collect_eq 
                  using 0 c1_closed x_closed SA_car_closed  c2_closed 
                  using Qp.cring_simprules(4) Qp.r_right_minus_eq by presburger
                have 2: "(t \<ominus> c2 x) \<in> carrier Q\<^sub>p"
                  using 0 c1_closed x_closed SA_car_closed  c2_closed t_closed by blast
                have 3: "(t \<ominus> c1 x) \<in> carrier Q\<^sub>p"
                  using 0 c1_closed x_closed SA_car_closed  c2_closed t_closed by blast
                have 4: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c2 x) = \<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)"
                  by (metis 1 2 Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1))
                have 5: "(\<pp> [^] N \<div> c2 x \<ominus> c1 x) \<otimes> (t \<ominus> c1 x) = \<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x)"
                  by (metis 1 3 Qp.cring_simprules(11) Qp.cring_simprules(14) Qp.nonzero_memE(1) nonzero_inverse_Qp p_natpow_closed(1))
                have 6: "\<pp> [^] N \<in> \<O>\<^sub>p"
                  using val_ring_int_inc_closed val_ring_nat_pow_closed by blast
                have 7: "\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
                  using b by blast 
                show "\<pp> [^] N \<otimes> (t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> \<O>\<^sub>p"
                  using 11 7 6 unfolding 4 5 
                  using val_ring_add_closed by presburger
              qed
              have 13: "(t \<ominus> c1 x \<div> c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
              proof-
                have 0: "c1 x \<noteq> c2 x"
                  using centers_neq'''[of x]  A1
                  unfolding refine_fibres_2_def \<S>_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                         S_def  condition_to_set.simps cell_def mem_Collect_eq list_tl 
                  by blast 
                have 1: "c2 x \<ominus> c1 x \<in> nonzero Q\<^sub>p"
                  unfolding nonzero_def mem_Collect_eq 
                  using 0 c1_closed x_closed SA_car_closed  c2_closed 
                  using Qp.cring_simprules(4) Qp.r_right_minus_eq by presburger
                have 2: "(t \<ominus> c2 x) \<in> carrier Q\<^sub>p"
                  using 0 c1_closed x_closed SA_car_closed  c2_closed t_closed by blast
                have 3: "(t \<ominus> c1 x) \<in> carrier Q\<^sub>p"
                  using 0 c1_closed x_closed SA_car_closed  c2_closed t_closed by blast
                thus ?thesis 
                  using "1" fract_closed by blast
              qed

              have R: "\<And> a. a \<in> carrier Q\<^sub>p \<Longrightarrow> val (\<pp>[^]N \<otimes> a) \<ge> 0 \<Longrightarrow> val a \<ge> -N"
                using val_mult[of "\<pp>[^]N"] unfolding p_pow 
              proof -
                fix ac :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"
                assume a1: "ac \<in> carrier Q\<^sub>p"
                assume a2: "0 \<le> val (\<pp> [^] N \<otimes> ac)"
                have "eint 0 \<le> eint 0"
                  by blast
                then have "eint 0 \<le> 0"
                  by (metis (no_types) add.comm_neutral padic_fields.add_cancel_eint_geq padic_fields_axioms plus_eint_simps(1))
                then have "eint 0 \<le> eint (- (- int N)) + val ac"
                  using a2 a1 by (metis (no_types) eint_ord_trans minus_equation_iff p_nat p_natpow_closed(1) val_mult)
                then show "eint (- int N) \<le> val ac"
                  by (metis (no_types) ab_group_add_class.ab_left_minus padic_fields.add_cancel_eint_geq padic_fields_axioms plus_eint_simps(1))
              qed
              have 11: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                apply(rule Case_iv[of n N t "c1 x" "c2 x" b])
                using locale_assms apply blast
                using N_def apply blast
                using N_def apply blast
                using t_closed apply blast
                using c1_closed SA_car_closed x_closed apply blast
                using c2_closed SA_car_closed x_closed apply blast
                    apply(rule centers_neq''') 
                using tx_in_S unfolding S'_def condition_to_set.simps cell_def mem_Collect_eq list_tl apply blast
                apply(rule R, rule 13, rule val_ring_memE, rule 12)
                using b apply blast
                using b  b_mod apply linarith
                unfolding b_mod'' using b b_mod' by linarith
              then obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                by blast 
              have 12: "t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                using u_def by blast 
              have 13: "val (u[^]n) = 0"
                using u_def 
                by (metis Qp.int_nat_pow_rep Qp.nat_pow_closed Qp.nat_pow_one Qp.nonzero_one_closed Qp.one_closed locale_assms(7) equal_val_imp_equal_ord(2) finite_val_imp_nonzero int_fun_to_poly_def local.nat_power_eq p_nat transpose_alt_def val_of_power val_one val_p_int_pow val_root)
              have 14: "(c2 x \<ominus> c1 x) \<in> carrier Q\<^sub>p"
                using c2_closed c1_closed x_closed SA_car_closed by blast 
              have 15: "val (t \<ominus> c1 x) = val (\<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x))"
                using val_mult[of "\<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x)" "u[^]n"]
                      u_def 14
                unfolding 12 13 
                by (metis Qp.cring_simprules(5) Qp.int_inc_closed Qp.nat_pow_closed arith_simps(50) p_intpow_closed(1))
              show " val (t \<ominus> c1 x) = val (\<eta> x)"
                unfolding 15 using x_closed \<eta>_eval 
                by presburger
            qed
            have 4: "\<And>xs. xs \<in> condition_to_set (refine_fibres_2 (\<S> b) C2) \<Longrightarrow> val ((hd xs) \<ominus> c1 (tl xs)) = val (\<eta> (tl xs))"
              apply(rule 3)
              by (metis cell_conditon_mem_decomp)
            have 5: "condition_to_set (refine_fibres_2 (\<S> b) C2) \<subseteq> a1"
              apply(rule subsetI)
              unfolding 0 Int_iff 
              apply(rule conjI)
              unfolding \<C>_params condition_to_set.simps cell_def 4 mem_Collect_eq 
              unfolding refine_fibres_2_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                      S'_def \<S>_def C2_def condition_to_set.simps cell_def mem_Collect_eq Int_iff 
              apply blast
              by blast 
            have 6: "a1 \<subseteq> condition_to_set (refine_fibres_2 (\<S> b) C2)"
              apply(rule subsetI)
              unfolding a1_inter' 
              unfolding refine_fibres_2_def refine_fibres_def condition_to_set.simps cell_def Int_iff 
                mem_Collect_eq \<S>_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
              by blast
            have a1_eq: "a1 = condition_to_set (refine_fibres_2 (\<S> b) C2)"
              using 5 6 by blast 
            obtain \<Q> where \<Q>_def: "\<Q> =  (refine_fibres_2 (\<S> b) C2)"
              by blast 
            obtain F where F_def: "F = (\<lambda> f \<in> fs \<union> gs. \<Q>)"
              by blast 
            have F_im: "F ` (fs \<union> gs) = {\<Q> }"
              apply(rule equalityI)
              using fs_nonempty unfolding F_def restrict_apply 
              apply (smt image_subset_iff singleton_mem)
              using fs_nonempty UnI1 subsetI by auto
            have 7: "card (center ` {\<Q> }) = 1"
            proof- have a: "center ` {\<Q> } = {center \<Q>}"
                by blast 
              show ?thesis unfolding a 
                using is_singleton_altdef by blast
            qed
            have FE: "\<And>f. f \<in> fs \<union> gs \<Longrightarrow> F f = \<Q>"
              unfolding F_def restrict_apply 
              by meson
            have \<Q>_closed: "is_cell_condition \<Q>"
              unfolding \<Q>_def apply(rule refine_fibres_2_is_cell'[of _ m])
              using arity.simps \<S>_params apply metis 
              using \<S>_cell apply blast
              using C2_semialg by blast 
            have \<Q>_arity: "arity \<Q> = m"
              unfolding \<Q>_def 
              unfolding refine_fibres_2_def refine_fibres_def arity.simps fibre_set.simps boundary_condition.simps u_bound.simps l_bound.simps center.simps
                        \<S>_def S'_def by blast 
            have \<Q>_set: "condition_to_set \<Q> = a1"
              unfolding \<Q>_def by (simp add: a1_eq)
            have 8: "\<And> x t. t#x \<in> (condition_to_set \<Q>) \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                    "\<And> x t. t#x \<in> (condition_to_set \<Q>) \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c2 x = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
            proof- 
              fix t x assume A0: "t#x \<in> condition_to_set \<Q>"
              have A1: "t#x \<in> a1"
                using A0 unfolding \<Q>_set by blast 
              have t_closed: "t \<in> carrier Q\<^sub>p"
                using A1 unfolding 0 mem_Collect_eq condition_to_set.simps \<C>_params cell_def Int_iff list_hd 
                using cell_cond_head_closure by blast
              have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
                using A1 unfolding 0 mem_Collect_eq condition_to_set.simps \<C>_params cell_def Int_iff list_hd list_tl  
                by (metis Qp_pow_ConsE(1) list_tl)
              have a1_sub_a0: "a1 \<subseteq> a0"
                using a1_def p3 is_partitionE by blast 
              have a0_sub_a: "a0 \<subseteq> a"
                using A q18 is_partitionE by blast  
              have a1_sub_a: "a1 \<subseteq> a"
                using a1_sub_a0 a0_sub_a by blast 
              have tx_in_a: "t#x \<in> a"
                using A1 a1_sub_a by blast 
              have tx_in_S: "t#x \<in> condition_to_set (S' b)"
                using 0 A1 unfolding \<S>_def using refine_fibres_2_subset by blast 
              have b_mod: "b mod p^(2*N) \<noteq> 0"
                apply(rule Rs_mod)
                using b_def unfolding \<R>s_def mem_Collect_eq by blast 
              have b_neq_0: "b \<noteq> 0"
                using b_def unfolding \<R>s_def mem_Collect_eq 
                using b0 by blast
              have b_car: "b \<in> carrier (residue_ring (p ^ (3 * N)))"
                using b_def unfolding \<R>s_def Rs_def by blast 
              have 10: "Qp_res (\<pp> [^] N \<otimes> (t \<ominus> c2 x \<div> c2 x \<ominus> c1 x)) (3 * N) = b"
                using tx_in_S S'_in[of b t x] b_car b_mod b_neq_0 by blast 
              show 11: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c1 x = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                apply(rule Case_iv[of n N t "c1 x" "c2 x" b])
                using locale_assms apply blast
                using N_def apply blast
                using N_def apply blast
                using t_closed apply blast
                using c1_closed SA_car_closed x_closed apply blast
                using c2_closed SA_car_closed x_closed apply blast
                    apply(rule centers_neq''') 
                using tx_in_a unfolding a_inter \<D>'_set \<D>'_params Int_iff condition_to_set.simps mem_Collect_eq list_tl cell_def 
                apply blast
                using tx_in_a q4 apply blast
                using "10" apply blast
                using tx_in_a q8 apply blast
                using tx_in_a q9 by blast                              
              show 12: "\<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> t \<ominus> c2 x = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 x \<ominus> c1 x) \<otimes> u [^] n"
                apply(rule Case_iv[of n N t "c1 x" "c2 x" b])
                using locale_assms apply blast
                using N_def apply blast
                using N_def apply blast
                using t_closed apply blast
                using c1_closed SA_car_closed x_closed apply blast
                using c2_closed SA_car_closed x_closed apply blast
                    apply(rule centers_neq''') 
                using tx_in_a unfolding a_inter \<D>'_set \<D>'_params Int_iff condition_to_set.simps mem_Collect_eq list_tl cell_def 
                apply blast
                using tx_in_a q4 apply blast
                using "10" apply blast
                using tx_in_a q8 apply blast
                using tx_in_a q9 by blast                              
            qed  
            have 9: "\<And> xs. xs \<in> (condition_to_set \<Q>) \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
                    "\<And> xs. xs \<in> (condition_to_set \<Q>) \<Longrightarrow> \<exists>u\<in>carrier Q\<^sub>p. val u = 0 \<and> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
               apply(rule 8) 
               apply (metis cell_conditon_mem_decomp)
              apply(rule 8) 
              by (metis cell_conditon_mem_decomp)
            obtain u0 where u0_def: "u0 = (\<lambda> xs. if xs \<in>  (condition_to_set \<Q>) then 
                            (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n)
                                            else \<one>)"
              by blast 
            obtain u1 where u1_def: "u1 = (\<lambda> xs. if xs \<in>  (condition_to_set \<Q>) then 
                            (SOME u. u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n)
                                            else \<one>)"
              by blast 
            have u0_q: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (u0 xs)\<in>carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
            proof- fix xs assume A: "xs \<in> condition_to_set \<Q>"
              obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
                using A 9 by blast 
              show "(u0 xs)\<in>carrier Q\<^sub>p \<and> val (u0 xs) = 0 \<and> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
                apply(rule SomeE[of "(u0 xs)" _ u]) using A u0_def 
                apply presburger
                by(rule u_def)
            qed
            have u1_q: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (u1 xs)\<in>carrier Q\<^sub>p \<and> val (u1 xs) = 0 \<and> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u1 xs) [^] n"
            proof- fix xs assume A: "xs \<in> condition_to_set \<Q>"
              obtain u where u_def: "u\<in>carrier Q\<^sub>p \<and> val u = 0 \<and> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> u [^] n"
                using A 9(2)[of xs] by blast 
              show "(u1 xs)\<in>carrier Q\<^sub>p \<and> val (u1 xs) = 0 \<and> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u1 xs) [^] n"
                apply(rule SomeE[of "(u1 xs)" _ u]) using A u1_def 
                apply presburger
                by(rule u_def)
            qed
            have u0_not_q:  "\<And>xs. xs \<notin> condition_to_set \<Q> \<Longrightarrow> u0 xs = \<one>"
              using u0_def by metis 
            have u1_not_q:  "\<And>xs. xs \<notin> condition_to_set \<Q> \<Longrightarrow> u1 xs = \<one>"
              using u1_def by metis 
            have u0_closed: "u0 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
              apply(rule )
              using u0_q u0_not_q   by (metis Qp.cring_simprules(6))
            have u1_closed: "u1 \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<rightarrow> carrier Q\<^sub>p"
              apply(rule )
              using u1_q u1_not_q 
              by (metis Qp.nonzero_memE(1) Qp.nonzero_one_closed)
            have u0_val: "\<And>xs. val (u0 xs) = 0"
              using u0_q u0_not_q val_one  by metis
            have u1_val: "\<And>xs. val (u1 xs) = 0"
              using u1_q u1_not_q val_one  by metis
            have u0_eq_0: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (hd xs) \<ominus> c1 (tl xs) = \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u0 xs) [^] n"
              using u0_q by blast 
            have u1_eq_0: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (hd xs) \<ominus> c2 (tl xs) = \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs)) \<otimes> (u1 xs) [^] n"
              using u1_q by blast 
            have \<eta>_eval': "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> \<eta> (tl xs) =  \<pp> [^] - int N \<otimes> [(b + p ^ N)] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs))"
              apply(rule \<eta>_eval) using \<Q>_arity 
              using condition_to_set_memE(2) by blast
            have \<phi>_eval': "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (\<phi> b (tl xs)) =  \<pp> [^] - int N \<otimes> [b] \<cdot> \<one> \<otimes> (c2 (tl xs) \<ominus> c1 (tl xs))"
              unfolding \<phi>_def using condition_to_set_memE(2) \<Q>_arity c2_closed c1_closed  
              by (metis Qp.cring_simprules(5) Qp.int_inc_closed SA_minus_eval SA_smult_formula h_closed h_def p_intpow_closed(1))
            have \<Q>_hd_closed: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> hd xs \<in> carrier Q\<^sub>p"
              using cell_hd_closed by blast
            have \<Q>_tl_closed: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> tl xs \<in> carrier (Q\<^sub>p\<^bsup>m\<^esup>)"
              using \<Q>_arity condition_to_set_memE(2) by blast
            have \<Q>_pt_closed: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow>xs \<in> carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
              using \<Q>_arity  condition_to_set_memE(1) by blast
            have c1_prepared: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (hd xs) \<ominus> c1 (tl xs) =((hd xs) \<ominus> center \<Q> (tl xs))[^](0::nat)\<otimes> \<eta> (tl xs) \<otimes> (u0 xs) [^] n"
              using \<Q>_hd_closed \<Q>_tl_closed \<Q>_pt_closed c1_closed c2_closed u0_closed unfolding u0_eq_0 \<eta>_eval' 
              by (metis Qp.cring_simprules(12) Qp.nat_pow_0 SA_car_closed \<eta>_closed \<eta>_eval')
            have c2_prepared: "\<And>xs. xs \<in> condition_to_set \<Q> \<Longrightarrow> (hd xs) \<ominus> c2 (tl xs) =((hd xs) \<ominus> center \<Q> (tl xs))[^](0::nat)\<otimes> \<phi> b (tl xs) \<otimes> (u1 xs) [^] n"
              using \<Q>_hd_closed \<Q>_tl_closed \<Q>_pt_closed c1_closed c2_closed u1_closed unfolding u1_eq_0 \<phi>_eval' 
              by (metis Qp.cring_simprules(12) Qp.nat_pow_0 SA_car_closed \<phi>_closed \<phi>_eval')
            show "is_r_preparable m n 1 (fs \<union> gs) a1"
              unfolding a1_eq 
              apply(rule is_r_prepared_imp_is_r_preparable)
              apply(rule is_r_preparedI[of _ _ F "F ` (fs \<union> gs)"] )
              using fs1 gs1 apply blast
              using locale_assms apply blast
              apply blast
              unfolding F_im 7  apply blast
              unfolding FE apply(rule \<Q>_closed)
                apply(rule \<Q>_arity)
            proof- 
              fix l assume A0: "l \<in> fs \<union> gs"
              have a1_sub_a0: "a1 \<subseteq> a0"
                using a1_def p3 is_partitionE by blast 
              have a0_sub_a: "a0 \<subseteq> a"
                using A q18 is_partitionE by blast   
              have a1_sub_a: "a1 \<subseteq> a"
                using a1_sub_a0 a0_sub_a by blast  
              have center_closed: "center \<Q> \<in> carrier (SA m)"
                using condition_decomp'[of \<Q>] \<Q>_closed \<Q>_arity 
                by (metis is_cell_conditionE(2))
              show "\<exists>u h k. SA_poly_factors p m n l (center \<Q>) (condition_to_set \<Q>) u h k"
              proof(cases "l \<in> fs")
                case l_in_fs: True
                have T0:"a \<subseteq> B13"
                   using local.P_def by blast
                have T1: "B13 \<subseteq> condition_to_set (F3 l)"
                  using l_in_fs K_def helper K_inter by blast 
                have T2: "condition_to_set (F3 l) \<subseteq> condition_to_set (\<B>1 l)"
                  using F3_def l_in_fs F3_sub by blast
                have T3: "condition_to_set (\<B>1 l) \<subseteq> condition_to_set (\<C>\<^sub>1 l)"
                  using l_in_fs \<B>1_def refine_fibres_2_subset by metis  
                have T4: "\<exists>u h k. SA_poly_factors p m n l c1 (condition_to_set (\<C>\<^sub>1 l)) u h k"
                  using fs_defs(6)[of l] l_in_fs fs_defs(3) by metis 
                have T5: "condition_to_set \<Q> \<subseteq> condition_to_set (\<C>\<^sub>1 l)"
                  unfolding \<Q>_set using T0 T1 T2 T3 a1_sub_a by blast  
                have T6: "\<exists>u h k. SA_poly_factors p m n l c1 (condition_to_set \<Q>) u h k"
                  using T4 T5 SA_poly_factors_subset by blast 
                show T7: "\<exists>u h k. SA_poly_factors p m n l (center \<Q>) (condition_to_set \<Q>) u h k"
                  apply(rule SA_poly_factors_change_of_center[of _ _ _ c1  "condition_to_set \<Q>" "center \<Q>" \<eta> u0 0  ])
                  using T6 apply blast
                  using center_closed apply blast
                  using \<eta>_closed apply blast
                  using u0_closed apply blast
                  using c1_prepared list_tl list_hd 
                  by (metis u0_val)
              next
                case False
                have l_in_gs: "l \<in> gs"
                  using A0 False by blast 
                have T0:"a \<subseteq> B2"
                  using local.P_def Ps_def Xs_def is_cell_decomp_subset[of m Xs "B2 - B21"]
                        B21_def a_neq by blast 
                have T1: "B2 \<subseteq> condition_to_set (\<B>2 l)"
                  using B2_def l_in_gs by blast  
                have T3: "condition_to_set (\<B>2 l) \<subseteq> condition_to_set (\<C>\<^sub>2 l)"
                  using l_in_gs \<B>2_def refine_fibres_2_subset by metis  
                have T4: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set (\<C>\<^sub>2 l)) u h k"
                  using gs_defs(6)[of l] l_in_gs gs_defs(3) by metis 
                have T5: "condition_to_set \<Q> \<subseteq> condition_to_set (\<C>\<^sub>2 l)"
                  unfolding \<Q>_set using T0 T1 T3 a1_sub_a by blast  
                have T6: "\<exists>u h k. SA_poly_factors p m n l c2 (condition_to_set \<Q>) u h k"
                  using T4 T5 SA_poly_factors_subset by blast 
                show T7: "\<exists>u h k. SA_poly_factors p m n l (center \<Q>) (condition_to_set \<Q>) u h k"
                  apply(rule SA_poly_factors_change_of_center[of _ _ _ c2  "condition_to_set \<Q>" "center \<Q>" "\<phi> b" u1 0  ])
                  using T6 apply blast
                  using center_closed apply blast
                  using \<phi>_closed apply blast
                  using u1_closed apply blast
                  using c2_prepared list_tl list_hd 
                  by (metis u1_val)
              qed
            next 
              have 00: "(\<Inter>f\<in>fs \<union> gs. condition_to_set (F f)) = condition_to_set \<Q>"
                using FE fs_nonempty by blast 
              show " condition_to_set (refine_fibres_2 (\<S> b) C2) = (\<Inter>f\<in>fs \<union> gs. condition_to_set (F f))"
                unfolding \<Q>_def 00 by blast 
            qed
          qed
        qed
      qed
    qed
  qed
qed


(**************************************************************************************************)
(**************************************************************************************************)

section\<open>The Final Theorem\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma second_piece:
"is_r_preparable m n 1 (fs \<union> gs) (B1 \<inter> B2)"
  apply(rule is_r_preparable_partition[of "{B11 \<inter> B2, B12 \<inter> B2, B13 \<inter> B2}"], 
        blast, rule B1_Int_B2_partition)
  using bottom_cut_is_preparable top_cut_is_preparable middle_cut_is_preparable
  by auto 

lemma final:
"is_r_preparable m n 1 (fs \<union> gs) (A' \<inter> B')"
proof- 
  have "is_r_preparable m n 1 (fs \<union> gs) (A \<inter> B)"
  apply(rule is_r_preparable_partition[of "{A1 \<inter> A2, B1 \<inter> B2}"], blast, 
        rule is_partitionI, rule disjointI)
    using 1 apply blast
    using 0 apply blast
    using first_piece second_piece by auto 
  thus ?thesis unfolding A_def B_def by auto 
qed
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Finishing the Proof of $II_{d+1}$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Having shown how to prove that a $2$-preparable set must be $1$-preparable, there is a simple 
inductive argument to finally pass from the $r$-preparable case to the $1$-preparable case, which wil\<close>
context common_decomp_proof_context 
begin

lemma is_2_prepared_reduce: 
  assumes "fs \<subseteq> carrier (UP (SA m))"
  assumes "\<And>f. f \<in> fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "gs \<subseteq> carrier (UP (SA m))"
  assumes "\<And>g. g \<in> gs \<Longrightarrow> deg (SA m) g \<le> Suc d"
  assumes "n > 0" 
  assumes "is_r_prepared m n 1 fs A"
  assumes "is_r_prepared m n 1 gs B"
  assumes "fs \<inter> gs = {}"
  shows "is_r_preparable m n 1 (fs \<union> gs) (A \<inter> B)"
proof(cases "fs = {}")
  case True
  then have T0: "A = UNIV"
    using is_r_preparedE[of m n 1 fs A]
    using True assms(6) by auto
  show ?thesis unfolding True T0 
    using assms(7) is_r_prepared_imp_is_r_preparable by auto
next
  case False
  have fs_nonempty: "fs \<noteq> {}"
    using False by blast 
  show ?thesis
  proof(cases "gs = {}")
    case True
    then have T0: "B = UNIV"
      using is_r_preparedE[of m n 1 gs B] assms(7) by auto
    show ?thesis unfolding True T0 using assms(8) 
      using assms(6) is_r_prepared_imp_is_r_preparable by auto
  next
    case F: False
    interpret two_preparable_to_one_preparable_reduction _ _ _ _ _ _ _ _ _  A B
         apply(intro two_preparable_to_one_preparable_reduction.intro
                      two_preparable_to_one_preparable_reduction_axioms.intro)
      apply (simp add: common_decomp_proof_context_axioms)
      apply (simp add: denef_I)
      using assms F False
      unfolding Z\<^sub>p_def Q\<^sub>p_def \<iota>_def by auto 
    show ?thesis using final by auto 
  qed
qed

lemma is_r_prepared_mono:
  assumes "is_r_prepared m n r Fs A"
  assumes "k \<ge> r"
  shows "is_r_prepared m n k Fs A"
proof-
  obtain \<C> Cs where defs: " \<C> \<in> Fs \<rightarrow> Cs \<and>
       card (center ` \<C> ` Fs) \<le> r \<and>
       A = (\<Inter>f\<in>Fs. condition_to_set (\<C> f)) \<and>
       (\<forall>f\<in>Fs. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
    using assms is_r_preparedE[of m n r Fs A] by blast 
  show "is_r_prepared m n k Fs A"
    apply(rule is_r_preparedI[of _ _ \<C> Cs])
    using assms is_r_preparedE apply blast
    using assms is_r_preparedE apply blast
    using defs apply blast
    using defs assms apply linarith
    using defs apply blast
    using defs apply blast
    using defs apply blast
    using defs by blast
qed

lemma is_r_preparable_mono:
  assumes "is_r_preparable m n r Fs A"
  assumes "k \<ge> r"
  shows "is_r_preparable m n k Fs A"
  unfolding is_r_preparable_def using assms is_r_prepared_mono 
  by (meson is_r_preparable_def)

lemma is_r_prepared_reduce: 
  assumes "is_r_prepared m n (Suc (Suc r)) Fs A"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "n > 0" 
  shows "is_r_preparable m n (Suc r) Fs A"
proof- 
  obtain \<C> Cs where defs: "\<C> \<in> Fs \<rightarrow> Cs \<and>
       card (center ` \<C> ` Fs) \<le> Suc (Suc r) \<and>
       A = (\<Inter>f\<in>Fs. condition_to_set (\<C> f)) \<and>
       (\<forall>f\<in>Fs. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
    using assms is_r_preparedE[of m n "Suc (Suc r)" Fs A] assms by blast 
  show ?thesis 
  proof(cases "card (center ` \<C> ` Fs) \<le> (Suc r)")
    case True
    show ?thesis 
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _ \<C> Cs])
             apply(rule is_r_preparedE[of m n "Suc (Suc r)" Fs A], rule assms)
             apply(rule is_r_preparedE[of m n "Suc (Suc r)" Fs A], rule assms)
      using defs apply blast
      using True apply blast
      using defs apply blast
      using defs apply blast
      using defs apply blast
      using defs by blast
  next
    case False
    have Fs_finite: "finite Fs"
      by(rule is_r_preparedE[of m n "Suc (Suc r)" Fs A], rule assms)
    then have F0: "card (center ` \<C> ` Fs) = Suc (Suc r)"
      using defs False  by linarith 
    have F1: "card Fs \<ge> card ( \<C> ` Fs)"
      using Fs_finite card_image_le by blast
    have F2: "card ( \<C> ` Fs) \<ge> card (center ` \<C> ` Fs)"
      using Fs_finite card_image_le by blast
    have F3: "card Fs \<ge>Suc (Suc r)"
      using F1 F2 Fs_finite F0 by linarith
    have Fs_nonempty: "Fs \<noteq> {}"
      using F3 
      by (meson card_le_Suc_iff empty_not_insert)
    have R: "\<And>A n f. finite A \<Longrightarrow> f \<in> A \<Longrightarrow> card A = Suc n \<Longrightarrow> card (A - {f}) = n"
      by (metis card_Diff_singleton diff_Suc_1)
    obtain c1 where c1_def: "c1 \<in> center ` \<C> ` Fs"
      using F0 card_le_Suc_iff  
      by (metis insertI1 le_refl)
    have card_centers: "card ((center ` \<C> ` Fs) - {c1}) = Suc r"
      using R[of "center ` \<C> ` Fs" c1 "Suc r"] c1_def Fs_finite F0 by blast 
    obtain c2 where c2_def: "c2 \<in> center ` \<C> ` Fs - {c1}"
      using card_centers  card_le_Suc_iff
      by (metis insertI1 le_refl)
    have card_centers': "card ((center ` \<C> ` Fs) - {c1, c2}) = r"
      using R[of "center ` \<C> ` Fs - {c1}" c2 r] c2_def Fs_finite card_centers 
      by (metis Diff_insert2 finite.intros(1) finite.intros(2) finite_Diff2 finite_imageI)
    obtain fs where fs_def: "fs = {f \<in> Fs. center (\<C> f) = c1}"
      by blast
    obtain gs where gs_def: "gs = {g \<in> Fs. center (\<C> g) = c2}"
      by blast 
    obtain hs where hs_def: "hs = Fs - fs - gs"
      by blast 
    obtain ds where ds_def: "ds= center ` \<C> ` Fs"
      by blast 
    obtain B where B_def: "B = (\<Inter> f \<in> fs. condition_to_set (\<C> f))"
      by blast 
    obtain C where C_def: "C = (\<Inter> g \<in> gs. condition_to_set (\<C> g))"
      by blast 
    have centers_fs: "(center ` \<C> ` fs) = {c1}"
      apply(rule equalityI')
      unfolding fs_def apply blast
      unfolding fs_def using c1_def by blast 
    have F4: "is_r_prepared m n 1 fs B"
      apply(rule is_r_preparedI[of _ _ \<C> "\<C> ` fs"])
      using Fs_finite fs_def  apply (metis (no_types) Collect_mem_eq Fs_finite finite_Collect_conjI fs_def)
      using assms is_r_preparedE fs_def apply blast
           apply blast
      unfolding centers_fs apply simp
      using defs fs_def apply blast
      using defs fs_def apply blast
      using defs fs_def apply blast
      unfolding B_def by blast 
    have centers_gs: "(center ` \<C> ` gs) = {c2}"
      apply(rule equalityI')
      unfolding gs_def apply blast
      unfolding gs_def using c2_def by blast 
    have F5: "is_r_prepared m n 1 gs C"
      apply(rule is_r_preparedI[of _ _ \<C> "\<C> ` gs"])
      using Fs_finite gs_def  apply (metis (no_types) Collect_mem_eq Fs_finite finite_Collect_conjI gs_def)
      using assms is_r_preparedE gs_def apply blast
           apply blast
      unfolding centers_gs apply simp
      using defs gs_def apply blast
      using defs gs_def apply blast
      using defs gs_def apply blast
      unfolding C_def by blast 
    have F6: "is_r_preparable m n 1 (fs \<union> gs) (B \<inter> C)"
    proof(cases "c1 = c2")
      case True
      have T0: "fs = gs"
        unfolding fs_def gs_def True by blast 
      have T1: "B  = C"
        unfolding B_def C_def T0 by blast 
      show ?thesis 
        using F5 unfolding T0 T1 
        by (simp add: is_r_prepared_imp_is_r_preparable)
    next
      case False
      show ?thesis 
      apply(rule is_2_prepared_reduce[of ])
      using assms is_r_preparedE fs_def apply blast
      using assms fs_def apply blast
      using assms is_r_preparedE gs_def apply blast
      using assms gs_def apply blast
      using assms apply blast
        apply(rule F4, rule F5)
      using fs_def gs_def False by blast
    qed
    have F7: "(center ` \<C> ` hs) = (center ` \<C> `Fs) - {c1, c2}"
      apply(rule equalityI')
      unfolding hs_def fs_def gs_def apply blast
      using c1_def c2_def by blast
    have F8: "card (center ` \<C> ` hs) = r"
      unfolding F7 card_centers' by blast  
    have F9: "is_r_preparable m n r hs (\<Inter> h \<in> hs. condition_to_set (\<C> h))"
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _ \<C> "\<C> ` hs"])
      using hs_def Fs_finite apply blast
      using hs_def assms is_r_preparedE apply blast
      apply blast
      unfolding F8 apply blast
      using defs hs_def apply blast
      using defs hs_def apply blast
      using defs hs_def apply blast
      by blast
    have F10: "A = (\<Inter>f\<in>Fs. condition_to_set (\<C> f))"
      using defs by blast 
    have F11: "A = (B \<inter> C) \<inter> (\<Inter> h \<in> hs. condition_to_set (\<C> h))"
      unfolding B_def C_def F10 fs_def gs_def hs_def 
      by blast 
    have F12: "Fs = fs \<union> gs \<union> hs"
      unfolding fs_def gs_def hs_def by blast 
    have "is_r_preparable m n (1 + r) Fs A"
    proof(cases "hs = {}")
      case True
      have T0: "(B \<inter> C \<inter> (\<Inter>h\<in>{}. condition_to_set (\<C> h))) = B \<inter> C"
        by blast 
      have T1: "fs \<union> gs \<union> {} = fs \<union> gs"
        by blast 
      show ?thesis 
        apply(rule is_r_preparable_mono[of m n 1])
        unfolding F12 True F11 T0 T1 using F6 apply blast
        by linarith 
    next
      case False
      show ?thesis 
      unfolding F11 F12 
      apply(rule is_r_preparable_intersect, rule F6)
      using fs_def c1_def apply blast
        apply(rule F9, rule False)
      unfolding hs_def by blast 
    qed
    thus "is_r_preparable m n (Suc r) Fs A"
      by auto
  qed
qed

lemma is_r_preparable_reduce: 
  assumes "is_r_preparable m n (Suc (Suc r)) Fs A"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "n > 0" 
  shows "is_r_preparable m n (Suc r) Fs A"
proof- 
  obtain Ps where Ps_def: "finite Ps \<and> Ps partitions A \<and> (\<forall>S\<in>Ps. is_r_prepared m n (Suc (Suc r)) Fs S)"
    using is_r_preparable_def[of m n "Suc (Suc r)" Fs A] assms by blast 
  show ?thesis 
    apply(rule is_r_preparable_partition[of Ps])
    using Ps_def apply blast
    using Ps_def apply blast
    apply(rule is_r_prepared_reduce[of ])
    using Ps_def apply blast
    using assms apply blast
    by(rule assms)
qed

definition family_intersect where
"family_intersect parts = atoms_of (\<Union> parts)"

lemma family_intersect_partitions:
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> Ps partitions A"
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> finite Ps"
  assumes "finite parts"
  assumes "parts \<noteq> {}"
  shows "family_intersect parts partitions A"
proof(rule is_partitionI)
  show "disjoint (family_intersect parts)"
    apply(rule disjointI)
    unfolding family_intersect_def apply(rule atoms_of_disjoint)
    apply blast
    apply blast
    by blast 
  show " \<Union> (family_intersect parts) = A"
  proof- 
    have 0: "\<Union> (family_intersect parts) = \<Union> (\<Union> parts)"
      unfolding family_intersect_def 
      apply(rule atoms_of_covers)
      by blast 
    have 1: "\<And>Ps. Ps \<in> parts \<Longrightarrow> \<Union>Ps = A"
      by(rule is_partitionE, rule assms, blast)
    show ?thesis unfolding 0 
      using 1 assms by blast 
  qed
qed

lemma family_intersect_memE: 
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> Ps partitions A"
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> finite Ps"
  assumes "finite parts"
  assumes "parts \<noteq> {}"
  shows "\<And>Ps a. a \<in> family_intersect parts \<Longrightarrow> Ps \<in> parts \<Longrightarrow> \<exists>P \<in> Ps. a \<subseteq> P"
proof- 
  fix Ps a assume A: "a \<in> family_intersect parts" "Ps \<in> parts"
  have 0: "\<Union> Ps = A"
    apply(rule is_partitionE)
    using A assms by blast 
  have 1: "\<Union> (family_intersect parts) = A"
    apply(rule is_partitionE)
    using family_intersect_partitions assms by blast 
  have 2: "a \<noteq> {}"
    using A unfolding family_intersect_def  atoms_of_def by blast 
  obtain P where P_def: "P \<in> Ps \<and> a \<inter> P \<noteq> {}"
    using 0 1 A 2 by blast 
  have P_in: "P \<in> (\<Union> parts)"
    using P_def A by blast 
  have a_sub: "a \<subseteq> P"
    using atoms_are_minimal P_def A P_in unfolding family_intersect_def by blast 
  show "\<exists>P \<in> Ps. a \<subseteq> P"
    using a_sub P_def by blast 
qed

lemma distinct_atoms:
  assumes "Cs \<noteq> {}"
  assumes "a \<in> atoms_of Cs"
  assumes "b \<in> atoms_of Cs"
  assumes "a \<noteq> b"
  shows "(\<exists>B \<in> Cs. b \<subseteq> B \<and> a \<inter> B = {}) \<or> (\<exists>A \<in> Cs. a \<subseteq> A \<and> b \<inter> A = {})"
proof- 
  have a_nonempty: "a \<noteq> {}"
    using assms atoms_nonempty by blast 
  have b_nonempty: "b \<noteq> {}"
    using assms atoms_nonempty by blast 
  have disj: "a \<inter> b = {}"
    apply(rule atoms_of_disjoint[of _ Cs])
    using assms apply blast
    using assms apply blast
    using assms by blast 
  obtain As where As_def: "As \<subseteq> Cs \<and> a = subset_to_atom Cs As"
    using assms unfolding atoms_of_def by blast 
  obtain Bs where Bs_def: "Bs \<subseteq> Cs \<and> b = subset_to_atom Cs Bs"
    using assms unfolding atoms_of_def by blast
  have As_neq_Bs : "As \<noteq> Bs"
    using As_def Bs_def assms by blast 
  show ?thesis
  proof(cases "As \<subseteq> Bs")
    case True
    then obtain B where B_def: "B \<in> Bs - As"
      using As_neq_Bs by blast 
    have T0: "B \<in> Cs - As"
      using B_def Bs_def unfolding subset_to_atom_def by blast 
    have T1: "\<not> a \<subseteq> B"
      using As_def T0 unfolding subset_to_atom_def 
      using a_nonempty by blast
    have T2: "a \<inter> B = {}"
      using T1 atoms_are_minimal assms T0 
      by blast
    have T3: "b \<subseteq> B"
      using B_def Bs_def unfolding subset_to_atom_def by blast 
    show ?thesis using B_def T0 T1 T2 T3 by blast 
  next
    case False
    then obtain A where A_def: "A \<in> As - Bs"
      using As_neq_Bs by blast 
    have T0: "A \<in> Cs - Bs"
      using A_def As_def unfolding subset_to_atom_def by blast 
    have T1: "\<not> b \<subseteq> A"
      using Bs_def T0 unfolding subset_to_atom_def 
      using b_nonempty by blast
    have T2: "b \<inter> A = {}"
      using T1 atoms_are_minimal assms T0 by blast 
    have T3: "a \<subseteq> A"
      using A_def As_def unfolding subset_to_atom_def by blast 
    show ?thesis using A_def T0 T1 T2 T3 by blast 
  qed
qed

lemma family_intersect_mem_inter: 
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> Ps partitions A"
  assumes "\<And>Ps. Ps \<in> parts \<Longrightarrow> finite Ps"
  assumes "finite parts"
  assumes "parts \<noteq> {}"
  assumes "a \<in> family_intersect parts"
  shows "\<exists>f. \<forall> Ps \<in> parts. f Ps \<in> Ps \<and> a = (\<Inter> Ps \<in> parts. f Ps)"
proof- 
  obtain f where f_def: "f = (\<lambda>Ps \<in> parts. (SOME P. P \<in> Ps \<and> a \<subseteq> P))"
    by blast 
  have f_eval: "\<And>Ps. Ps \<in> parts \<Longrightarrow> f Ps \<in> Ps \<and> a \<subseteq> (f Ps)"
  proof- 
    fix Ps assume A: "Ps \<in> parts"
    obtain P where P_def: "P \<in> Ps \<and> a \<subseteq> P"
      using assms family_intersect_memE A by blast 
    show " f Ps \<in> Ps \<and> a \<subseteq> f Ps"
      apply(rule SomeE[of _ _ P])
      unfolding f_def restrict_apply apply (meson A)
      by(rule P_def)
  qed
  have 0: "a \<noteq> {}"
    using assms unfolding family_intersect_def 
    using atoms_nonempty by blast
  have 1: "a = (\<Inter> Ps \<in> parts. f Ps)"
  proof(rule equalityI)
    show 10: "a \<subseteq> \<Inter> (f ` parts)"
      using f_eval by blast 
    show "\<Inter> (f ` parts) \<subseteq> a"
    proof
      fix x assume A: "x \<in> \<Inter> (f ` parts)"
      obtain b where B0_def: "b = point_to_atom (\<Union> parts) x"
        by blast 
      have b_atom: "b \<in> atoms_of (\<Union> parts)"
        unfolding B0_def apply(rule point_to_atom_closed)
        using A f_eval assms by blast
      show x_in_a: "x \<in> a"
      proof(rule ccontr)
        assume "x \<notin> a"
        then have "\<not> b \<subseteq> a"
          using B0_def unfolding point_to_atom_def  point_to_type_def  subset_to_atom_def by blast
        hence p0: "a \<noteq> b"
          by blast 
        have p1: "b \<inter> a = {}"
          apply(rule atoms_of_disjoint[of _ "(\<Union> parts)"] ) 
            apply(rule b_atom)
          using assms unfolding family_intersect_def apply blast
          using p0 by blast 
        have p2: " (\<exists>B\<in>\<Union> parts. b \<subseteq> B \<and> a \<inter> B = {}) \<or> (\<exists>A\<in>\<Union> parts. a \<subseteq> A \<and> b \<inter> A = {})"
          using distinct_atoms[of "\<Union> parts" a b] assms 
          by (metis Sup_bot_conv(1) b_atom equalityI' f_eval family_intersect_def mem_simps(2) p0)
        show False 
        proof(cases "(\<exists>B\<in>\<Union> parts. b \<subseteq> B \<and> a \<inter> B = {})")
          case True
          then obtain B where B_def: "B\<in>\<Union> parts \<and> b \<subseteq> B \<and> a \<inter> B = {}"
            by blast 
          obtain Ps where Ps_def: "B \<in> Ps \<and> Ps \<in> parts"
            using B_def by blast 
          have B_neq: "B \<noteq> f Ps"
            using Ps_def B_def 10 0 by blast 
          have B_cap: "B \<inter> f Ps = {}"
            apply(rule disjointE[of Ps])
               apply(rule is_partitionE[of Ps A])
            using Ps_def assms apply blast
            using Ps_def apply blast
            using f_eval Ps_def apply blast
            by(rule B_neq)
          have b_cap: "b \<inter> f Ps = {}"
            using B_cap B_def by blast 
          have x_in_b: "x \<in> b"
            using B0_def unfolding point_to_atom_def point_to_type_def subset_to_atom_def 
            by blast  
          show False using x_in_b b_cap Ps_def A by blast 
        next
          case False
          then obtain B where B_def: "B\<in>\<Union> parts \<and> a \<subseteq> B \<and> b \<inter> B = {}"
            using p2 by blast 
          obtain Ps where Ps_def: "B \<in> Ps \<and> Ps \<in> parts" 
            using B_def by blast 
          have F0: "B = f Ps"
          proof(rule ccontr)
            assume not: "B \<noteq> f Ps"
            have F0: "B \<inter> f Ps = {}"
             apply(rule disjointE[of Ps])
               apply(rule is_partitionE[of Ps A])
            using Ps_def assms apply blast
            using Ps_def apply blast
            using f_eval Ps_def apply blast
            by(rule not)
            have a_sub: "a \<subseteq> f Ps"
              using 10 Ps_def by blast 
            show False using F0 B_def a_sub 0  by blast 
          qed
          have x_in_B: "x \<in> B"
            unfolding F0 using A Ps_def by blast 
          have x_in_b: "x \<in> b"
            using B0_def unfolding point_to_atom_def point_to_type_def subset_to_atom_def 
            by blast  
          show False using x_in_b x_in_B B_def by blast 
        qed
      qed
    qed
  qed
  show ?thesis using f_eval 1 by blast 
qed

lemma Qp_is_r_preparable: 
  assumes "n > 0"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "Fs \<subseteq> carrier (UP (SA m))"
  assumes "finite Fs"
  assumes "Fs \<noteq> {}"
  shows "is_r_preparable m n (card Fs) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
proof- 
  have 0: "\<And>f. f \<in> Fs \<Longrightarrow> is_r_preparable m n 1 {f} (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    apply(rule is_1_preparable_singelton[of ])
    using assms apply blast
    using assms apply blast by(rule assms)
  obtain cd where cd_def: "cd = card Fs"
    by blast 
  obtain Ps where Ps_def: "Ps = (\<lambda>f. (SOME Ps. finite Ps \<and> Ps partitions (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and> 
                                                (\<forall>S\<in>Ps. is_r_prepared m n 1 {f} S)))"
    by blast 
  have PsE: "\<And>f. f \<in> Fs \<Longrightarrow> finite (Ps f) \<and> (Ps f)  partitions (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
                                     (\<forall>S\<in>(Ps f) . is_r_prepared m n 1 {f} S)"
  proof- fix f assume A: "f \<in> Fs"
    obtain As where As_def: "finite As \<and> As partitions (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
                                           (\<forall>S\<in>As. is_r_prepared m n 1 {f} S)"
      using 0 A unfolding is_r_preparable_def by blast 
    show " finite (Ps f) \<and> (Ps f)  partitions (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
                     (\<forall>S\<in>(Ps f) . is_r_prepared m n 1 {f} S)"
      apply(rule SomeE[of _ _ As])
      unfolding Ps_def apply blast
      by(rule As_def)
  qed
  obtain Qs where Qs_def: "Qs = family_intersect (Ps ` Fs)"
    by blast 
  have Qs_fun: "\<And>q.  q \<in> Qs \<Longrightarrow> \<exists>f. \<forall>Psa\<in>Ps ` Fs. f Psa \<in> Psa \<and> q = \<Inter> (f ` Ps ` Fs)"
    unfolding Qs_def
    apply(rule family_intersect_mem_inter[of "Ps ` Fs" "carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"])
    using PsE  apply blast
    using PsE apply blast
    using assms apply blast
    using PsE  apply (simp add: assms(5))
    by auto 
  have Qs_partitions: "Qs partitions carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
    unfolding Qs_def 
    apply(rule family_intersect_partitions)
    using PsE assms assms by auto 
  have F0: "is_r_preparable m n cd Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) "
    apply(rule is_r_preparable_partition[of Qs])
    unfolding family_intersect_def Qs_def
      apply(rule finite_set_imp_finite_atoms)
    using PsE assms apply blast
    using Qs_partitions unfolding Qs_def family_intersect_def apply blast
  proof- 
    have Fs_nonempty: "Fs \<noteq> {}"
      using assms by auto
    fix a assume A: " a \<in> atoms_of (\<Union> (Ps ` Fs))"
    have a_in: "a \<in> Qs"
      unfolding Qs_def family_intersect_def using A by blast 
    obtain G0 where G0_def: "\<forall>P\<in>Ps ` Fs. G0 P \<in> P \<and> a = \<Inter> (G0 ` Ps ` Fs)"
      using Qs_fun a_in by blast 
    obtain G where G_def: "G = (\<lambda>f. G0 (Ps f))"
      by blast 
    have G_in: "\<And>f. f \<in> Fs \<Longrightarrow> G f \<in> Ps f"
      using G0_def unfolding G_def by blast 
    have 0: "\<Inter> (G0 ` Ps ` Fs) = (\<Inter>f \<in> Fs. G f)"
      using G0_def unfolding G_def by blast 
    hence 1: "a = \<Inter> (G0 ` Ps ` Fs)"
      using G0_def Fs_nonempty 
      by (metis (no_types, opaque_lifting) INF_eq_const empty_is_image)
    have a_eq: "a = (\<Inter>f \<in> Fs. G f)"
      unfolding 0 1 by blast 
    have a_prepared: "\<And>f S. f \<in> Fs \<Longrightarrow> S \<in> Ps f \<Longrightarrow>  (\<exists>Cs \<C>.
           \<C> \<in> {f} \<rightarrow> Cs \<and>
           card (center ` \<C> ` {f}) \<le> 1 \<and>
           S = (\<Inter>g\<in>{f}. condition_to_set (\<C> g)) \<and>
           (\<forall>g\<in>{f}. is_cell_condition (\<C> g) \<and> arity (\<C> g) = m \<and> (\<exists>u h k. SA_poly_factors p m n g (center (\<C> g)) (condition_to_set (\<C> g)) u h k)))"
      using PsE unfolding is_r_prepared_def by blast 
    have a_prepared': "\<And>f S. f \<in> Fs \<Longrightarrow> S \<in> Ps f \<Longrightarrow>  (\<exists>\<C>.
           card (center ` \<C> ` {f}) \<le> 1 \<and>
           S = (\<Inter>f\<in>{f}. condition_to_set (\<C> f)) \<and>
           (\<forall>f\<in>{f}. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k)))"
      using a_prepared by blast 
    obtain \<C> where \<C>_def: "\<C> = (\<lambda>f.  (SOME x.
    card (center ` x ` {f}) \<le> 1 \<and>
    G f = (\<Inter>g\<in>{f}. condition_to_set (x g)) \<and>
    (\<forall>g\<in>{f}. is_cell_condition (x g) \<and> arity (x g) = m \<and> (\<exists>u h k. SA_poly_factors p m n g (center (x g)) (condition_to_set (x g)) u h k))) )"
      by blast 
    have \<C>E: "\<And>f. f \<in> Fs \<Longrightarrow> card (center ` \<C> f ` {f}) \<le> 1 \<and>
           (G f) = (\<Inter>g\<in>{f}. condition_to_set (\<C> f g)) \<and>
           (\<forall>g\<in>{f}. is_cell_condition (\<C> f g) \<and> arity (\<C> f g) = m \<and> (\<exists>u h k. SA_poly_factors p m n g (center (\<C> f g)) (condition_to_set (\<C> f g)) u h k))"
    proof- 
      fix f assume A: "f \<in> Fs"
      obtain \<A> where \<A>_def: "card (center ` \<A> ` {f}) \<le> 1 \<and>
G f = (\<Inter>g\<in>{f}. condition_to_set (\<A> g)) \<and>
(\<forall>g\<in>{f}. is_cell_condition (\<A> g) \<and> arity (\<A> g) = m \<and> (\<exists>u h k. SA_poly_factors p m n g (center (\<A> g)) (condition_to_set (\<A> g)) u h k))"
        using A a_prepared'[of f "G f"] G_in[of f] by blast 
      show "card (center ` (\<C> f) ` {f}) \<le> 1 \<and>
           (G f) = (\<Inter>g\<in>{f}. condition_to_set ((\<C> f) g)) \<and>
           (\<forall>g\<in>{f}. is_cell_condition (\<C> f g) \<and> arity (\<C> f g) = m \<and> (\<exists>u h k. SA_poly_factors p m n g (center (\<C> f g)) (condition_to_set (\<C> f g)) u h k))"
        apply(rule SomeE[of "\<C> f" _ \<A>])
        unfolding \<C>_def apply metis  
        by(rule \<A>_def)
    qed
    obtain \<B> where \<B>_def: "\<B> = (\<lambda>f. \<C> f f)"
      by blast 
    have \<B>_center: "\<And>f. center ` \<B> ` {f} =      (center ` \<C> f ` {f})"
      unfolding \<B>_def by blast 
    have \<B>_inter: "\<And>f. f \<in> Fs \<Longrightarrow> (G f) =  condition_to_set (\<B> f)"
    proof- fix f assume A: "f \<in> Fs"
      have 0: "(\<Inter>g\<in>{f}. condition_to_set (\<C> f g)) = condition_to_set (\<C> f f)"
        by blast 
      show "(G f) =  condition_to_set (\<B> f)"
        using A \<C>E[of f] unfolding 0 \<B>_def by blast 
    qed
    have \<B>_factors: "\<And>f. f \<in> Fs \<Longrightarrow> is_cell_condition (\<B> f) \<and> arity (\<B> f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<B> f)) (condition_to_set (\<B> f)) u h k)"
    proof- fix f assume A: "f \<in> Fs"
      show "is_cell_condition (\<B> f) \<and> arity (\<B> f) = m \<and> (\<exists>u h k. SA_poly_factors p m n f (center (\<B> f)) (condition_to_set (\<B> f)) u h k)"
      using \<C>E[of f] A unfolding \<B>_def by blast 
    qed
    have 2: "card (center ` \<B> ` Fs) \<le> cd"
      unfolding cd_def 
      by (meson assms card_image_le finite_imageI le_trans)
    show "is_r_preparable m n cd Fs a"
      apply(rule is_r_prepared_imp_is_r_preparable)
      apply(rule is_r_preparedI[of _ _ \<B> "\<B> ` Fs"])
      using assms apply blast
      using assms apply blast
       apply blast
      using 2 apply blast
      using \<B>_factors apply blast
      using \<B>_factors apply blast
      using \<B>_factors apply blast
      unfolding a_eq using \<B>_inter 
      by blast
  qed
  thus ?thesis unfolding cd_def by auto 
qed

lemma Qp_is_1_preparable: 
  assumes "n > 0"
  assumes "\<And>f. f \<in> Fs \<Longrightarrow> deg (SA m) f \<le> Suc d"
  assumes "Fs \<subseteq> carrier (UP (SA m))"
  assumes "finite Fs"
  assumes "Fs \<noteq> {}"
  shows "is_r_preparable m n 1 Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
proof- 
  have 0: "is_r_preparable m n (card Fs) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
    by(intro  Qp_is_r_preparable assms, auto)
  show ?thesis 
  proof(cases "card Fs = 1")
    case True
    then show ?thesis using 0 by auto 
  next
    case False
    then obtain r where r_def: "card Fs = Suc (Suc r)"
      using assms(5) 
      by (metis One_nat_def assms(4) card_gt_0_iff not0_implies_Suc rel_simps(70))
    obtain l where l_def: "l =  (LEAST x. is_r_preparable m n (Suc (Suc x)) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)))"
      by blast 
    have l_prep: "is_r_preparable m n (Suc (Suc l)) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
      unfolding l_def apply(rule LeastI[of _ r])
      using 0 unfolding r_def by blast 
    have l_eq: "l = 0"
    proof(rule ccontr)
      assume not: "l \<noteq> (0::nat)"
      then obtain k where k_def: "l = Suc k"
        using not0_implies_Suc by blast
      have k_less: "k < l"
        using k_def by blast 
      have 0: "is_r_preparable m n (Suc l) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
        by(rule is_r_preparable_reduce[of ], auto simp: l_prep assms )
      show False
        using 0 unfolding k_def 
        using k_less l_def not_less_Least by blast 
    qed
    have  "is_r_preparable m n (Suc 0) Fs (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
       apply(rule is_r_preparable_reduce[of ])
       using assms  l_prep l_eq by(auto simp add: denef_I denef_II_axioms )
    thus ?thesis 
      by (simp add: l_prep)
  qed
qed


lemma denef_cell_decomp_II_induct:
  shows "denef_II p (Suc d)" 
proof-
  have main:  "\<And> n m Ps.
       finite Ps \<and> (\<forall>P\<in>Ps. P \<in> carrier (UP (SA m)) \<and> deg (SA m) P \<le> Suc d) \<and> 0 < n\<Longrightarrow>
       (\<exists>S. is_cell_decomp m S (carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)) \<and>
            (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k))"
  proof- fix n m Ps
    assume P0: "finite Ps \<and> (\<forall>P\<in>Ps. P \<in> carrier (UP (SA m)) \<and> deg (SA m) P \<le> Suc d)\<and> 0 < (n::nat)"
    have finite_Ps: "finite Ps"
      using P0 by blast 
    have Ps_closed: "\<And>P. P \<in> Ps \<Longrightarrow> P \<in> carrier (UP (SA m))"
      using P0 by blast 
    have Ps_deg_bound: "\<And>P. P \<in> Ps \<Longrightarrow> deg (SA m) P \<le> Suc d"
      using P0 by blast 
    have "(\<exists>S. is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
            (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k))"
    proof(cases "Ps = {}")
      case True
      obtain \<C> where \<C>_def: "\<C> = Cond m (carrier (Q\<^sub>p\<^bsup>m\<^esup>)) \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> \<zero>\<^bsub>SA m\<^esub> closed_ray"
        by blast 
      have \<C>_cell: "is_cell_condition \<C>"
        using carrier_is_cell unfolding \<C>_def by blast 
      have \<C>_set: "condition_to_set \<C> = carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)"
        using carrier_is_cell unfolding \<C>_def by blast 
      have 0: "is_cell_decomp m {\<C>} (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
        using singleton_cell_decomp[of \<C> m] \<C>_cell unfolding \<C>_set unfolding \<C>_def
        arity.simps by blast 
      then show ?thesis unfolding True by blast 
    next
      case False
      have n_pos: "n \<ge> 1"
        using P0 by linarith   
      have n_nonzero: "n \<noteq> 0"
        using n_pos by linarith 
      have F0: "is_r_preparable m n 1 Ps (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"
        using  Qp_is_1_preparable[of ] P0 False by auto 
      obtain As where As_def: " finite As \<and> As partitions carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>) \<and> (\<forall>S\<in>As. is_r_prepared m n 1 Ps S)"
        using F0  is_r_preparable_def[of m n 1 Ps "(carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>))"]
        by blast 
      have F1: "\<And>S. S \<in> As \<Longrightarrow> \<exists>Cs \<C>.
       \<C> \<in> Ps \<rightarrow> Cs \<and>
       card (center ` \<C> ` Ps) \<le> 1 \<and>
       S = (\<Inter>f\<in>Ps. condition_to_set (\<C> f)) \<and>
       (\<forall>f\<in>Ps. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and>
                   (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
        using As_def is_r_preparedE[of m n 1 Ps] by blast 
      have F2: "\<And>S. S \<in> As \<Longrightarrow> \<exists>\<C>.
       card (center ` \<C> ` Ps) \<le> 1 \<and>
       S = (\<Inter>f\<in>Ps. condition_to_set (\<C> f)) \<and>
       (\<forall>f\<in>Ps. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> 
                   (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
        using F1 by blast 
      show "\<exists>S. is_cell_decomp m S (carrier (Q\<^sub>p\<^bsup>Suc m\<^esup>)) \<and>
              (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
        apply(rule decomp_partition_elements[of _ _ As])
        apply blast
        using As_def apply blast
        using As_def apply blast
      proof- fix S assume A: "S \<in> As"
        obtain \<C> where \<C>_def: " card (center ` \<C> ` Ps) \<le> 1 \<and>
       S = (\<Inter>f\<in>Ps. condition_to_set (\<C> f)) \<and>
       (\<forall>f\<in>Ps. is_cell_condition (\<C> f) \<and> arity (\<C> f) = m \<and> 
          (\<exists>u h k. SA_poly_factors p m n f (center (\<C> f)) (condition_to_set (\<C> f)) u h k))"
           using A As_def is_r_preparedE[of m n 1 Ps] F0 
           by metis            
        obtain f where f_def: "f \<in> Ps"
          using False by blast 
        obtain c where c_def: "c = center (\<C> f)"
          by blast 
        have arity: "arity (\<C> f) = m"
          using f_def \<C>_def by blast 
        have cell: "is_cell_condition (\<C> f)"
          using f_def \<C>_def by blast 
        have c_closed: "c \<in> carrier (SA m)"
          using cell is_cell_conditionE(2)[of m "fibre_set (\<C> f)" c] condition_decomp'[of "\<C> f"] 
          unfolding c_def arity 
          using is_cell_conditionE''(5) by blast
        have 0: " card (center ` \<C> ` Ps)  = 1"                  
        proof- 
          have "center ` \<C> ` Ps \<noteq> {}"
            using P0 False by blast 
          hence "card (center ` \<C> ` Ps) \<noteq> 0"
            by (meson card_0_eq finite_Ps finite_imageI)
          thus ?thesis
          using \<C>_def using f_def False by linarith 
        qed
        have 1: "(center ` \<C> ` Ps) = {c}"
          using 0 f_def unfolding c_def 
          by (smt card_1_singletonE doubleton_eq_iff image_insert insert_absorb insert_absorb2)
        have " \<exists>\<C>'. is_cell_condition \<C>' \<and>
       center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` \<C> ` Ps) \<and> 
                              condition_to_set \<C>' = \<Inter> (condition_to_set ` \<C> ` Ps)"
          apply(rule cell_finite_intersection_same_center[of "\<C> ` Ps" c m])
          using P0 apply blast
          using \<C>_def apply blast
          using 1 apply blast
          using \<C>_def apply blast
          using False by blast 
        then obtain \<C>' where \<C>'_def: " is_cell_condition \<C>' \<and>
                      center \<C>' = c \<and> arity \<C>' = m \<and> fibre_set \<C>' = \<Inter> (fibre_set ` \<C> ` Ps) \<and> 
                                    condition_to_set \<C>' = \<Inter> (condition_to_set ` \<C> ` Ps)"
          by auto   
        have S_eq0: "S = (\<Inter>f\<in>Ps. condition_to_set (\<C> f))"
          using A \<C>_def F2[of S] by blast 
        have S_eq: "S = condition_to_set \<C>'"
          unfolding S_eq0 using \<C>'_def by blast 
        have 2: "is_cell_decomp m {\<C>'} S"
          using \<C>'_def unfolding S_eq by (meson singleton_cell_decomp)
        have 3: "(\<forall>A\<in>{\<C>'}. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
        proof
          fix A assume A: " A \<in> {\<C>'} "
          then have A_eq: "A = \<C>'"
            by blast 
          show " \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k"
            unfolding A_eq 
          proof
            fix g assume A1: "g\<in> Ps"
            show " \<exists>u h k. SA_poly_factors p m n g (center \<C>') (condition_to_set \<C>') u h k"
            proof(rule SA_poly_factors_subset[of _ _ _  _ "condition_to_set (\<C> g)"])
              have p0: "center \<C>' = c"
                using \<C>'_def by blast 
              have p1: "center (\<C> g) = c"
                using A1 1 by blast 
              have p2: "(\<exists>u h k. SA_poly_factors p m n g (center (\<C> g)) (condition_to_set (\<C> g)) u h k)"
                using \<C>_def A1 by blast 
              show "\<exists>u h k. SA_poly_factors p m n g (center \<C>') (condition_to_set (\<C> g)) u h k"
                using p2 unfolding p0 p1 by blast 
              show "condition_to_set \<C>' \<subseteq> condition_to_set (\<C> g)"
                using \<C>'_def A1 by blast 
            qed
          qed
        qed
        show " \<exists>S'. is_cell_decomp m S' S \<and> (\<forall>A\<in>S'. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
          using 2 3 by blast 
      qed
    qed
    thus " \<exists>S. is_cell_decomp m S (carrier (Frac (padic_int p)\<^bsup>Suc m\<^esup>)) \<and>
           (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p m n P (center A) (condition_to_set A) u h k)"
      unfolding Q\<^sub>p_def Zp_def by blast 
  qed
  thus ?thesis unfolding denef_II_def denef_II_axioms_def using padic_fields_axioms by blast 
qed

end

context padic_fields
begin

lemma denef_cell_decomp_II_base: 
"denef_II p 0"
  unfolding denef_II_def denef_II_axioms_def 
proof(rule conjI, rule padic_fields_axioms)
  show "\<forall>n m Ps.
       finite Ps \<and> (\<forall>P\<in>Ps. P \<in> carrier (UP (SA n)) \<and> deg (SA n) P \<le> 0)\<and> 0 < m \<longrightarrow>
       (\<exists>S. is_cell_decomp n S (carrier (Frac (padic_int p)\<^bsup>Suc n\<^esup>)) \<and>
            (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p n m P (center A) (condition_to_set A) u h k))"
  proof(rule , rule, rule, rule)
    fix n m Ps 
    assume A: "finite Ps \<and> (\<forall>P\<in>Ps. P \<in> carrier (UP (SA n)) \<and> deg (SA n) P \<le> 0)\<and> 0 < (m::nat)"
    then have Ps_finite: "finite Ps"
      by blast
    have Ps_closed: "\<And> P. P \<in> Ps \<Longrightarrow> P \<in> carrier (UP (SA n))"
      using A by blast 
    have Ps_deg: "\<And>P. P \<in> Ps \<Longrightarrow> deg (SA n) P = 0"
      using A  by blast
    have 0: "\<And>P. P \<in> Ps \<Longrightarrow> \<exists>c \<in> carrier (SA n). P = to_polynomial (SA n) c"
      using Ps_deg Ps_closed by (metis UPSA.lcf_closed UPSA.to_poly_inverse)
    obtain F where F_def: "F = (\<lambda>P. (SOME c. c \<in> carrier (SA n) \<and> P = to_polynomial (SA n) c))"
      by blast 
    have FE: "\<And>P. P \<in> Ps \<Longrightarrow> F P \<in> carrier (SA n) \<and> P = to_polynomial (SA n) (F P)"
      using tfl_some 0 F_def by smt
    have F_closed: "\<And>P. P \<in> Ps \<Longrightarrow> F P \<in> carrier (SA n)"
      using FE by blast 
    have F_eq: "\<And>P. P \<in> Ps \<Longrightarrow> P = to_polynomial (SA n) (F P)"
      using FE by blast 
    obtain S where S_def: "is_cell_decomp n S (carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>))"
      using denef_cell_decomp_I_base zero_closed[of n] deg_zero[of n]
      unfolding denef_I_def denef_I_axioms_def  Q\<^sub>p_def Zp_def by blast 
    have 1: " (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p n m P (center A) (condition_to_set A) u h k)"
    proof(rule, rule) 
      fix \<C> P assume A: "\<C> \<in> S" "P \<in> Ps"
      have \<C>_cell: "is_cell_condition \<C>"
        using  A S_def is_cell_decompE by blast 
      have \<C>_arity: "arity \<C> = n" 
        using  A S_def is_cell_decompE(4) by blast 
      obtain C c a1 a2 I where params: "\<C> = Cond n C c a1 a2 I"
        using \<C>_arity arity.simps condition_decomp' by blast
      have c_closed: "c \<in> carrier (SA n)"
        using \<C>_cell unfolding params 
        using is_cell_conditionE(2) by blast
      have C_closed: "is_semialgebraic n C"
        using \<C>_cell unfolding params 
        using is_cell_conditionE(1) by blast
      have a1_closed: "a1 \<in> carrier (SA n)"
        using \<C>_cell unfolding params 
        using is_cell_conditionE''(6) by blast
      have a2_closed: "a2 \<in> carrier (SA n)"
        using \<C>_cell unfolding params 
        using is_cell_condition.simps by blast
      have I_convex: "is_convex_condition I"
        using \<C>_cell unfolding params 
        using is_cell_conditionE(5) by blast
      obtain f where f_def: "f = F P"
        by blast 
      have f_closed: "f \<in> carrier (SA n)"
        unfolding f_def by(rule F_closed, rule A)
      have P_eq: "P = to_polynomial (SA n) f"
        unfolding f_def by(rule F_eq, rule A)     
      have "SA_poly_factors p n m P (center \<C>) (condition_to_set \<C>) \<one>\<^bsub>SA (Suc n)\<^esub> f 0"
        apply(rule SA_poly_factorsI)
        unfolding params condition_to_set.simps cell_def mem_Collect_eq list_tl list_hd 
            apply blast
        using SA_car_memE(3) apply blast
          unfolding center.simps apply(rule c_closed)
           apply(rule f_closed)
        proof- 
          fix x t assume A': "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"  "t \<in> carrier Q\<^sub>p"
           "t # x \<in> carrier (Q\<^sub>p\<^bsup>Suc n\<^esup>) \<and> x \<in> C \<and> val (t \<ominus> c x) \<in> I (val (a1 x)) (val (a2 x))"
          have t_closed: "t \<in> carrier Q\<^sub>p"
            using A' by blast
          have x_closed: "x \<in> carrier (Q\<^sub>p\<^bsup>n\<^esup>)"
            using A' by blast
          have x_in_C: "x \<in> C"
            using A' by blast 
          have P0: "val (\<one>\<^bsub>SA (Suc n)\<^esub> (t # x)) = 0"
            using SA_oneE[of "t#x" "Suc n"] val_one A'(3) by metis 
          have P1: "SA_poly_to_Qp_poly n x P = to_polynomial Q\<^sub>p (f x)"
            unfolding P_eq 
            by(rule SA_poly_to_Qp_poly_extends_apply, rule x_closed, rule f_closed)
          have P2: "SA_poly_to_Qp_poly n x P \<bullet> t = f x"
            unfolding P1 
            by(rule UPQ.to_fun_to_poly, rule SA_car_closed[of _ n], rule f_closed, rule x_closed, rule t_closed)
          have P3: " \<one>\<^bsub>SA (Suc n)\<^esub> (t # x) = \<one>"
            using SA_oneE[of "t#x" "Suc n"]  A'(3) by metis 
          have P4: "\<one>\<^bsub>SA (Suc n)\<^esub> (t # x) [^] m = \<one>"
            unfolding P3 
            using Qp.nat_pow_one by blast
          have P5: "(t \<ominus> c x) [^] (0::nat) = \<one>"
            using Qp.nat_pow_0 by blast
          have fx_closed: "f x \<in> carrier Q\<^sub>p"
            using x_closed f_closed SA_car_closed by blast 
          have P6: "SA_poly_to_Qp_poly n x P \<bullet> t = \<one>\<^bsub>SA (Suc n)\<^esub> (t # x) [^] m \<otimes> f x \<otimes> (t \<ominus> c x) [^] (0::nat)"
            unfolding P2 P4 P5 using fx_closed Qp.cring_simprules(12) Qp.r_one by presburger
          show "val (\<one>\<^bsub>SA (Suc n)\<^esub> (t # x)) = 0 \<and> SA_poly_to_Qp_poly n x P \<bullet> t = \<one>\<^bsub>SA (Suc n)\<^esub> (t # x) [^] m \<otimes> f x \<otimes> (t \<ominus> c x) [^] (0::nat)"
            using P6 P0 by blast 
        qed
      thus " \<exists>u h k. SA_poly_factors p n m P (center \<C>) (condition_to_set \<C>) u h k"
          using f_closed by blast 
    qed
    show "\<exists>S. is_cell_decomp n S (carrier (Frac (padic_int p)\<^bsup>Suc n\<^esup>)) \<and>
           (\<forall>A\<in>S. \<forall>P\<in>Ps. \<exists>u h k. SA_poly_factors p n m P (center A) (condition_to_set A) u h k)"
      using S_def 1 unfolding Q\<^sub>p_def Zp_def  by blast 
  qed
qed

theorem denef_cell_decomp_I:
  "denef_I p d"
proof-
  have "\<forall>k \<le> d. denef_I p d \<and> denef_II p d"
  proof( induction d)
  case 0
    then show ?case using denef_cell_decomp_I_base 
    using denef_cell_decomp_II_base by blast
  next
    case (Suc d)
    have 0: "denef_I p (Suc d)"
      apply(intro common_decomp_proof_context.denef_I common_decomp_proof_context.intro)
      using Suc apply blast
      using Suc by blast
    have 1: "denef_II p (Suc d)"
      apply(intro common_decomp_proof_context.denef_cell_decomp_II_induct
                  common_decomp_proof_context.intro)       
      using Suc by auto  
    show "\<forall>k\<le>Suc d. denef_I p (Suc d) \<and> denef_II p (Suc d)"
      using 0 1 Suc by blast 
  qed
  thus ?thesis by blast 
qed

theorem denef_cell_decomp_II:
"denef_II p d"
  apply(induction d)
   apply(intro denef_cell_decomp_II_base,
          intro common_decomp_proof_context.denef_cell_decomp_II_induct
                common_decomp_proof_context.intro denef_cell_decomp_I)
  by auto 
end  
end