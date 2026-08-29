theory SIL_Star_Complete
imports SIL_Star_WP SIL_Star_Sound SIL_Big_Step_Complete
begin

lemma ParND_is_pre:
  assumes IH1: "\<And>Q. \<turnstile> \<langle>wp c\<^sub>1 Q\<rangle> c\<^sub>1 \<langle>Q\<rangle>"
      and IH2: "\<And>Q. \<turnstile> \<langle>wp c\<^sub>2 Q\<rangle> c\<^sub>2 \<langle>Q\<rangle>"
      and "c\<^sub>1 \<noteq> SKIP"
      and "c\<^sub>2 \<noteq> SKIP"
    shows "\<turnstile> \<langle>wp (c\<^sub>1 || c\<^sub>2) Q\<rangle> c\<^sub>1 || c\<^sub>2 \<langle>Q\<rangle>"
  sorry

thm tParallelL

lemma wp_is_pre: "\<turnstile> \<langle>wp c Q\<rangle> c \<langle>Q\<rangle>"
  proof(induction c arbitrary: Q)
    case SKIP
    then show ?case
      by (metis tFalsePre wp_SKIP_OK wp_SKIP_ER SIL_Star.tSkip SIL_Star.strengthen_pre_er post.exhaust)
    case ABORT
    then show ?case
      by (metis SIL_Star.strengthen_pre SIL_Star.tAbort post_assn.elims tFalsePre wp_ABORT_ER
          wp_ABORT_OK)
  next
    case (Assign x1 x2)
    then show ?case 
      apply (cases Q)
      apply simp
      apply (simp add: SIL_Star.tAssign)
      by (metis wp_Assign_ER SIL_Star.strengthen_pre_er tFalsePre)
  next
    case (AssignND x1 x2)
    then show ?case 
      apply (cases Q)
       apply clarsimp
      apply (cases "x2 = {}")
      apply clarsimp
      apply (metis tFalsePre)
      using wp_AssignND_NonEmpty_OK apply (simp add: SIL_Star.tAssignNDOK)
      apply (cases "x2 = {}")
       apply clarsimp
       apply (metis SIL_Star.tAssignNDER)
     by (simp add: tFalsePre)
  next
    case (Seq c1 c2)
    then show ?case
      apply (cases Q)
       apply clarsimp
       apply (metis wp_Seq_OK SIL_Star.tSeqOK)
      apply clarsimp
      by (metis SIL_Star.tSeqER SIL_Star.tSeqOK tDisjunction)
    next
    case (If x1 c1 c2)
    then show ?case
      apply(cases Q)
       apply clarsimp
      using wp_If
       apply (smt (verit, del_insts) SIL_Star.strengthen_pre SIL_Star.tIf)
      apply clarsimp
      using wp_If by (smt (verit, del_insts) SIL_Star.strengthen_pre SIL_Star.tIf)
  next
    case (SelectND x)
    then show ?case
      apply clarsimp
      apply (cases Q)
      sorry
  next
    case (While x1 c)
    then show ?case
      apply (cases Q)
      apply clarsimp
      sorry
  next 
    case (Par c1 c2)
    then show ?case
       apply (cases "c1 = SKIP")
        apply (metis wp_Par_SKIP_L tParallelSkipL)
       apply (cases "c2 = SKIP")
       apply (metis wp_Par_SKIP_R tParallelSkipR)
      using wp_Par_OK by (simp add: ParND_is_pre)
qed

lemma valid_imp_wp_big_step: "\<Turnstile> \<langle>P\<rangle> c  \<langle>Q\<rangle> \<Longrightarrow>
    \<forall>s. P s \<longrightarrow> wp_big_step c Q s"
  unfolding wp_big_step_def SIL_valid_def
  apply(cases Q)
  apply fastforce
by fastforce

lemma sil_complete: 
  "\<Turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>"
  apply (rule strengthen_pre[where P="wp_big_step c Q"])
  apply (metis valid_imp_wp_big_step)
by (metis wp_big_step_is_pre)

corollary sil_sound_complete: 
  "\<turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle> \<longleftrightarrow> \<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>"
   by(fastforce simp: sil_sound sil_complete)

end
(*
Table of Contents
- Abstract
- Introduction Section - Explaining utility of this work. 
- Literature Review 
  - Hoare Logic
  - Predicate Transformers
  - "Finding Attackers by means of Predicate Transformers"
  - IL
  - SIL
  - Predicate Transformers in SIL
- Introduction to IL and SIL, comparison of the logics
  - Providing toy example to demonstrate where IL fails, and potentially if SIL could fail (unsure)
  - Showing use case of SIL predicate transformers
- Modification of SIL (e.g. "Error States")
- Defining Predicate Transformers for SIL with some proofs.
- Applying Predicate Transformers to determine possibility of attacks on small example systems
  - Applying predicate transformers to toy examples
- Applying Predicate Transformers to Large Scale Systems
- Conclusion
*)
