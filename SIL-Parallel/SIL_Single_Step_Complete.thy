subsection \<open>Soundness and Completeness\<close>

theory SIL_Single_Step_Complete
imports SIL_Single_Step SIL_Single_Step_WP SIL_Single_Step_Sound
begin

subsubsection "Soundness"

lemma seq_wp_single_is_pre:
  assumes "\<turnstile> \<langle>wp_single c\<^sub>1 c' Q\<rangle> c\<^sub>1 \<leadsto> c' \<langle>Q\<rangle>"
  and " \<turnstile> \<langle>wp_single c\<^sub>2 c' Q\<rangle> c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
shows "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' Q\<rangle> c\<^sub>1;;c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"

proof(cases "c\<^sub>1 = SKIP")
  case True
  obtain Q' where  assn: "Q' = post_assn Q"
    by auto
  have h0: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> c\<^sub>2 = c'\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>"
    by (metis sSubstituteCom sSeqSkip True)
  have h1: "\<forall>s. wp_single (c\<^sub>1;;c\<^sub>2) c' (OK Q') s \<longrightarrow>  Q' s \<and> c\<^sub>2 = c'"
    unfolding wp_single_def
    using True by auto
  have h2: " \<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' (OK Q')\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>"
    unfolding wp_single_def
    using wp_single_Seq_OK h0 h1 sConseqOK wp_single_def
    by auto
 have h3: "\<forall>s. wp_single (c\<^sub>1;;c\<^sub>2) c' (ER Q') s \<longrightarrow>  False"
    unfolding wp_single_def
    using True by auto
  have h4: "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' (ER Q')\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>ER Q'\<rangle>"
    using h3 sFalsePre by presburger
  then show ?thesis by (metis assn h2 h4 post_assn.elims)
next
  case False
  then show ?thesis sorry
qed
 



lemma wp_single_is_pre: 
  "\<turnstile> \<langle>wp_single c c' Q\<rangle> c \<leadsto> c' \<langle>Q\<rangle>"
proof(induction c arbitrary: Q)
  case SKIP
  then show ?case 
    apply (cases Q)
    apply (metis wp_single_SKIP_OK sFalsePre strengthen_pre)
    by (metis wp_single_SKIP_ER sFalsePre strengthen_pre)
next
  case ABORT
  then show ?case
    apply (cases Q)
    apply (metis wp_single_ABORT_OK sFalsePre strengthen_pre)
    by (metis sFalsePre strengthen_pre wp_single_ABORT_ER sAbort)
next
  case (Assign x1 x2)
  then show ?case 
    apply (cases Q)
    apply (metis Assign' sFalsePre strengthen_pre wp_single_Assign_OK)
    by (metis wp_single_Assign_ER sFalsePre strengthen_pre)
next
  case (AssignND x1 x2)
  then show ?case
    apply(cases Q)
    using  wp_single_AssignND_OK
    apply (smt (verit, best) sAssignNDEmpty sAssignNDOK sFalsePre strengthen_pre
        wp_single_AssignND_Empty_OK)
    by (metis wp_single_AssignND_ER sFalsePre strengthen_pre)
next
  case (Seq c1 c2)
  then show ?case by (simp add: seq_wp_single_is_pre)
next
  case (If x1 c1 c2)
  then show ?case
    apply(cases Q)
    using wp_single_If_OK sorry
next
  case (SelectND x)
  then show ?case sorry
next
  case (While x1 c)
  then show ?case sorry
next
  case (Par c1 c2)
  then show ?case sorry
qed


lemma valid_imp_wp: "\<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<Longrightarrow>  \<forall>s. P s \<longrightarrow> wp_single c c' Q s"
  unfolding wp_single_def SIL_Single_Step_Valid_def
  apply(cases Q)
by fastforce+

lemma sil_complete: 
  "\<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle>"
  apply (rule strengthen_pre[where P="wp_single c c' Q"])
  apply (metis valid_imp_wp)
by (metis wp_is_pre)

corollary sil_sound_complete: 
  "\<turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<longleftrightarrow> \<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle>"
by(fastforce simp: sil_single_step_sound sil_complete)