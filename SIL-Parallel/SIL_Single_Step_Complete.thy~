subsection \<open>Soundness and Completeness\<close>

theory SIL_Single_Step_Complete
imports SIL_Single_Step SIL_Single_Step_WP SIL_Single_Step_Sound
begin

subsubsection "Soundness"

lemma seq_wp_single_is_pre:
  assumes "\<forall>c' .\<turnstile> \<langle>wp_single c\<^sub>1 c' Q\<rangle> c\<^sub>1 \<leadsto> c' \<langle>Q\<rangle>"
  and "\<forall>c' . \<turnstile> \<langle>wp_single c\<^sub>2 c' Q\<rangle> c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
shows "\<forall>c' .\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' Q\<rangle> c\<^sub>1;;c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
proof(intro allI)
  fix c'
  show "\<turnstile> \<langle>wp_single (c\<^sub>1;; c\<^sub>2) c' Q\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
  proof (cases "c\<^sub>1 = SKIP")
    case True
      obtain Q' where  assn: "Q' = post_assn Q"
      by auto
    have h0: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> c\<^sub>2 = c'\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>"
      using sSubstituteCom sSeqSkip True by (metis (mono_tags, lifting) strengthen_pre)
    have h1: "\<forall>s. wp_single (c\<^sub>1;;c\<^sub>2) c' (OK Q') s \<longrightarrow>  Q' s \<and> c\<^sub>2 = c'"
      unfolding wp_single_def
      using True by auto
    have h2: "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' (OK Q')\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>"
      unfolding wp_single_def
      using wp_single_Seq_OK h0 h1 sConseqOK wp_single_def
      by auto
   have h3: "\<forall>s. wp_single (c\<^sub>1;;c\<^sub>2) c' (ER Q') s \<longrightarrow>  False"
      unfolding wp_single_def
      using True by auto
    have h4: "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' (ER Q')\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>ER Q'\<rangle>"
      using h3 sFalsePre by presburger
    have h5: "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' Q\<rangle> c\<^sub>1;; c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
      by (metis assn h2 h4 post_assn.elims)
    then show ?thesis by auto
  next
    case False
     fix c\<^sub>1'
    have h1: "\<turnstile> \<langle>wp_single c\<^sub>1 c\<^sub>1' Q\<rangle> c\<^sub>1;;c\<^sub>2 \<leadsto> c\<^sub>1';;c\<^sub>2 \<langle>Q\<rangle>"
      using assms sSeq by auto
    have h2: "\<turnstile> \<langle>\<lambda>s. wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1';;c\<^sub>2\<rangle> (c\<^sub>1;;c\<^sub>2) \<leadsto> c' \<langle>Q\<rangle>"
      by (smt (verit) h1 sFalsePre strengthen_pre)
    have h3: "\<turnstile> \<langle>\<lambda>s. (\<exists>c\<^sub>1'. wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1';;c\<^sub>2)\<rangle> (c\<^sub>1;;c\<^sub>2) \<leadsto> c' \<langle>Q\<rangle>"
      by (smt (verit, ccfv_SIG) assms(1) com.inject(3) h2 sSeq strengthen_pre)
    have h4: "\<turnstile> \<langle>wp_single (c\<^sub>1;;c\<^sub>2) c' Q\<rangle> (c\<^sub>1;;c\<^sub>2) \<leadsto> c' \<langle>Q\<rangle>"
      apply(cases Q)
      using wp_single_Seq_OK False apply (smt (verit, del_insts) Pair_inject SIL_Single_Step.post.simps(5) Small_Step.SeqE
          Small_Step.post.distinct(1) h3 strengthen_pre wp_single_def)
      using wp_single_Seq_OK False by (smt (verit, ccfv_SIG) Pair_inject SIL_Single_Step.post.simps(6) Small_Step.SeqE
          Small_Step.post.distinct(1) h3 sConseqER wp_single_def)
    then show ?thesis by auto
  qed
qed

lemma wp_single_if_is_pre:
  assumes "\<forall>c'. \<turnstile> \<langle>wp_single c\<^sub>1 c' Q\<rangle> c\<^sub>1 \<leadsto> c' \<langle>Q\<rangle>"
   and "\<forall>c'.  \<turnstile> \<langle>wp_single c\<^sub>2 c' Q\<rangle> c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
 shows "\<forall>c'. \<turnstile> \<langle>wp_single (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q\<rangle>  IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
  apply(intro allI)
  apply(cases Q)
  defer
   apply (simp add: sFalsePre wp_single_If_ER)
proof-
  fix c' Q'
  assume Qeq: "Q = OK Q'"
  have h0: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> bval b s \<and> c' = c\<^sub>1\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>" 
    using sIfTrue sSubstituteCom strengthen_pre weaken_post_ok  by (smt (verit, best))
  have h1: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> \<not>bval b s \<and> c' = c\<^sub>2\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>OK Q'\<rangle>" 
    using sIfFalse sSubstituteCom strengthen_pre weaken_post_ok by (smt (verit, best))
  have h2: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> bval b s \<and> c' = c\<^sub>1 \<or> Q' s \<and> \<not>bval b s \<and> c' = c\<^sub>2\<rangle>  
        IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (simp add: Qeq h0 h1 sDisjunction)
  have h4: "\<turnstile> \<langle>\<lambda>s. if bval b s then c' = c\<^sub>1 \<and> Q' s else c' = c\<^sub>2 \<and> Q' s\<rangle>  
        IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>" by (smt (verit, best) h2 strengthen_pre)
  then show "\<turnstile> \<langle>wp_single (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (simp add: Qeq wp_single_If_OK)
qed

lemma wp_single_select_is_pre:
  assumes "\<forall> b c c'. (b,c) \<in> set S \<longrightarrow> \<turnstile> \<langle>wp_single c c' Q\<rangle> c  \<leadsto> c' \<langle>Q\<rangle>"
  shows "\<turnstile> \<langle>wp_single (SELECT S) c' Q\<rangle> SELECT S \<leadsto> c' \<langle>Q\<rangle>"
  apply(cases Q)
   defer
   apply (simp add: sFalsePre)
proof-
  fix  Q'
  assume Qeq: "Q = OK Q'"
  have h0: "\<turnstile> \<langle>\<lambda>s. (\<exists>b. (b,c') \<in> set S \<and> bval b s) \<and> Q' s\<rangle> SELECT S \<leadsto> c' \<langle>OK Q'\<rangle>"
    using sSelectND sConseqOK sFalsePre weaken_post_ok by (smt (verit, ccfv_SIG))
  have h1: "\<turnstile> \<langle>\<lambda>s. \<exists>(b,c) \<in> set S. bval b s \<and> c' = c \<and> Q' s\<rangle> SELECT S \<leadsto> c' \<langle>OK Q'\<rangle>"
    by (smt (verit, best) case_prodE h0 sConseqOK)
  have h2: "\<turnstile> \<langle>\<lambda>s. (\<forall>(b, c)\<in>set S. \<not> bval b s) \<and> c' = ABORT \<and> Q' s\<rangle> SELECT S \<leadsto> c'\<langle>OK Q'\<rangle>"
    by (smt (verit, ccfv_threshold) sConseqOK sFalsePre sSelectNDNP)
  show " \<turnstile> \<langle>wp_single (SELECT S) c' Q\<rangle>  SELECT S \<leadsto> c' \<langle>Q\<rangle>" 
    using h1 h2 sDisjunction wp_single_SelectND_OK Qeq by presburger
qed

lemma par_wp_single_is_pre:
  assumes "\<forall>c' .\<turnstile> \<langle>wp_single c\<^sub>1 c' Q\<rangle> c\<^sub>1 \<leadsto> c' \<langle>Q\<rangle>"
  and "\<forall>c' . \<turnstile> \<langle>wp_single c\<^sub>2 c' Q\<rangle> c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
shows "\<turnstile> \<langle>wp_single (c\<^sub>1||c\<^sub>2) c' Q\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
proof(cases Q)
  case (OK Q')
  thm wp_single_Par_OK
  thm sParallelSkipL
  thm sParallelSkipR
  fix c\<^sub>1' c\<^sub>2'
  have h0: "\<turnstile> \<langle>wp_single c\<^sub>1 c\<^sub>1' Q\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c\<^sub>1'||c\<^sub>2 \<langle>Q\<rangle>"
    using sParallelL assms(1) by simp
  have h0': "\<turnstile> \<langle>wp_single c\<^sub>2 c\<^sub>2' Q\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c\<^sub>1||c\<^sub>2' \<langle>Q\<rangle>"
    using sParallelR assms(2) by simp
  have h1: "\<turnstile> \<langle>\<lambda>s. wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (smt (verit, best) h0 sFalsePre strengthen_pre)
  have h2: "\<turnstile> \<langle>\<lambda>s. \<exists>c\<^sub>1'.  wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using h1 strengthen_pre by (smt (verit, ccfv_SIG) assms(1) com.inject(7) sParallelL)
  have h3: "\<turnstile> \<langle>\<lambda>s. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2'\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (metis (mono_tags, lifting) h0' h1 strengthen_pre)
  have h4: "\<turnstile> \<langle>\<lambda>s. \<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2'\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using h3 strengthen_pre by (smt (verit, ccfv_SIG) assms(2) com.inject(7) sParallelR)
  have h5: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> (c' = c\<^sub>1) \<and> (c\<^sub>2 = SKIP)\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using sSubstituteCom sParallelSkipR OK by (metis (mono_tags, lifting) strengthen_pre)
  have h6: "\<turnstile> \<langle>\<lambda>s. Q' s \<and> (c' = c\<^sub>2) \<and> (c\<^sub>1 = SKIP)\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using sSubstituteCom sParallelSkipL OK by (metis (mono_tags, lifting) strengthen_pre)
  have h7: "\<turnstile> \<langle>\<lambda>s. (\<exists>c\<^sub>1'.  wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2) 
            \<or> (\<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2')
            \<or> (Q' s \<and> (c' = c\<^sub>2) \<and> (c\<^sub>1 = SKIP))
            \<or> (Q' s \<and> (c' = c\<^sub>2) \<and> (c\<^sub>1 = SKIP))
\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
  using h2 h4 h5 h6 sDisjunction by auto
  then show ?thesis
    by (smt (verit, best) OK h5 strengthen_pre wp_single_Par_OK wp_single_SKIP_OK)
next
  case (ER Q')
  fix c\<^sub>1' c\<^sub>2'
  have h0: "\<turnstile> \<langle>wp_single c\<^sub>1 c\<^sub>1' Q\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c\<^sub>1'||c\<^sub>2 \<langle>Q\<rangle>"
    using sParallelL assms(1) by simp
  have h0': "\<turnstile> \<langle>wp_single c\<^sub>2 c\<^sub>2' Q\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c\<^sub>1||c\<^sub>2' \<langle>Q\<rangle>"
    using sParallelR assms(2) by simp
  have h1: "\<turnstile> \<langle>\<lambda>s. wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (smt (verit, best) h0 sFalsePre strengthen_pre)
  have h2: "\<turnstile> \<langle>\<lambda>s. \<exists>c\<^sub>1'.  wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using h1 strengthen_pre by (smt (verit, ccfv_SIG) assms(1) com.inject(7) sParallelL)
  have h3: "\<turnstile> \<langle>\<lambda>s. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2'\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    by (metis (mono_tags, lifting) h0' h1 strengthen_pre)
  have h4: "\<turnstile> \<langle>\<lambda>s. \<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2'\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using h3 strengthen_pre by (smt (verit, ccfv_SIG) assms(2) com.inject(7) sParallelR)
  have h5: "\<turnstile> \<langle>\<lambda>s. (\<exists>c\<^sub>1'.  wp_single c\<^sub>1 c\<^sub>1' Q s \<and> c' = c\<^sub>1'||c\<^sub>2) 
            \<or> (\<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2' Q s \<and> c' = c\<^sub>1||c\<^sub>2')\<rangle> c\<^sub>1||c\<^sub>2 \<leadsto> c' \<langle>Q\<rangle>"
    using h2 h4 sDisjunction by auto
  then show ?thesis using wp_single_Par_ER ER by (smt (verit, best) sConseqER)
qed

thm wp_single_Par_ER

thm sParallelL
thm sParallelR
lemma wp_single_is_pre: 
  "\<turnstile> \<langle>wp_single c c' Q\<rangle> c \<leadsto> c' \<langle>Q\<rangle>"
proof(induction c arbitrary: Q c')
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
  then show ?case by (simp add: wp_single_if_is_pre)
next
  case (SelectND x)
  then show ?case apply clarsimp by (metis wp_single_select_is_pre)
next
  case (While x1 c)
  then show ?case
    apply(cases Q)
    using wp_single_While_OK sFalsePre sWhile apply (metis strengthen_pre)
    using wp_single_While_ER sFalsePre by auto
next
  case (Par c1 c2)
  then show ?case by (simp add: par_wp_single_is_pre)
qed


lemma valid_imp_wp_single: "\<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<Longrightarrow>  \<forall>s. P s \<longrightarrow> wp_single c c' Q s"
  unfolding wp_single_def SIL_Single_Step_Valid_def
  apply(cases Q)
by fastforce+

lemma sil_single_step_complete: 
  "\<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle>"
  apply (rule strengthen_pre[where P="wp_single c c' Q"])
  apply (metis valid_imp_wp_single)
by (metis wp_single_is_pre)

corollary sil_single_step_sound_complete: 
  "\<turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle> \<longleftrightarrow> \<Turnstile> \<langle>P\<rangle> c \<leadsto> c'\<langle>Q\<rangle>"
by(fastforce simp: sil_single_step_sound sil_single_step_complete)