(* Author: Tobias Nipkow *)

subsection \<open>Soundness and Completeness\<close>

theory SIL_Big_Step_Complete
imports SIL_Big_Step SIL_Big_Step_Sound SIL_Big_Step_WP
begin

lemma "seq_is_pre":
  assumes c1: "\<forall>R. \<turnstile>\<^sub>b \<langle>wp_big_step c1 R\<rangle> c1  \<langle>R\<rangle>"
  and c2: "\<turnstile>\<^sub>b \<langle>wp_big_step c2 Q\<rangle> c2  \<langle>Q\<rangle>"
  shows "\<turnstile>\<^sub>b \<langle>wp_big_step (c1;; c2) Q\<rangle>
         c1;; c2 \<langle>Q\<rangle>"
proof (cases Q)
  case (OK x)
  have "\<turnstile>\<^sub>b \<langle>wp_big_step c1 (OK (wp_big_step c2 Q))\<rangle> c1  \<langle>OK (wp_big_step c2 Q)\<rangle>"
    by (metis c1)
  then show ?thesis
    using OK c2 by auto
next
  case (ER x)
  have h0: "\<turnstile>\<^sub>b \<langle>wp_big_step c1 (OK (wp_big_step c2 Q))\<rangle> c1  \<langle>OK (wp_big_step c2 Q)\<rangle>"
    by (metis c1)
  have h1: "\<turnstile>\<^sub>b \<langle>wp_big_step c1 (OK (wp_big_step c2 Q))\<rangle> c1;;c2  \<langle>ER x\<rangle>"
    by (metis c2 ER h0 tSeqOK)
  have h2: "\<turnstile>\<^sub>b \<langle>wp_big_step c1 (ER x)\<rangle> c1  \<langle>ER x\<rangle>"
    by (metis c1)
  have h3: "\<turnstile>\<^sub>b \<langle>wp_big_step c1 (ER x)\<rangle> c1;;c2  \<langle>ER x\<rangle>"
    by (metis c1 tSeqER)
  have h4: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (wp_big_step c1 (ER x)) s \<or> wp_big_step c1 (OK (wp_big_step c2 Q)) s\<rangle> c1;;c2  \<langle>ER x\<rangle>"
    by (metis h3 h1 disjunction)
  then show ?thesis
    by (smt (verit) ER strengthen_pre wp_big_step_Seq_ER)
qed



(*(SELECT ?bs, ?s) \<Down> ?t \<Longrightarrow> 
(\<And>b c. (b, c) \<in> set ?bs \<Longrightarrow> 
bval b ?s \<Longrightarrow> (c, ?s) \<Down> ?t \<Longrightarrow> ?P) 
\<Longrightarrow> ?P *)

definition select_pre where
  "select_pre \<equiv> \<lambda>bs Q. (\<lambda>s.(\<exists>t. (SELECT bs, s) \<Down> t \<and> apply_post Q t))"

definition select_pre_er where
  "select_pre_er \<equiv> \<lambda>bs Q. wp_big_step (SelectND bs) Q"

definition select_path_pre_er where
  "select_path_pre_er \<equiv> \<lambda>b c Q. (\<lambda>s. (\<exists>t. (c, s) \<Down> (t,False) \<and> post_assn Q t))"

definition select_path_pre_np where
  "select_path_pre_np  \<equiv> \<lambda>bs Q. (\<lambda>s. \<not>(\<exists>b c. (b,c) \<in> set bs \<and> bval b s) \<and> post_assn Q s)"

definition select_path_pre where
  "select_path_pre \<equiv> \<lambda>b c Q. (\<lambda>s. (\<exists>t. (c, s) \<Down> t \<and> apply_post Q t))"

lemma SelectND_is_pre:
  assumes "\<forall>b c. (b,c) \<in> set bs \<longrightarrow> \<turnstile>\<^sub>b \<langle>wp_big_step c Q\<rangle> c \<langle>Q\<rangle>"
  shows "\<turnstile>\<^sub>b \<langle>wp_big_step (SELECT bs) Q\<rangle> SELECT bs \<langle>Q\<rangle>"
proof(cases Q)
  case (OK x)
    have h3: "\<forall>s. select_pre bs Q s \<longrightarrow> 
        (\<exists>b c. (b,c) \<in> set bs \<and> bval b s \<and> (\<exists>t. (c, s) \<Down> t \<and> apply_post Q t))"
      by (metis OK SelectNDE apply_post.simps(1) select_pre_def)
  
    have h6: "\<forall>bc \<in> set bs. case bc of (b,c) \<Rightarrow> \<turnstile>\<^sub>b \<langle>\<lambda>s. select_path_pre b c Q s \<and> bval b s\<rangle> c \<langle>Q\<rangle>"
      using assms
      unfolding select_path_pre_def wp_big_step_def apply clarsimp
      by (metis (no_types, lifting) strengthen_pre)
  
    hence "\<turnstile>\<^sub>b \<langle>select_pre bs Q\<rangle> SELECT bs \<langle>Q\<rangle>" 
      unfolding select_path_pre_def
      using h3 by (fastforce intro: tSelectND)
  
    thus ?thesis
      by (fastforce simp: wp_big_step_def select_pre_def)
  next
    case (ER x)
    have h3: "\<forall>s. select_pre_er bs Q s \<longrightarrow> (\<exists>(b,c) \<in> set bs. (bval b s) \<and> 
                (\<exists>t. (c, s) \<Down> t \<and> apply_post Q t)) 
                \<or> ((\<forall>(b,c) \<in> set bs. \<not>bval b s) \<and> x s)"
      by (smt (verit, del_insts) ER case_prodE case_prodI select_pre_er_def wp_big_step_SelectND_ER wp_big_step_def)

    have h4: "\<forall>s. select_pre_er bs Q s \<and> (\<exists>(b,c) \<in> set bs. bval b s) \<longrightarrow> (\<exists>(b,c) \<in> set bs. (bval b s) \<and> 
                (\<exists>t. (c, s) \<Down> t \<and> apply_post Q t))"
      using h3 by auto 

    have h4p5: "\<forall>s. select_pre_er bs Q s \<and> \<not> (\<exists>(b,c) \<in> set bs. bval b s) \<longrightarrow> x s"
      using h3 by auto 

    have h5: "\<forall>s. select_pre_er bs Q s \<and> (\<exists>(b,c) \<in> set bs. bval b s) \<longrightarrow> (\<exists>(b,c) \<in> set bs. (bval b s) \<and> 
                (\<exists>t. (c, s) \<Down> (t,False) \<and> post_assn Q t))"
      by (smt (verit, ccfv_threshold) ER apply_post.elims(2) apply_post.simps(2) case_prodE case_prodI h4
          post_assn.simps(2))

    have h6: "\<forall>bc \<in> set bs. case bc of (b,c) \<Rightarrow>
       \<turnstile>\<^sub>b \<langle>\<lambda>s. (select_path_pre_er b c Q s)  \<and> bval b s\<rangle> c \<langle>Q\<rangle>"
      using assms
      unfolding select_path_pre_def wp_big_step_def apply clarsimp
      by (smt (verit) ER apply_post.simps(2) post_assn.simps(2) select_path_pre_er_def
          strengthen_pre)

    hence "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_pre_er bs Q s \<and> (\<exists>(b,c) \<in> set bs. bval b s))\<rangle> SELECT bs \<langle>Q\<rangle>" 
      unfolding select_path_pre_er_def
      using h5 by (fastforce intro: tSelectND)

    have h7: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_path_pre_np bs Q s)\<rangle> SELECT bs \<langle>Q\<rangle>"
      by (smt (verit, ccfv_threshold) ER case_prodI2 post_assn.simps(2) select_path_pre_np_def tSelectNDNP
          weaken_post_er)
    hence "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_pre_er bs Q s \<and> \<not>(\<exists>(b,c) \<in> set bs. bval b s))\<rangle> SELECT bs \<langle>Q\<rangle>" 
      unfolding select_path_pre_er_def
      by (smt (verit) ER case_prod_conv h4p5 post_assn.simps(2) select_path_pre_np_def
          strengthen_pre)

    have h7p5: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_pre_er bs Q s \<and> \<not>(\<exists>(b,c) \<in> set bs. bval b s))\<rangle> SELECT bs \<langle>Q\<rangle>"
      using \<open>\<turnstile>\<^sub>b \<langle>\<lambda>s. select_pre_er bs Q s \<and> \<not> (\<exists>(b, c)\<in>set bs. bval b s)\<rangle> SELECT bs \<langle>Q\<rangle>\<close> by blast

    have h6p5: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_pre_er bs Q s \<and> (\<exists>(b,c) \<in> set bs. bval b s))\<rangle> SELECT bs \<langle>Q\<rangle>"
      using \<open>\<turnstile>\<^sub>b \<langle>\<lambda>s. select_pre_er bs Q s \<and> (\<exists>(b, c)\<in>set bs. bval b s)\<rangle> SELECT bs \<langle>Q\<rangle>\<close> by blast


    have h8: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (select_pre_er bs Q s \<and> (\<exists>(b,c) \<in> set bs. bval b s)) \<or> (select_pre_er bs Q s \<and> \<not>(\<exists>(b,c) \<in> set bs. bval b s))\<rangle> 
        SELECT bs \<langle>Q\<rangle>"
      using disjunction h6p5 h7p5 by blast

    have h9: "\<turnstile>\<^sub>b \<langle>select_pre_er bs Q \<rangle> 
        SELECT bs \<langle>Q\<rangle>"
      by (metis (no_types, lifting) h8 strengthen_pre)

    thus ?thesis
      by (metis h9 select_pre_er_def)
qed

primrec QQ ::
  "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"
where
  "QQ R b c 0 = (\<lambda>s. R s \<and> \<not> bval b s)"
| "QQ R b c (Suc n) = (\<lambda>s. wp_big_step c (OK (QQ R b c n)) s \<and> bval b s)"

primrec QQ_er_1 ::
  "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"
  where
  "QQ_er_1 R b c 0 = (\<lambda>s. wp_big_step c (ER R) s \<and> bval b s)"
| "QQ_er_1 R b c (Suc n) = (\<lambda>s. wp_big_step c (OK (QQ_er_1 R b c n)) s \<and> bval b s)"

primrec QQ_er ::
  "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"
  where
  "QQ_er R b c 0 = R"
| "QQ_er R b c (Suc n) = QQ_er_1 R b c n"


lemma While_Strengthen:
  assumes exec: "(WHILE b DO c, s) \<Down> t"
  and post: "apply_post (OK Q) t"
  shows "\<exists>n. (QQ Q b c) n  s"
  using exec post
proof (induction "(WHILE b DO c, s)" t arbitrary: Q s rule: big_step.induct)
  case  WhileGuardFalse then show ?case
    by (meson QQ.simps(1) apply_post.simps(1))
  next 
  case (WhileBodySucceeds s1 s2 s3) 
      then obtain n where hn: "QQ Q b c n s2"
        by blast
      then have h0: "QQ Q b c n s2"
        by simp
      then have h1: "wp_big_step c (OK (QQ Q b c n)) s1"
        unfolding wp_big_step_def
      proof-
        show "\<exists>t. (c, s1) \<Down> t \<and> apply_post (OK (QQ Q b c n)) t"
          using WhileBodySucceeds.hyps(2) hn by auto
      qed
    then have h2: "wp_big_step c (OK (QQ Q b c n)) s1 \<and> bval b s1"
      by (metis h1 WhileBodySucceeds.hyps(1))    
    show "\<exists>n. QQ Q b c n s1"
        proof (rule exI[where x="Suc n"])
          show "QQ Q b c (Suc n) s1"
            by (simp add: h2)
        qed
   next
     case (WhileBodyAborts s1 s2)
     then obtain n where hn: "QQ Q b c n s2"
       by force
      then have h0: "QQ Q b c n s2"
        by simp
      then have h1: "wp_big_step c (ER (QQ Q b c n)) s1"
        unfolding wp_big_step_def
      proof-
        show "\<exists>t. (c, s1) \<Down> t \<and> apply_post (ER (QQ Q b c n)) t"
          using WhileBodyAborts.prems by auto
      qed
    then have h2: "wp_big_step c (ER (QQ Q b c n)) s1 \<and> bval b s1"
      by (metis h1 WhileBodyAborts.hyps(1))
    show "\<exists>n. QQ Q b c n s1"
        proof (rule exI[where x="Suc n"])
            show "QQ Q b c (Suc n) s1"
              using WhileBodyAborts.prems by auto
          qed
qed

lemma While_Strengthen_ER:
  assumes exec: "(WHILE b DO c, s) \<Down> t"
  and post: "apply_post (ER Q) t"
  shows "\<exists>n. (QQ_er Q b c) (Suc n) s"
  using exec post
  apply (induction "(WHILE b DO c, s)" t arbitrary: Q s rule: big_step.induct)
    apply simp
   defer
   apply clarsimp
   apply (metis QQ_er_1.simps(1) apply_post.simps(2) wp_big_step_def)
  apply clarsimp
proof-
  fix s\<^sub>1 s\<^sub>2 a Q
  assume bval: "bval b s\<^sub>1"
     and c_step: "(c, s\<^sub>1) \<Down> (s\<^sub>2, True)"
     and while_step: "(WHILE b DO c, s\<^sub>2) \<Down> (a, False)"
     and IH: "\<And>Q. Q a \<Longrightarrow> \<exists>n. QQ_er_1 Q b c n s\<^sub>2"
     and Qa: "Q a"

  obtain n where hn: "QQ_er_1 Q b c n s\<^sub>2"
    by (metis Qa IH)
  then have h0: "QQ_er_1 Q b c n s\<^sub>2"
    by simp
  then have h1: "wp_big_step c (OK (QQ_er_1 Q b c n)) s\<^sub>1"
    unfolding wp_big_step_def
    using c_step by auto
  then have h2: "wp_big_step c (OK (QQ_er_1 Q b c n)) s\<^sub>1 \<and> bval b s\<^sub>1"
    by (metis h1 bval)
  show "\<exists>n. QQ_er_1 Q b c n s\<^sub>1"
    by (meson QQ_er_1.simps(2) h2)
qed

lemma While_is_pre_ok:
  assumes "\<forall>Q. \<turnstile>\<^sub>b \<langle>wp_big_step c (OK Q)\<rangle> c  \<langle>OK Q\<rangle>"
  shows "\<turnstile>\<^sub>b \<langle>wp_big_step (WHILE b DO c) (OK Q)\<rangle> (WHILE b DO c) \<langle>(OK Q)\<rangle>"
  unfolding wp_big_step_def  
proof- 
  fix n
  have h1: "\<turnstile>\<^sub>b \<langle>wp_big_step c (OK (QQ Q b c n))\<rangle> c  \<langle>OK (QQ Q b c n)\<rangle>"
    by (metis assms)
  have h2: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (wp_big_step c (OK (QQ Q b c n)) s \<and> bval b s)\<rangle> c  \<langle>OK (QQ Q b c n)\<rangle>"
    by (smt (verit, best) conseqOK h1)
  have h3: "\<turnstile>\<^sub>b \<langle>(QQ Q b c (Suc n))\<rangle> c  \<langle>OK (QQ Q b c n)\<rangle>"
    by (simp add: h2)
  have h4: "\<And>n::nat. \<turnstile>\<^sub>b \<langle>(QQ Q b c) (Suc n)\<rangle> c  \<langle>OK ((QQ  Q b c) n)\<rangle>"
    by (metis QQ.simps(2) assms strengthen_pre)
  have h5: "\<And>s. (QQ Q b c) 0 s \<Longrightarrow> \<not> bval b s"
    by simp
  have h6: "\<And>n s. (QQ Q b c) (Suc n) s \<Longrightarrow> bval b s"
    by simp
  have h7: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>n. (QQ Q b c) n  s\<rangle> WHILE b DO c \<langle>OK (\<lambda>s. (QQ Q b c) 0 s)\<rangle>"
    using QQ_def
    by (smt (verit, best) conseqOK h4 h5 h6 tWhileOK)
  have h8: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>n. (QQ Q b c) n  s\<rangle> WHILE b DO c \<langle>OK Q\<rangle>"
    using QQ.simps(1) h7 weaken_post_ok by presburger
  have h9: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>t. (WHILE b DO c, s) \<Down> t \<and> apply_post (OK Q) t\<rangle> WHILE b DO c \<langle>OK Q\<rangle>"
    by (smt (verit, best) While_Strengthen conseqOK h8)
  show "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>t. (WHILE b DO c, s) \<Down> t \<and> apply_post (OK Q) t\<rangle> WHILE b DO c \<langle>OK Q\<rangle>"
    by (metis h9)
qed

lemma While_is_pre_er:
  assumes "\<forall>Q. \<turnstile>\<^sub>b \<langle>wp_big_step c Q\<rangle> c  \<langle>Q\<rangle>"
  shows "\<turnstile>\<^sub>b \<langle>wp_big_step (WHILE b DO c) (ER Q)\<rangle> (WHILE b DO c) \<langle>(ER Q)\<rangle>"
  unfolding wp_big_step_def
  apply clarsimp 
proof-
  have h0: "\<exists>a ba. (WHILE b DO c, s) \<Down> (a, ba) \<and> Q a \<and> \<not> ba 
              \<longleftrightarrow> 
            (\<exists>a. (WHILE b DO c, s) \<Down> (a, False) \<and> Q a)"
    by blast
  fix n
  have h0: "\<turnstile>\<^sub>b \<langle>wp_big_step c (ER (QQ_er Q b c 0))\<rangle> c  \<langle>ER (QQ_er Q b c 0)\<rangle>"
    by (metis assms)
  have h1: "\<turnstile>\<^sub>b \<langle>wp_big_step c (OK (QQ_er Q b c (Suc n)))\<rangle> c  \<langle>OK (QQ_er Q b c (Suc n))\<rangle>"
    by (metis assms)
  have h2: "\<turnstile>\<^sub>b \<langle>\<lambda>s. (wp_big_step c (OK (QQ_er Q b c (Suc n))) s \<and> bval b s)\<rangle> c  \<langle>OK (QQ_er Q b c (Suc n))\<rangle>"
    by (metis (no_types, lifting) assms strengthen_pre_ok)
  have h3: "\<turnstile>\<^sub>b \<langle>(QQ_er Q b c (Suc (Suc n)))\<rangle> c  \<langle>OK (QQ_er Q b c (Suc n))\<rangle>"
    using h2 by auto
  have h4: "\<And>n::nat. \<turnstile>\<^sub>b \<langle>(QQ_er Q b c) (Suc (Suc n))\<rangle> c  \<langle>OK ((QQ_er Q b c) (Suc n))\<rangle>"
    by (metis QQ_er.simps(2) QQ_er_1.simps(2) assms strengthen_pre_ok)
  have h5: "\<turnstile>\<^sub>b \<langle>QQ_er Q b c 1\<rangle> c  \<langle>ER (QQ_er Q b c 0)\<rangle>"
    by (metis One_nat_def QQ_er.simps(1,2) QQ_er_1.simps(1) assms strengthen_pre_er)
  have h6: "\<And>n s. (QQ_er Q b c) (Suc n) s \<Longrightarrow> bval b s"
    by (metis QQ_er.simps(2) QQ_er_1.simps(1,2) old.nat.exhaust)
  have h7: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>n. (QQ_er Q b c) (Suc n)  s\<rangle> WHILE b DO c \<langle>ER (\<lambda>s. (QQ_er Q b c) 0 s)\<rangle>"
    using h4 h5 h6 tWhileER by blast
  have h8: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>n. (QQ_er Q b c) (Suc n)  s\<rangle> WHILE b DO c \<langle>ER Q\<rangle>"
    using h7 by auto
  have h9: "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>t. (WHILE b DO c, s) \<Down> (t,False) \<and> Q t\<rangle> WHILE b DO c \<langle>ER Q\<rangle>"
    by (smt (verit, ccfv_threshold) While_Strengthen_ER apply_post.simps(2) h8 strengthen_pre)
  show "\<turnstile>\<^sub>b \<langle>\<lambda>s. \<exists>a ba. (WHILE b DO c, s) \<Down> (a, ba) \<and> Q a \<and> \<not> ba\<rangle>
            WHILE b DO c  
          \<langle>ER Q\<rangle> " 
    by (smt (verit, ccfv_SIG) conseqER h9)
qed


lemma wp_big_step_is_pre: "isSequential c \<Longrightarrow> \<turnstile>\<^sub>b \<langle>wp_big_step c Q\<rangle> c \<langle>Q\<rangle>"
  proof(induction c arbitrary: Q)
    case SKIP
    then show ?case
      by (metis false_pre post_assn.elims strengthen_pre tSkip wp_big_step_SKIP_ER wp_big_step_SKIP_OK)
  next
    case ABORT
    then show ?case
      by (metis false_pre post_assn.elims strengthen_pre tAbort wp_big_step_ABORT_ER wp_big_step_ABORT_OK)
  next
    case (Assign x1 x2)
    then show ?case 
      apply (cases Q)
      apply simp
    by (metis wp_big_step_Assign_ER strengthen_pre_er false_pre)
  next
    case (AssignND x1 x2)
    then show ?case 
      apply (cases Q)
      apply clarsimp
      apply (smt (verit, best) strengthen_pre_ok tAssignNDOK wp_big_step_AssignND_Empty_OK
          wp_big_step_AssignND_NonEmpty_OK)
      by (metis false_pre wp_big_step_AssignND_Empty_ER wp_big_step_AssignND_NonEmpty_ER strengthen_pre tAssignNDER)
  next
    case (Seq c1 c2)
    then show ?case by (simp add: seq_is_pre)
  next
    case (If x1 c1 c2)
    then show ?case
      by (smt (verit, best) isSequential.simps(3) strengthen_pre tIf wp_big_step_If)
  next
    case (SelectND x)
    then show ?case
      using SelectND_is_pre by fastforce
  next
    case (While x1 c)
    then show ?case
      apply (cases Q)
      apply clarsimp
       apply (metis While_is_pre_ok)
      using While_is_pre_er by simp
  next
    case (Par c1 c2)
    then show ?case
      by simp
qed

lemma valid_imp_wp_big_step: 
  assumes "isSequential c"
  shows "\<Turnstile> \<langle>P\<rangle> c  \<langle>Q\<rangle> \<Longrightarrow> \<forall>s. P s \<longrightarrow> wp_big_step c Q s"
  unfolding wp_big_step_def SIL_valid_def
  apply(cases Q)
  apply fastforce
by fastforce

lemma sil_complete: 
  assumes "isSequential c"
  shows "\<Turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<Longrightarrow> \<turnstile>\<^sub>b \<langle>P\<rangle> c \<langle>Q\<rangle>"
  apply (rule strengthen_pre[where P="wp_big_step c Q"])
  apply (metis assms valid_imp_wp_big_step)
by (metis assms wp_big_step_is_pre)


lemma sil_sound_complete: 
  assumes "isSequential c"
  shows "\<turnstile>\<^sub>b \<langle>P\<rangle>c\<langle>Q\<rangle> \<longleftrightarrow> \<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>"
by (metis assms sil_sound sil_complete)

end
