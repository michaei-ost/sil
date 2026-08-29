subsection \<open>Soundness and Completeness\<close>

theory SIL_Star_Sound
imports SIL_Star SIL_Single_Step_Sound
begin

subsubsection "Soundness"

lemma sil_while_sound_ok:
assumes "\<And>n. \<turnstile> \<langle>Q (Suc n)\<rangle> c  \<langle>OK (Q n)\<rangle>"
      and "\<And>s. Q 0 s \<Longrightarrow> \<not> bval b s"
      and "\<And>n s. Q (Suc n) s \<Longrightarrow>  bval b s"
      and "Q n s"
      and "\<And>n. \<forall>s. Q (Suc n) s \<longrightarrow> (\<exists>t. (c, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q n t)"
    shows "(\<exists>t. (WHILE b DO c, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q 0 t)"
  using assms
  apply (induct n arbitrary: s)
   apply (metis While small_step.IfFalse star.simps)
  by (smt (verit, ccfv_threshold) Small_Step.WhileE Small_Step.sPost.distinct(1)
      com.distinct(13) final_def final_iff_SKIP seq_comp_sOK small_step.IfTrue star.step)

lemma sil_while_sound_er:
  assumes "\<And>n. \<turnstile> \<langle>Q (Suc (Suc n))\<rangle> c \<langle>OK (Q (Suc n))\<rangle>"
  and "\<turnstile> \<langle>Q 1\<rangle> c \<langle>ER (Q 0)\<rangle>"
  and "\<And>s. Q 1 s \<Longrightarrow> (\<exists>t. (c, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q 0 t)"
  and "\<And>n s. Q (Suc n) s \<Longrightarrow> bval b s"
  and "Q (Suc m) s"
  and "\<And>n. \<forall>s. Q (Suc (Suc n)) s \<longrightarrow> (\<exists>t. (c, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q (Suc n) t)"
  shows "\<exists>t. (WHILE b DO c, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q 0 t"
  using assms
  apply (induct m arbitrary: s)
  apply (smt (verit) One_nat_def Small_Step.IfE Small_Step.WhileE Small_Step.sPost.distinct(1)
      com.distinct(13,9) final_def final_iff_SKIP post_state.simps(1) seq_comp_sER star.simps)
  apply clarsimp
  by (smt (verit, del_insts) Small_Step.WhileE Small_Step.sPost.distinct(1) com.distinct(13)
      com.size_gen(2) final_def final_iff_SKIP seq_comp_sOK small_step.IfTrue star.simps
      star.step)

lemma sil_parL_sound_ok:
  assumes h0: "c\<^sub>2 \<noteq> SKIP"
  assumes h1: "\<turnstile> \<langle>P\<rangle> c\<^sub>1 \<leadsto> c\<^sub>1' \<langle>OK P'\<rangle>"
  assumes h2: "\<turnstile> \<langle>P'\<rangle> c\<^sub>1' || c\<^sub>2 \<langle>Q\<rangle>"
  assumes h3: "case Q of
                 OK Q' \<Rightarrow> \<forall>s. P' s \<longrightarrow> (\<exists>t. (c\<^sub>1' || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q' t)
               | ER Q' \<Rightarrow> \<forall>s. P' s \<longrightarrow> (\<exists>t. (c\<^sub>1' || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q' t)"
  shows "case Q of
           OK Q' \<Rightarrow> \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q' t)
         | ER Q' \<Rightarrow> \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q' t)"
proof (cases Q)
  case (OK x)
  have " \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1' || c\<^sub>2, sOK t) \<and> P' t)"
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce
  then show ?thesis
    by (smt (verit, best) OK h3 post.simps(5) star.step)
next
  case (ER x)
  have " \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1' || c\<^sub>2, sOK t) \<and> P' t)"
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce
  then show ?thesis
    by (smt (verit, best) ER h3 post.simps(6) star.step)
qed

lemma sil_parR_sound_ok:
  assumes h0: "c\<^sub>1 \<noteq> SKIP"
  assumes h1: "\<turnstile> \<langle>P\<rangle> c\<^sub>2 \<leadsto> c\<^sub>2' \<langle>OK P'\<rangle>"
  assumes h2: "\<turnstile> \<langle>P'\<rangle> c\<^sub>1 || c\<^sub>2' \<langle>Q\<rangle>"
  assumes h3: "case Q of
                 OK Q' \<Rightarrow> \<forall>s. P' s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2', sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q' t)
               | ER Q' \<Rightarrow> \<forall>s. P' s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2', sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q' t)"
  shows "case Q of
           OK Q' \<Rightarrow> \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK t) \<and> Q' t)
         | ER Q' \<Rightarrow> \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q' t)"
proof (cases Q)
  case (OK x)
  have " \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1 || c\<^sub>2', sOK t) \<and> P' t)"
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce
  then show ?thesis
    by (smt (verit, best) OK h3 post.simps(5) star.step)
next
  case (ER x)
  have " \<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1 || c\<^sub>2', sOK t) \<and> P' t)"
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce
  then show ?thesis
    by (smt (verit, best) ER h3 post.simps(6) star.step)
qed

lemma sParL_sound_er:
  assumes h0: "c\<^sub>2 \<noteq> SKIP"
  assumes h1: "\<turnstile> \<langle>P\<rangle> c\<^sub>1 \<leadsto> c\<^sub>1' \<langle>ER Q\<rangle>"
  shows "\<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q t)"
proof-
  have h0: "\<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1' || c\<^sub>2, sER t) \<and> Q t)" 
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce 
  then show ?thesis  by (metis Er star.simps)
qed

lemma sParR_sound_er:
  assumes h0: "c\<^sub>1 \<noteq> SKIP"
  assumes h1: "\<turnstile> \<langle>P\<rangle> c\<^sub>2 \<leadsto> c\<^sub>2' \<langle>ER Q\<rangle>"
  shows "\<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER t) \<and> Q t)"
proof-
  have h0: "\<forall>s. P s \<longrightarrow> (\<exists>t. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1 || c\<^sub>2', sER t) \<and> Q t)" 
    using SIL_Single_Step_Valid_def h0 h1 sil_single_step_sound by fastforce 
  then show ?thesis  by (metis Er star.simps)
qed


lemma sil_star_sound: 
  "\<turnstile> \<langle>P\<rangle> c \<langle>R\<rangle>  \<Longrightarrow>  \<Turnstile> \<langle>P\<rangle> c \<langle>R\<rangle>"
  unfolding SIL_Star_Valid_def
  apply (induction rule:SIL_Star.induct)
                      apply fastforce
                      apply fastforce
                     apply fastforce
                    apply fastforce
                   apply clarsimp
                   defer
  apply (case_tac R)
                    apply clarsimp
  using seq_comp_sOK apply blast
                   apply clarsimp
                   apply (metis seq_comp_sOK)
                  apply clarsimp
                  apply (metis seq_comp_sER)
                 apply (case_tac R)
  apply clarsimp
                  apply (metis small_step.IfFalse small_step.IfTrue star.step)
                 apply (case_tac R)
                  apply clarsimp
                 apply clarsimp
                 apply (metis small_step.IfFalse small_step.IfTrue star.step)
                apply (case_tac Q)
                 apply clarsimp
    defer
                 apply (case_tac Q)
                  apply clarsimp
                 apply clarsimp
                 defer
                 apply clarsimp
                 apply (metis SelectNDN small_step.Abort star.simps)
                apply clarsimp
                defer
                apply clarsimp
                defer
  apply fastforce
               apply fastforce
              apply (case_tac Q)
               apply fastforce
              apply fastforce
             apply (case_tac Q)
              apply fastforce
             apply fastforce
            defer
            defer
            defer
            defer
            apply (case_tac Q)
             apply clarsimp
             apply (metis ParSkipL star.step)
            apply clarsimp
            apply (meson ParSkipL star.step)
            apply (case_tac Q)
             apply clarsimp
             apply (metis ParSkipR star.step)
            apply clarsimp
           apply (meson ParSkipR star.step)
          apply (meson small_step.Abort small_step.AssignNDEmpty star.step star_step1)
         apply (smt (verit) case_prodD small_step.SelectND star.step)
        apply (smt (verit, best) case_prod_conv small_step.SelectND star.step)
       apply (simp add: sil_while_sound_ok)
      apply (smt (verit, ccfv_threshold) One_nat_def sil_while_sound_er)
     apply (simp add: sil_parL_sound_ok)
    apply (simp add: sil_parR_sound_ok)
   apply clarsimp 
   apply (metis sParL_sound_er)
  by (simp add: sParR_sound_er)
  
end

                




