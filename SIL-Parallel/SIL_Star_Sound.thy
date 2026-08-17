subsection \<open>Soundness and Completeness\<close>

theory SIL_Star_Sound
imports SIL_Star
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
  by (smt (verit, ccfv_threshold) Small_Step.WhileE Small_Step.post.distinct(1)
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
  apply (smt (verit) One_nat_def Small_Step.IfE Small_Step.WhileE Small_Step.post.distinct(1)
      com.distinct(13,9) final_def final_iff_SKIP post_state.simps(1) seq_comp_sER star.simps)
  apply clarsimp
  sorry




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
  sledgehammer
  


                




