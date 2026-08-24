subsection \<open>Soundness and Completeness\<close>

theory SIL_Single_Step_Sound
imports SIL_Single_Step
begin

subsubsection "Soundness"

lemma sil_single_step_sound: 
  "\<turnstile> \<langle>P\<rangle>c \<leadsto> c'\<langle>R\<rangle>  \<Longrightarrow>  \<Turnstile> \<langle>P\<rangle>c \<leadsto> c'\<langle>R\<rangle>"
  unfolding SIL_Single_Step_Valid_def
  apply (induction rule:SIL_Single_Step.induct; fastforce?)
            apply (case_tac R)
            apply (clarsimp)
            apply fastforce
           apply fastforce
          apply (case_tac Q)
       apply clarsimp
      apply fastforce
            apply (case_tac Q)
            apply clarsimp
          apply fastforce
         apply (case_tac Q)
         apply clarsimp
         apply fastforce
        apply (case_tac R)
        apply clarsimp
        apply fastforce
       apply clarsimp
       apply fastforce
      apply (case_tac R)
      apply clarsimp
      apply fastforce
  by fastforce

end