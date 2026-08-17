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
  by fastforce

definition wp_single :: "com \<Rightarrow> com \<Rightarrow> post \<Rightarrow> assn" where
  "wp_single c1 c2 R = (\<lambda>s. case R of
      OK Q \<Rightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sOK s') \<and> Q s')
    | ER Q \<Rightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sER s') \<and> Q s'))"


lemma wp_single_ABORT: "wp_single ABORT SKIP R = (case R of
      OK Q \<Rightarrow> (\<lambda>s. False)
    | ER Q \<Rightarrow> Q)" 
  apply (case_tac R)
   apply clarsimp
  unfolding wp_single_def apply fastforce
  apply clarsimp
  unfolding wp_single_def apply fastforce
  done
