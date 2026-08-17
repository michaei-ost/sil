subsection \<open>Soundness and Completeness\<close>

theory SIL_Single_Step_WP
imports SIL_Single_Step
begin

definition wp_single :: "com \<Rightarrow> com \<Rightarrow> post \<Rightarrow> assn" where
  "wp_single c1 c2 R = (\<lambda>s. case R of
      OK Q \<Rightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sOK s') \<and> Q s')
    | ER Q \<Rightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sER s') \<and> Q s'))"


lemma wp_single_SKIP_OK: "wp_single SKIP c' (OK Q) =(\<lambda>s. False)"
  unfolding wp_single_def by fastforce

lemma wp_single_SKIP_ER: "wp_single SKIP c' (ER Q) =(\<lambda>s. False)"
  unfolding wp_single_def by fastforce

lemma wp_single_ABORT_OK: "wp_single ABORT c' (OK Q) =(\<lambda>s. False)"
  unfolding wp_single_def by fastforce

lemma wp_single_ABORT_ER: "wp_single ABORT c' (ER Q) = (\<lambda>s. c' = SKIP \<and> Q s)"
  unfolding wp_single_def by fastforce

lemma wp_single_Assign_OK: "wp_single (x ::= a) c' (OK Q) = 
  (\<lambda>s. c' = SKIP \<and> Q(s(x := aval a s)))"
  unfolding wp_single_def by fastforce

lemma wp_single_Assign_ER: "wp_single (x ::= a) c' (ER Q) =(\<lambda>s. False)"
  unfolding wp_single_def by fastforce

lemma wp_single_AssignND_OK: "A \<noteq> {} \<Longrightarrow> wp_single (x ::= ND A) c' (OK Q) = 
  (\<lambda>s. c' = SKIP \<and> (\<exists>a \<in> A. Q(s(x := aval a s))))"
  unfolding wp_single_def by fastforce

lemma wp_single_AssignND_Empty_OK: "wp_single (x ::= ND {}) c' (OK Q) = 
  (\<lambda>s. c' = ABORT \<and> Q s)"
  unfolding wp_single_def by fastforce

lemma wp_single_AssignND_ER: "wp_single (x ::= ND A) c' (ER Q) = (\<lambda>s. False)"
  unfolding wp_single_def by fastforce