
theory SIL_Big_Step_WP
imports SIL_Big_Step
begin

subsubsection "Weakest Precondition"

definition wp_big_step :: "com \<Rightarrow> post \<Rightarrow> assn" where
  "wp_big_step c Q = (\<lambda>s. \<exists>t. (c,s) \<Down> t \<and> apply_post Q t)"

lemma wp_big_step_SKIP_OK [simp]: 
  "wp_big_step SKIP (OK Q) = Q"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_SKIP_ER [simp]: 
  "wp_big_step SKIP (ER Q) = (\<lambda>s. False)"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_ABORT_ER [simp]: 
  "wp_big_step ABORT (ER Q) = Q"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_ABORT_OK [simp]: 
  "wp_big_step ABORT (OK Q) = (\<lambda>s. False)"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_Assign_OK [simp]: 
  "wp_big_step (x::=a) (OK Q) = (\<lambda>s. Q(s[a/x]))"
  by (fastforce simp: wp_big_step_def)

lemma wp_big_step_Assign_ER [simp]: 
  "wp_big_step (x::=a) (ER Q) = (\<lambda>s. False)"
  using wp_big_step_def by fastforce

lemma wp_big_step_AssignND_NonEmpty_OK [simp]: 
  "vals \<noteq> {} \<Longrightarrow> wp_big_step (x::= ND vals) (OK Q) = (\<lambda>s. (\<exists>v \<in> vals. Q (s(x := aval v s))))"
  by (fastforce simp: wp_big_step_def)

lemma wp_big_step_AssignND_NonEmpty_ER [simp]: 
  "vals \<noteq> {} \<Longrightarrow> wp_big_step (x::= ND vals) (ER Q) = (\<lambda>s. False)"
  by (fastforce simp: wp_big_step_def)

lemma wp_big_step_AssignND_Empty_ER [simp]: 
  "vals = {} \<Longrightarrow> wp_big_step (x::= ND vals) (ER Q) = Q"
  unfolding wp_big_step_def
  by auto

lemma wp_big_step_AssignND_Empty_OK [simp]: 
  "vals = {} \<Longrightarrow> wp_big_step (x::= ND vals) (OK Q) = (\<lambda>s. False)"
  unfolding wp_big_step_def
  by auto

lemma wp_big_step_SelectND_OK[simp]: 
  "wp_big_step (SelectND S) (OK Q) = (\<lambda>s. \<exists>(b,c) \<in> set S. (bval b s) \<and> (wp_big_step c (OK Q) s))"
  by (fastforce simp: wp_big_step_def)

lemma wp_big_step_SelectND_ER[simp]: 
  "wp_big_step (SelectND S) (ER Q) = 
    (\<lambda>s. (\<exists>(b,c) \<in> set S. (bval b s) \<and> (wp_big_step c (ER Q) s)) 
                \<or> ((\<forall>(b,c) \<in> set S. \<not>bval b s) \<and> Q s))"
  apply (rule ext)
  apply (simp add: wp_big_step_def)
  apply (rule iffI)
  apply clarsimp
  apply blast
  by blast

lemma wp_big_step_Seq_OK[simp]: 
  "wp_big_step (c\<^sub>1;;c\<^sub>2) (OK Q) = wp_big_step c\<^sub>1 (OK (wp_big_step c\<^sub>2 (OK Q)))"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_Seq_ER[simp]: 
  "wp_big_step (c\<^sub>1;;c\<^sub>2) (ER Q) = (\<lambda>s. wp_big_step c\<^sub>1 (OK (wp_big_step c\<^sub>2 (ER Q))) s \<or> wp_big_step c\<^sub>1 (ER Q) s )"
  by (rule ext) (fastforce simp: wp_big_step_def)

lemma wp_big_step_If[simp]:
 "wp_big_step (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. if bval b s then wp_big_step c\<^sub>1 Q s else wp_big_step c\<^sub>2 Q s)"
  by (rule ext) (auto simp: wp_big_step_def)

lemma wp_big_step_While_If:
 "wp_big_step (WHILE b DO c) Q s = wp_big_step (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
  unfolding wp_big_step_def by blast

lemma wp_big_step_While_True[simp]: 
  "bval b s \<Longrightarrow> wp_big_step (WHILE b DO c) Q s = wp_big_step (c;; WHILE b DO c) Q s"
  by(fastforce simp: wp_big_step_While_If)

lemma wp_big_step_While_False_OK[simp]: 
  "\<not> bval b s \<Longrightarrow> wp_big_step (WHILE b DO c) (OK Q) s  = Q s"
  by (simp add: wp_big_step_While_If)

lemma wp_big_step_While_False_ER[simp]: 
  "\<not> bval b s \<Longrightarrow> wp_big_step (WHILE b DO c) (ER Q) s  = False"
  by (simp add: wp_big_step_While_If)

end