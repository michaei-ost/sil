(* Author: Tobias Nipkow *)

subsection \<open>Soundness and Completeness\<close>

theory SIL_Sound_Complete
imports SIL
begin

subsubsection "Soundness"

lemma sil_while_sound:
  assumes "\<And>n. \<turnstile> \<langle>Q (Suc n)\<rangle> c  \<langle>Q n\<rangle>"
      and "\<And>n. \<forall>s. Q (Suc n) s \<longrightarrow> (\<exists>t. (c, s) \<Down> t \<and> Q n t)"
      and "\<And>s. Q 0 s \<Longrightarrow> \<not> bval b s"
      and "\<And>n s. Q (Suc n) s \<Longrightarrow>  bval b s"
      and "Q n s"
    shows "\<exists>t. (WHILE b DO c, s) \<Down> t \<and> Q 0 t"
  using assms
  apply (induct n arbitrary: s rule: Nat.nat_less_induct, clarsimp)
  by (metis WhileFalse WhileTrue lessI not0_implies_Suc)

lemma sil_sound: 
  "\<turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>  \<Longrightarrow>  \<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>"
  unfolding SIL_valid_def
  apply (induction rule: SIL.induct; blast?)
  using sil_while_sound by blast


subsubsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
  "wp c Q = (\<lambda>s. \<exists>t. (c,s) \<Down> t \<and>  Q t)"

lemma wp_SKIP [simp]: 
  "wp SKIP Q = Q"
  by (rule ext) (fastforce simp: wp_def)

lemma wp_Ass [simp]: 
  "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
  by (fastforce simp: wp_def)

lemma wp_AssND [simp]: 
  "wp (x::= ND vals) Q = (\<lambda>s. (\<exists>v \<in> vals. Q (s(x := aval v s))))"
  sledgehammer
  by (fastforce simp: wp_def)

lemma wp_SelectND[simp]: 
  "wp (SelectND S) Q = (\<lambda>s. \<exists>(b,c) \<in> set S. (bval b s) \<and> (wp c Q s))"
  by (fastforce simp: wp_def)

lemma wp_Seq[simp]: 
  "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
  by (rule ext) (fastforce simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
  by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s = wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
  unfolding wp_def by blast

lemma wp_While_True[simp]: 
  "bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
  by(fastforce simp: wp_While_If)

lemma wp_While_False[simp]: 
  "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
  by(fastforce simp: wp_While_If)


subsubsection "Completeness"

primrec QQ ::
  "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"
where
  "QQ R b c 0 = (\<lambda>s. R s \<and> \<not> bval b s)"
| "QQ R b c (Suc n) = (\<lambda>s. wp c (QQ R b c n) s \<and> bval b s)"


lemma While_Strengthen:
  assumes exec: "(WHILE b DO c, s) \<Down> t"
  and post: "Q t"
  shows "\<exists>n. (QQ Q b c) n  s"
  using exec post
proof (induction "(WHILE b DO c, s)" t arbitrary: Q s rule: big_step.induct)
  case  WhileFalse then show ?case
    by (meson QQ.simps(1))
    next 
      case (WhileTrue s1 s2 s3) 
      then obtain n where hn: "QQ Q b c n s2"
        using WhileTrue.hyps(2) WhileTrue.prems
        by presburger
      then have h0: "QQ Q b c n s2"
        by simp
      then have h1: "wp c (QQ Q b c n) s1"
        unfolding wp_def
      proof-
        show "\<exists>t. (c, s1) \<Down> t \<and> QQ Q b c n t"
        proof (rule exI[where x=s2])
          show "(c, s1) \<Down> s2 \<and> QQ Q b c n s2"
          using assms
          by (simp add: WhileTrue.hyps(2) hn)
      qed
    qed
    then have h2: "wp c (QQ Q b c n) s1 \<and> bval b s1"
      by (metis h1 WhileTrue.hyps(1))      
    show "\<exists>n. QQ Q b c n s1"
        proof (rule exI[where x="Suc n"])
          show "QQ Q b c (Suc n) s1"
            by (simp add: h2)
        qed
    qed
        

lemma While_is_pre:
  assumes "(\<forall>Q. \<turnstile> \<langle>wp c Q\<rangle> c  \<langle>Q\<rangle>)"
  shows "\<turnstile> \<langle>wp (WHILE b DO c) Q\<rangle> (WHILE b DO c) \<langle>Q\<rangle>"
  unfolding wp_def  
proof- 
  fix n
  have h1: "\<turnstile> \<langle>wp c (QQ Q b c n)\<rangle> c  \<langle>QQ Q b c n\<rangle>"
    by (metis assms)
  have h2: "\<turnstile> \<langle>\<lambda>s. (wp c (QQ Q b c n) s \<and> bval b s)\<rangle> c  \<langle>QQ Q b c n\<rangle>"
    by (smt (verit, ccfv_SIG) conseq h1)
  have h3: "\<turnstile> \<langle>(QQ Q b c (Suc n))\<rangle> c  \<langle>QQ Q b c n\<rangle>"
    by (simp add: h2)
  have h4: "\<And>n::nat. \<turnstile> \<langle>(QQ Q b c) (Suc n)\<rangle> c  \<langle>(QQ  Q b c) n\<rangle>"
    by (metis QQ.simps(2) assms strengthen_pre)
  have h5: "\<And>s. (QQ Q b c) 0 s \<Longrightarrow> \<not> bval b s"
    by simp
  have h6: "\<And>n s. (QQ Q b c) (Suc n) s \<Longrightarrow> bval b s"
    by simp
  have h7: "\<turnstile> \<langle>\<lambda>s. \<exists>n. (QQ Q b c) n  s\<rangle> WHILE b DO c \<langle>\<lambda>s. (QQ Q b c) 0 s\<rangle>"
    using QQ_def
    by (smt (verit, best) conseq h4 h5 h6 tWhile)
  have h8: "\<turnstile> \<langle>\<lambda>s. \<exists>n. (QQ Q b c) n  s\<rangle> WHILE b DO c \<langle>Q\<rangle>"
    using QQ.simps(1) h7 weaken_post by presburger
  have h9: "\<turnstile> \<langle>\<lambda>s. \<exists>t. (WHILE b DO c, s) \<Down> t \<and> Q t\<rangle> WHILE b DO c \<langle>Q\<rangle>"
    by (smt (verit, best) While_Strengthen conseq h8)
  show "\<turnstile> \<langle>\<lambda>s. \<exists>t. (WHILE b DO c, s) \<Down> t \<and> Q t\<rangle> WHILE b DO c \<langle>Q\<rangle>"
    by (metis h9)
qed

lemma AssignND_is_pre: 
  "\<turnstile> \<langle>wp (x ::= ND vals) Q\<rangle> x ::= ND vals  \<langle>Q\<rangle>"
  using wp_AssND 
  by (fastforce simp: wp_def tAssignND)

definition select_pre where
  "select_pre \<equiv> \<lambda>bs Q. (\<lambda>s.(\<exists>t. (SELECT bs, s) \<Down> t \<and> Q t))"

definition select_path_pre where
  "select_path_pre \<equiv> \<lambda>b c Q. (\<lambda>s. (\<exists>t. (c, s) \<Down> t \<and> Q t))"

lemma SelectND_is_pre:
  assumes "\<forall>b c. (b,c) \<in> set bs \<longrightarrow> \<turnstile> \<langle>wp c Q\<rangle> c \<langle>Q\<rangle>"
    shows "\<turnstile> \<langle>wp (SELECT bs) Q\<rangle> SELECT bs \<langle>Q\<rangle>"
proof-
  have h3: "\<forall>s. select_pre bs Q s \<longrightarrow> (\<exists>b c. (b,c) \<in> set bs \<and> bval b s \<and> (\<exists>t. (c, s) \<Down> t \<and> Q t))"
    unfolding select_pre_def  by blast

  have h6: "\<forall>bc \<in> set bs. case bc of (b,c) \<Rightarrow> \<turnstile> \<langle>\<lambda>s. select_path_pre b c Q s \<and> bval b s\<rangle> c \<langle>Q\<rangle>"
    using assms
    unfolding select_path_pre_def wp_def apply clarsimp
    by (metis (no_types, lifting) strengthen_pre)

  hence "\<turnstile> \<langle>select_pre bs Q\<rangle> SELECT bs \<langle>Q\<rangle>" 
    unfolding select_path_pre_def
    using h3 by (fastforce intro: tSelectND)

  thus ?thesis
    by (fastforce simp: wp_def select_pre_def)
qed

lemma wp_is_pre: "\<turnstile> \<langle>wp c Q\<rangle> c \<langle>Q\<rangle>"
  proof(induction c arbitrary: Q)
    case If thus ?case by(force intro: conseq)
  next
    case SKIP thus ?case by force
  next
    case Assign thus ?case  by force
  next
    case Seq thus ?case by force
  next
    case AssignND thus ?case by (rule AssignND_is_pre)
  next
    case SelectND thus ?case 
      using SelectND_is_pre by force
  next
    case While thus ?case using While_is_pre by force
  qed


lemma sil_complete: 
  "\<Turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>"
  apply (rule strengthen_pre[where P="wp c Q"])
  by (fastforce intro: wp_is_pre simp: SIL_valid_def wp_def)+

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
