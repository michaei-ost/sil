(* Author: Tobias Nipkow *)

subsection \<open>Soundness and Completeness\<close>

theory SIL_Sound_Complete
imports SIL
begin

subsubsection "Soundness"


lemma sil_while_sound:
 "(\<And>n::nat. \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s \<and> T s n\<rangle> c  \<langle>\<lambda>s. P s \<and> (\<exists>n'<n. T s n')\<rangle>) \<Longrightarrow>
  (\<And>n::nat. \<forall>s. P s \<and> bval b s \<and> T s n \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> P t \<and> (\<exists>n'<n. T t n'))) \<Longrightarrow>
  P s \<Longrightarrow> T s m \<Longrightarrow> \<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t"
  thm Nat.nat_less_induct
  apply (induct m arbitrary: s rule: Nat.nat_less_induct)
  apply clarsimp
  apply (cases "bval b s")
   defer
   apply blast
proof-
  {
  fix n s
  assume IH: "\<forall>m<n. \<forall>s. P s \<longrightarrow>  T s m \<longrightarrow> (\<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t)"
  and body_triple:  "\<And>n. \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s \<and> T s n\<rangle> c  \<langle>\<lambda>s. P s \<and> (\<exists>n'<n. T s n')\<rangle>"
  and body_consq: "\<And>n. \<forall>s. P s \<and> bval b s \<and> T s n \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> P t \<and> (\<exists>n'<n. T t n'))"
  and P: "P s"
  and T: "T s n" 
  and guard: "bval b s"
  have "\<exists>t. (c, s) \<Rightarrow> t \<and> P t \<and> (\<exists>n'<n. T t n')"
    using P T body_consq guard by blast
  then obtain s_1 m where body_works: "(c, s) \<Rightarrow> s_1 \<and> P s_1 \<and> (m<n \<and> T s_1 m)" by blast
  then obtain s_2 where "(WHILE b DO c, s_1) \<Rightarrow> s_2 \<and> P s_2 \<and> \<not> bval b s_2" using IH  by blast
  then have "\<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t"
    using body_works guard by blast
  } then show "\<And>n sa.
       \<lbrakk>\<forall>m<n. \<forall>x. P x \<longrightarrow> T x m \<longrightarrow> (\<exists>t. (WHILE b DO c, x) \<Rightarrow> t \<and> P t \<and> \<not> bval b t);
        \<And>n. \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s \<and> T s n\<rangle> c  \<langle>\<lambda>s. P s \<and> (\<exists>n'<n. T s n')\<rangle>;
        \<And>n. \<forall>s. P s \<and> bval b s \<and> T s n \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> P t \<and> (\<exists>n'<n. T t n')); P sa; T sa n; bval b s\<rbrakk>
       \<Longrightarrow> \<exists>t. (WHILE b DO c, sa) \<Rightarrow> t \<and> P t \<and> \<not> bval b t"
    by blast
qed



lemma sil_sound: "\<turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>  \<Longrightarrow>  \<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>"
  apply (induction rule: SIL.induct)
  apply (auto simp: SIL_valid_def)[1]
  apply (auto simp: SIL_valid_def)[1]
  apply (auto simp: SIL_valid_def)[1]
  unfolding SIL_valid_def apply blast
  unfolding SIL_valid_def apply blast
  unfolding SIL_valid_def apply blast
  defer
  unfolding SIL_valid_def apply blast
  apply clarsimp
by (rule sil_while_sound)
  

subsubsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<exists>t. (c,s) \<Rightarrow> t \<and>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
  unfolding wp_def
by (auto simp: wp_def)

lemma wp_AssND[simp]: "wp (x::= ND vals) Q = (\<lambda>s. (\<exists>v \<in> vals. Q (s(x := v))))"
  using wp_def
by auto

lemma wp_SelectND[simp]: "wp (SelectND S) Q = (\<lambda>s. \<exists>(b,c) \<in> set S. (bval b s) \<and> (wp c Q s))"
  using wp_def
by auto

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
by(simp add: wp_While_If)


subsubsection "Completeness"

lemma while_is_pre:
  "\<turnstile> \<langle>wp (WHILE b DO c) Q\<rangle> (WHILE b DO c) \<langle>Q\<rangle>"
  unfolding SIL_valid_def wp_def
  apply(auto simp: SIL_valid_def)
  apply (cases "bval b s")
  defer
  apply(rule WhileFalse)
 sledgehammer
  sorry


(*
 "\<turnstile> \<langle>\<lambda>s. (\<exists>v \<in> vals. P(s(x := v)))\<rangle> x::= ND vals \<langle>P\<rangle>"

AssignND: "v \<in> S \<Longrightarrow> (x ::= ND S, s) \<Rightarrow> s(x := v)"
*)

lemma syntax_identical:
    "\<exists>v \<in> vals. Q (s(x := v)) \<Longrightarrow> \<exists>t. (x ::= ND vals, s) \<Rightarrow> t \<and> Q t"
  proof (erule bexE)
    fix v
    assume h1: "v \<in> vals"
    assume h2: "Q (s(x := v))"
  show "\<exists>t. (x ::= ND vals, s) \<Rightarrow> t \<and> Q t"
  proof (rule exI[of _ "s(x := v)"])
    show "(x ::= ND vals, s) \<Rightarrow> s(x := v) \<and> Q (s(x := v))"
    by (simp add: AssignND h1 h2)
  qed
qed

lemma syntax_identical_reverse:
  "\<exists>t. (x ::= ND vals, s) \<Rightarrow> t \<and> Q t \<Longrightarrow> \<exists>v \<in> vals. Q (s(x := v))"
proof (erule exE)
  fix t
  assume h: "(x ::= ND vals, s) \<Rightarrow> t \<and> Q t"
  from h have step: "(x ::= ND vals, s) \<Rightarrow> t" by (rule conjE)
  from h have Qt: "Q t" by (rule conjE)
  from step obtain v where "v \<in> vals" and "t = s(x := v)"
    by (rule AssignNDE)
  then show "\<exists>v \<in> vals. Q (s(x := v))"
    using \<open>t = s(x := v)\<close> \<open>v \<in> vals\<close> h by auto
qed


lemma AssignND_is_pre: 
"\<turnstile> \<langle>wp (x ::= ND vals) Q\<rangle>
          x ::= ND vals  \<langle>Q\<rangle>"
  unfolding wp_def
proof-
  show "\<turnstile> \<langle>\<lambda>s. \<exists>t. (x ::= ND vals, s) \<Rightarrow> t \<and> Q t\<rangle> x ::= ND vals \<langle>Q\<rangle>"
    using tAssignND wp_AssND wp_def by auto
qed

(*
tSelectND: "\<lbrakk>(b,c) \<in> set bs ;  \<forall>s. P s \<longrightarrow>  bval b s ;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>Q\<rangle>"

SelectND: "\<lbrakk> (b, c) \<in> set bs; bval b s; (c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (SELECT bs, s) \<Rightarrow> t"
*)

(*
Have a Precondition: P = 
"\<lambda>s. (\<exists>t. (SELECT bs, s) \<Rightarrow> t \<and> Q t)"

Need to Prove that

1. Pick a (b,c) from set bs
2. Prove that P s \<rightarrow> bval b s
3. Prove that \<langle>P\<rangle> c \<langle>Q\<rangle> is a valid triple.

*)

thm SelectNDE

lemma "\<lbrakk>(b,c) \<in> set bs ;  \<forall>s. P s \<longrightarrow>  bval b s ;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>Q\<rangle>"
  by (simp add: tSelectND)
  apply (rule tSelectND[where P = "\<lambda>s. (\<exists>t. (SELECT bs, s) \<Rightarrow> t \<and> Q t)"])
  oops

lemma
"\<And>t. (SELECT bs, s) \<Rightarrow> t \<and> Q t \<Longrightarrow> (\<And>b c. (b, c) \<in> set bs \<Longrightarrow> bval b s \<Longrightarrow> (c, s) \<Rightarrow> t \<Longrightarrow> Q t) \<Longrightarrow> Q t"
  by blast

lemma cor_1: "\<lbrakk>(b,c) \<in> set bs\<rbrakk> \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. bval b s \<and> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t)\<rangle> SELECT bs \<langle>Q\<rangle>"

  sorry

lemma strengthen_test:
" \<turnstile> \<langle>\<lambda>s. bval b s \<and> ((c,s) \<Rightarrow> t \<and> Q t)\<rangle> SELECT bs \<langle>Q\<rangle> \<Longrightarrow>
  \<turnstile> \<langle>\<lambda>s. (SELECT x, s) \<Rightarrow> t \<and>
               Q t\<rangle>
       SELECT x  \<langle>Q\<rangle>
"
  show "\<exists>t. (b, c) \<in> set bs \<Longrightarrow> (\<lambda>s. bval b s \<and> ((c,s) \<Rightarrow> t \<and> Q t) \<Longrightarrow> (SELECT bs, s) \<Rightarrow> t \<and>
               Q t)"
    sledgehammer
    oops

lemma "\<turnstile> \<langle>wp (SELECT x) Q\<rangle>
  SELECT x  \<langle>Q\<rangle>"
  unfolding wp_def
proof -
  fix s t
  assume pre: "\<exists>t. (SELECT x, s) \<Rightarrow> t \<and> Q t"
  assume step: "(SELECT x, s) \<Rightarrow> t"
  from pre obtain t' where ht': "(SELECT x, s) \<Rightarrow> t'" and Qt': "Q t'" by blast
  from step obtain b c where 
    hbc: "(b,c) \<in> set x" and
    hb: "bval b s" and
    hc: "(c,s) \<Rightarrow> t"
    by (rule SelectNDE)
  oops

lemma SelectND_is_pre: 
"\<turnstile> \<langle>wp (SELECT x) Q\<rangle>
  SELECT x  \<langle>Q\<rangle>"
  unfolding wp_def
proof-
  assume h: "\<exists>t. (SELECT x, s) \<Rightarrow> t \<and> Q t"
  from h obtain t where ht: "(SELECT x, s) \<Rightarrow> t" and Qt: "Q t" by blast
  have "(\<And>b c. (b, c) \<in> set bs \<Longrightarrow> bval b s \<Longrightarrow> (c, s) \<Rightarrow> t \<Longrightarrow> Q t) \<Longrightarrow> Q t" 
    using Qt by fastforce
  have "(SELECT bs, s) \<Rightarrow> t \<and> Q t \<Longrightarrow> (\<And>b c. (b, c) \<in> set bs \<Longrightarrow> bval b s \<Longrightarrow> (c, s) \<Rightarrow> t \<Longrightarrow> Q t) \<Longrightarrow> Q t"
    by argo 
 have "\<lbrakk> (b, c) \<in> set bs; bval b s; (c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (SELECT bs, s) \<Rightarrow> t"
   by auto
  have "\<lbrakk>(b,c) \<in> set bs\<rbrakk> \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. bval b s \<and> ((c,s) \<Rightarrow> t \<and> Q t)\<rangle> SELECT bs \<langle>Q\<rangle>"
    by (smt (verit, ccfv_SIG) conseq cor_1)
  have "\<turnstile> \<langle>\<lambda>s. (SELECT x, s) \<Rightarrow> t \<and>
               Q t\<rangle>
       SELECT x  \<langle>Q\<rangle>"
    oops


lemma wp_is_pre: "\<turnstile> \<langle>wp c Q\<rangle> c \<langle>Q\<rangle>"
  proof(induction c arbitrary: Q)
    case If thus ?case by(auto intro: conseq)
  next
    case SKIP thus ?case by auto
    case Assign thus ?case  by auto
    case Seq thus ?case  by auto
  next
    case AssignND thus ?case by (rule AssignND_is_pre)
    case SelectND thus ?case using SelectND_is_pre by auto
  next
    case While thus ?case by (simp add: while_is_pre)
  qed


lemma sil_complete: assumes "\<Turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>" shows "\<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: SIL_valid_def wp_def)
  show "\<turnstile> \<langle>wp c Q\<rangle> c \<langle>Q\<rangle>" by(rule wp_is_pre)
qed

corollary sil_sound_complete: "\<turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle> \<longleftrightarrow> \<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle>"
  by (metis sil_sound sil_complete)


end
