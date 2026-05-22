(* Author: Tobias Nipkow *)

section "SIL Logic"

subsection "SIL Logic for Partial Correctness"

theory SIL  imports Big_Step begin

type_synonym assn = "state \<Rightarrow> bool"

definition
SIL_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" (\<open>\<Turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50) where
"\<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle> = (\<forall>s. P s \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> Q t))"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  (\<open>_[_'/_]\<close> [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  SIL :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" (\<open>\<turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50)
where
Skip: "\<turnstile> \<langle>P\<rangle> SKIP \<langle>P\<rangle>"  |

Assign:  "\<turnstile> \<langle>\<lambda>s. P(s[a/x])\<rangle> x::=a \<langle>P\<rangle>"  |

AssignND:  "\<turnstile> \<langle>\<lambda>s. (\<exists>v \<in> vals. P(s[N v/x]))\<rangle> x::= ND vals \<langle>P\<rangle>"  |

Seq: "\<lbrakk> \<turnstile> \<langle>P\<rangle> c\<^sub>1 \<langle>Q\<rangle>;  \<turnstile> \<langle>Q\<rangle> c\<^sub>2 \<langle>R\<rangle> \<rbrakk>
      \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c\<^sub>1;;c\<^sub>2 \<langle>R\<rangle>"  |

If: "\<lbrakk> \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> c\<^sub>1 \<langle>Q\<rangle>;  \<turnstile> \<langle>\<lambda>s. P s \<and> \<not> bval b s\<rangle> c\<^sub>2 \<langle>Q\<rangle> \<rbrakk>
     \<Longrightarrow> \<turnstile> \<langle>P\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<langle>Q\<rangle>"  |

SelectND: "\<lbrakk>(b,c) \<in> set bs ;  \<forall>s. P s \<longrightarrow>  bval b s ;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>Q\<rangle>" |

While: "\<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> c \<langle>P\<rangle> \<Longrightarrow>
        \<turnstile> \<langle>P\<rangle> WHILE b DO c \<langle>\<lambda>s. P s \<and> \<not> bval b s\<rangle>"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>Q'\<rangle>"

lemmas [simp] = SIL.Skip SIL.Assign SIL.Seq If

lemmas [intro!] = SIL.Skip SIL.Assign SIL.Seq SIL.If

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle> \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>Q\<rangle>"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> \<langle>P\<rangle> c \<langle>Q'\<rangle>"
by (blast intro: conseq)

text\<open>The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions.\<close>

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> \<langle>P\<rangle> x ::= a \<langle>Q\<rangle>"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> c \<langle>P\<rangle>" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile> \<langle>P\<rangle> WHILE b DO c \<langle>Q\<rangle>"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])

end
