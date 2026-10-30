(* Author: Tobias Nipkow *)

section "SIL Logic"

subsection "SIL Logic for Partial Correctness"

theory SIL imports Big_Step begin

type_synonym assn = "state \<Rightarrow> bool"

definition
SIL_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" (\<open>\<Turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50) where
"\<Turnstile> \<langle>P\<rangle>c\<langle>Q\<rangle> \<equiv> (\<forall>s. P s \<longrightarrow> (\<exists>t. (c, s) \<Down> t \<and> Q t))"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  (\<open>_[_'/_]\<close> [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  SIL :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" (\<open>\<turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50)
where
tSkip: "\<turnstile> \<langle>P\<rangle> SKIP \<langle>P\<rangle>"  |

tAssign:  "\<turnstile> \<langle>\<lambda>s. P(s[a/x])\<rangle> x::=a \<langle>P\<rangle>"  |

tAssignND:  "\<turnstile> \<langle>\<lambda>s. (\<exists>v \<in> vals. P(s(x := aval v s)))\<rangle> x::= ND vals \<langle>P\<rangle>"  |

tSeq: "\<lbrakk> \<turnstile> \<langle>P\<rangle> c\<^sub>1 \<langle>Q\<rangle>;  \<turnstile> \<langle>Q\<rangle> c\<^sub>2 \<langle>R\<rangle> \<rbrakk>
      \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c\<^sub>1;;c\<^sub>2 \<langle>R\<rangle>"  |

tIf: "\<lbrakk> \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> c\<^sub>1 \<langle>Q\<rangle>;  \<turnstile> \<langle>\<lambda>s. P s \<and> \<not> bval b s\<rangle> c\<^sub>2 \<langle>Q\<rangle> \<rbrakk>
     \<Longrightarrow> \<turnstile> \<langle>P\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<langle>Q\<rangle>"  |

tSelectND: "
\<lbrakk>
  \<forall>bc \<in> set bs. case bc of (b,c) \<Rightarrow> 
      \<turnstile> \<langle>\<lambda>s. (R b c) s \<and> bval b s\<rangle> c \<langle>Q\<rangle>;
  \<forall>s. P s \<longrightarrow> 
      (\<exists>b c.(b, c) \<in> set bs  \<and> (R b c) s \<and> bval b s)
\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>Q\<rangle>" |

tWhile: "
\<lbrakk>
  \<And>n::nat. \<turnstile> \<langle>Q (Suc n)\<rangle> c  \<langle>Q n\<rangle>; 
  \<And>s. Q 0 s \<Longrightarrow> \<not> bval b s;
  \<And>n s. Q (Suc n) s \<Longrightarrow> bval b s
\<rbrakk>
\<Longrightarrow> 
  \<turnstile> \<langle>\<lambda>s. \<exists>n. Q n s\<rangle>  WHILE b DO c \<langle>\<lambda>s. Q 0 s\<rangle>" |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>Q'\<rangle>" |

disjunction:  "\<lbrakk> \<turnstile> \<langle>P\<^sub>1\<rangle> c \<langle>Q\<^sub>1\<rangle>; \<turnstile> \<langle>P\<^sub>2\<rangle> c \<langle>Q\<^sub>2\<rangle> \<rbrakk> 
        \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. (P\<^sub>1 s \<or> P\<^sub>2 s)\<rangle> c \<langle>\<lambda>s. (Q\<^sub>1 s \<or> Q\<^sub>2 s)\<rangle>" |

empty: "\<turnstile> \<langle>\<lambda>s. False\<rangle> c \<langle>P\<rangle>"  


lemmas [simp] = SIL.tSkip SIL.tAssign SIL.tSeq tIf

lemmas [intro!] = SIL.tSkip SIL.tAssign SIL.tSeq SIL.tIf

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
  by (simp add: strengthen_pre[OF _ tAssign])

lemma Example_1: "\<turnstile> \<langle>\<lambda>s. True\<rangle> ''n'' ::= ND {N 0, N 1} ;; ''x'' ::= V ''n'' \<langle>\<lambda>s. s ''x'' = 0\<rangle>"
proof-

 have h0': "\<lambda>s. (\<lambda>t. t ''n'' = 0) (s[(N 0)/''n'']) \<equiv> \<lambda>s. True"
    by simp
  have h0: "\<turnstile> \<langle>\<lambda>s. True\<rangle> ''n'' ::= ND {N 0, N 1} \<langle>\<lambda>s. s ''n'' = 0\<rangle>" 
    using tAssignND conseq h0' by (smt (verit, ccfv_SIG) insertCI)
  have h1: "\<turnstile> \<langle>\<lambda>s. s ''n'' = 0\<rangle> ''x'' ::= V ''n'' \<langle>\<lambda>s. s ''x'' = 0\<rangle>" 
    using tAssign by (simp add: Assign')
  have h2: "\<turnstile> \<langle>\<lambda>s. True\<rangle> ''n'' ::= ND {N 0, N 1} ;; ''x'' ::= V ''n'' \<langle>\<lambda>s. s ''x'' = 0\<rangle>"
    using tSeq h0 h1 by blast
  then show ?thesis by blast
lemma 
end
