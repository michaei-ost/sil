(* Author: Tobias Nipkow *)

section "SIL Logic"

subsection "SIL Logic for Partial Correctness"

theory SIL imports Big_Step begin

type_synonym assn = "state \<Rightarrow> bool"

datatype post =
    OK assn
    | ER assn

fun post_assn :: "post \<Rightarrow> assn" where
  "post_assn (OK Q) = Q"
| "post_assn (ER Q) = Q"

fun post_ok :: "post \<Rightarrow> bool" where
  "post_ok (OK Q) = True"
| "post_ok (ER Q) = False"

fun apply_post :: "post \<Rightarrow> state \<times> bool \<Rightarrow> bool" where
  "apply_post (OK Q) (s,b) = (Q s \<and> b)" 
| "apply_post (ER Q) (s,b) = (Q s \<and> \<not>b)" 


definition SIL_valid ::
  "assn \<Rightarrow> com \<Rightarrow> post \<Rightarrow> bool" (\<open>\<Turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50)
where
"\<Turnstile> \<langle>P\<rangle> c \<langle>R\<rangle> \<equiv>
  (case R of
      OK Q \<Rightarrow> (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Down> (t,True) \<and> Q t))
    | ER Q \<Rightarrow> (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Down> (t,False) \<and> Q t)))"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  (\<open>_[_'/_]\<close> [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  SIL :: "assn \<Rightarrow> com \<Rightarrow> post \<Rightarrow> bool" (\<open>\<turnstile> (\<langle>(1_)\<rangle>/ (_)/  \<langle>(1_)\<rangle>)\<close> 50)
where
tSkip: "\<turnstile> \<langle>P\<rangle> SKIP \<langle>OK P\<rangle>"  |

tAbort: "\<turnstile> \<langle>P\<rangle> ABORT \<langle>ER P\<rangle>"  |

tAssign:  "\<turnstile> \<langle>\<lambda>s. P(s[a/x])\<rangle> x::=a \<langle>OK P\<rangle>"  |

tAssignNDOK:  "\<turnstile> \<langle>\<lambda>s. (\<exists>v \<in> vals. P(s(x := aval v s)))\<rangle> x::= ND vals \<langle>OK P\<rangle>"  |

tAssignNDER:  "\<turnstile> \<langle>P\<rangle> x ::= ND {} \<langle>ER P\<rangle>"  |

tSeqOK: "\<lbrakk> \<turnstile> \<langle>P\<rangle> c\<^sub>1 \<langle>OK Q\<rangle>;  \<turnstile> \<langle>Q\<rangle> c\<^sub>2 \<langle>R\<rangle> \<rbrakk>
      \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c\<^sub>1;;c\<^sub>2 \<langle>R\<rangle>"  |

tSeqER: "\<lbrakk> \<turnstile> \<langle>P\<rangle> c\<^sub>1 \<langle>ER Q\<rangle>\<rbrakk>
      \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c\<^sub>1;;c\<^sub>2 \<langle>ER Q\<rangle>"  |

tIf: "\<lbrakk> \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> c\<^sub>1 \<langle>R\<rangle>;  \<turnstile> \<langle>\<lambda>s. P s \<and> \<not> bval b s\<rangle> c\<^sub>2 \<langle>R\<rangle> \<rbrakk>
     \<Longrightarrow> \<turnstile> \<langle>P\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<langle>R\<rangle>"  |

tSelectND: "
\<lbrakk>
  \<forall>bc \<in> set bs. case bc of (b,c) \<Rightarrow> 
      \<turnstile> \<langle>\<lambda>s. (R b c) s \<and> bval b s\<rangle> c \<langle>Q\<rangle>;
  \<forall>s. P s \<longrightarrow> 
      (\<exists>b c.(b, c) \<in> set bs  \<and> (R b c) s \<and> bval b s)
\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>Q\<rangle>" |

tSelectNDNP: (* No Path *)
"
\<lbrakk>
  \<forall>s. P s \<longrightarrow> (\<forall>(b,c) \<in> set bs. \<not>bval b s)
\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<langle>ER P\<rangle>" |

tWhileOK: "
\<lbrakk>
  \<And>n::nat. \<turnstile> \<langle>Q (Suc n)\<rangle> c  \<langle>OK (Q n)\<rangle>; 
  \<And>s. Q 0 s \<Longrightarrow> \<not> bval b s;
  \<And>n s. Q (Suc n) s \<Longrightarrow> bval b s
\<rbrakk>
\<Longrightarrow> 
  \<turnstile> \<langle>\<lambda>s. \<exists>n. Q n s\<rangle>  WHILE b DO c \<langle>OK (Q 0)\<rangle>" |

tWhileER: "
\<lbrakk>
  \<And>n::nat. \<turnstile> \<langle>Q (Suc (Suc n))\<rangle> c  \<langle>OK (Q (Suc n))\<rangle>; 
  \<turnstile> \<langle>Q 1\<rangle> c  \<langle>ER (Q 0)\<rangle>; 
  \<And>n s. Q (Suc n) s \<Longrightarrow> bval b s
\<rbrakk>
\<Longrightarrow> 
  \<turnstile> \<langle>\<lambda>s. \<exists>n. Q (Suc n) s\<rangle>  WHILE b DO c \<langle>ER (Q 0)\<rangle>" |

conseqOK: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>OK Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>OK Q'\<rangle>" |

conseqER: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>ER Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>ER Q'\<rangle>" |

false_pre: "\<turnstile> \<langle>\<lambda>s. False\<rangle> c \<langle>Q\<rangle>" |

disjunction:  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<langle>Q\<rangle>; \<turnstile> \<langle>R\<rangle> c \<langle>Q\<rangle> \<rbrakk> 
        \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. (P s \<or> R s)\<rangle> c \<langle>Q\<rangle>"

lemmas [simp] = SIL.tSkip SIL.tAssign SIL.tSeqOK tIf
lemmas [intro!] = SIL.tSkip SIL.tAssign SIL.tSeqOK SIL.tIf

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>R\<rangle> \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>R\<rangle>"
  by (smt (verit, ccfv_SIG) conseqER conseqOK post.exhaust)

lemma strengthen_pre_ok:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>OK Q\<rangle> \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>OK Q\<rangle>"
  by (simp add: conseqOK)

lemma strengthen_pre_er:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<langle>ER Q\<rangle> \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<langle>ER Q\<rangle>"
  by (simp add: conseqER)

lemma weaken_post_ok:
  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<langle>OK Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> \<langle>P\<rangle> c \<langle>OK Q'\<rangle>"
  using conseqOK by blast

lemma weaken_post_er:
  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<langle>ER Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> \<langle>P\<rangle> c \<langle>ER Q'\<rangle>"
  using conseqER by blast

text\<open>The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions.\<close>

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> \<langle>P\<rangle> x ::= a \<langle>OK Q\<rangle>"
  by (metis (lifting) conseqOK tAssign)

end
