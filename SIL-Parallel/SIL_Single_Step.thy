(* Author: Tobias Nipkow *)

section "SIL Logic"

subsection "SIL Logic for Partial Correctness"

theory SIL_Single_Step imports Small_Step begin

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

definition SIL_Single_Step_Valid ::
  "assn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> post \<Rightarrow> bool" (\<open>\<Turnstile> (\<langle>(1_)\<rangle>/ (_)/ \<leadsto> (_)/ \<langle>(1_)\<rangle>)\<close> 50)
where
"\<Turnstile> \<langle>P\<rangle> c1 \<leadsto> c2 \<langle>R\<rangle> \<equiv>
      (case R of
      OK Q \<Rightarrow> (\<forall>s. P s \<longrightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sOK s') \<and> Q s'))
    | ER Q \<Rightarrow> (\<forall>s. P s \<longrightarrow> (\<exists>s'. (c1,sOK s) \<rightarrow> (c2,sER s') \<and> Q s')))"


abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  (\<open>_[_'/_]\<close> [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  SIL_Single_Step :: "assn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> post \<Rightarrow> bool" (\<open>\<turnstile> (\<langle>(1_)\<rangle>/ (_)/ \<leadsto> (_)/ \<langle>(1_)\<rangle>)\<close> 50)
where
sAbort: "\<turnstile> \<langle>P\<rangle> ABORT \<leadsto> SKIP \<langle>ER P\<rangle>"  |

sAssign:  "\<turnstile> \<langle>\<lambda>s. P(s[a/x])\<rangle> x::=a \<leadsto> SKIP \<langle>OK P\<rangle>"  |

sAssignNDOK:  "\<turnstile> \<langle>\<lambda>s. (\<exists>v \<in> vals. P(s(x := aval v s)))\<rangle> x::= ND vals \<leadsto> SKIP \<langle>OK P\<rangle>"  |

sAssignNDEmpty:  "\<turnstile> \<langle>P\<rangle> x ::= ND {} \<leadsto> ABORT \<langle>OK P\<rangle>"  |

sSeq: "\<lbrakk> \<turnstile> \<langle>P\<rangle> c\<^sub>1 \<leadsto> c\<^sub>1' \<langle>R\<rangle>\<rbrakk>
      \<Longrightarrow> \<turnstile> \<langle>P\<rangle> c\<^sub>1;;c\<^sub>2 \<leadsto> c\<^sub>1';;c\<^sub>2 \<langle>R\<rangle>"  |

sSeqSkip: "\<turnstile> \<langle>P\<rangle> SKIP;;c\<^sub>2 \<leadsto> c\<^sub>2 \<langle>OK P\<rangle>"  |

sIfTrue: "\<forall>s. P s \<longrightarrow> bval b s \<Longrightarrow> \<turnstile> \<langle>P\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c\<^sub>1  \<langle>OK P\<rangle>"  |
sIfFalse: "\<forall>s. P s \<longrightarrow> \<not>bval b s \<Longrightarrow> \<turnstile> \<langle>P\<rangle> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<leadsto> c\<^sub>2  \<langle>OK P\<rangle>"  |

sSelectND: "\<lbrakk>(b,c) \<in> set bs; bval b s\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. P s \<and> bval b s\<rangle> SELECT bs \<leadsto> c \<langle>OK P\<rangle>" |

sSelectNDNP: (* No Path *)
"\<lbrakk>\<forall>s. P s \<longrightarrow> (\<forall>(b, c) \<in> set bs. \<not>bval b s)\<rbrakk>
   \<Longrightarrow> \<turnstile> \<langle>P\<rangle> SELECT bs \<leadsto> ABORT \<langle>OK P\<rangle>" |

sWhile: "\<turnstile> \<langle>P\<rangle> WHILE b DO c \<leadsto> IF b THEN c;;WHILE b DO c ELSE SKIP \<langle>OK P\<rangle>" |

sConseqOK: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>OK Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<leadsto> c' \<langle>OK Q'\<rangle>" |

sConseqER: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>ER Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<leadsto> c' \<langle>ER Q'\<rangle>" |

sFalsePre: "\<turnstile> \<langle>\<lambda>s. False\<rangle> c \<leadsto> c' \<langle>Q\<rangle>" |

sDisjunction:  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>Q\<rangle>; \<turnstile> \<langle>R\<rangle> c \<leadsto> c' \<langle>Q\<rangle> \<rbrakk> 
        \<Longrightarrow> \<turnstile> \<langle>\<lambda>s. (P s \<or> R s)\<rangle> c \<leadsto> c' \<langle>Q\<rangle>"

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>R\<rangle> \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>P'\<rangle> c \<leadsto> c' \<langle>R\<rangle>"
  by (smt (verit, ccfv_SIG) post_assn.elims sConseqER sConseqOK)

lemma weaken_post_ok:
  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>OK Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>OK Q'\<rangle>"
  using sConseqOK by blast

lemma weaken_post_er:
  "\<lbrakk> \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>ER Q\<rangle>;  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> \<langle>P\<rangle> c \<leadsto> c' \<langle>ER Q'\<rangle>"
  using sConseqER by blast

text\<open>The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions.\<close>

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> \<langle>P\<rangle> x ::= a \<leadsto> SKIP \<langle>OK Q\<rangle>"
  by (simp add: sAssign strengthen_pre)

end
