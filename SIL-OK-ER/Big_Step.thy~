(* Author: Gerwin Klein, Tobias Nipkow *)

subsection "Big-Step Semantics of Commands"

theory Big_Step imports Com_SIL begin

text \<open>
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes \<open>(c,s) \<Down> s'\<close>.
\<close>

text_raw\<open>\snip{BigStepdef}{0}{1}{%\<close>
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<times> bool \<Rightarrow> bool" (infix \<open>\<Down>\<close> 55)
where
Skip: "(SKIP,s) \<Down> (s, True)" |
Abort: "(ABORT,s) \<Down> (s, False)" |
Assign: "(x ::= a,s) \<Down> (s(x := aval a s), True)" |
AssignND: "v \<in> S \<Longrightarrow> (x ::= ND S, s) \<Down> (s(x := v), True)" |
AssignNDEmpty: "(x ::= ND {}, s) \<Down> (s, False)" |
SeqTrue: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Down> (s\<^sub>2,True);  (c\<^sub>2,s\<^sub>2) \<Down> sb \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Down> sb" |
SeqFalse: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Down> (s\<^sub>2,False) \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Down> (s\<^sub>2,False)" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Down> tb \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Down> tb" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Down> tb \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Down> tb" |
SelectND: "\<lbrakk> (b, c) \<in> set bs; bval b s; (c, s) \<Down> tb \<rbrakk> \<Longrightarrow> (SELECT bs, s) \<Down> tb" |
SelectNDFalse: "\<lbrakk> \<forall>(b, c) \<in> set bs. \<not>bval b s\<rbrakk> \<Longrightarrow> (SELECT bs, s) \<Down> (s,False)" |
WhileGuardFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Down> (s,True)" |
WhileBodySucceeds:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Down> (s\<^sub>2,True);  (WHILE b DO c, s\<^sub>2) \<Down> sb \<rbrakk>  
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Down> sb" |
WhileBodyAborts:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Down> (s\<^sub>2,False)\<rbrakk>  
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Down> (s\<^sub>2,False)"
print_theorems
 
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{BigStepEx}{1}{2}{%\<close>
schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Down> ?t"
apply(rule SeqTrue)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw\<open>}%endsnip\<close>

thm ex[simplified]

text\<open>We want to execute the big-step rules:\<close>

code_pred big_step .

text\<open>For inductive definitions we need command
       \texttt{values} instead of \texttt{value}.\<close>

text\<open>Proof automation:\<close>

text \<open>The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules.\<close>
declare big_step.intros [intro]

text\<open>The standard induction rule 
@{thm [display] big_step.induct [no_vars]}\<close>

thm big_step.induct

text\<open>
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the \<open>c\<close>, \<open>s\<close>,
and \<open>s'\<close> that we are likely to encounter. Splitting
the tuple parameter fixes this:
\<close>
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text \<open>
@{thm [display] big_step_induct [no_vars]}
\<close>


subsection "Rule inversion"

text\<open>What can we deduce from \<^prop>\<open>(SKIP,s) \<Down> t\<close> ?
That \<^prop>\<open>s = t\<close>. This is how we can automatically prove it:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<Down> t"
thm SkipE
inductive_cases AbortE[elim!]: "(ABORT,s) \<Down> t"
thm AbortE

text\<open>This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands:\<close>

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Down> t"
thm AssignE
inductive_cases AssignNDE[elim!]: "(x ::= ND vals, s) \<Down> t"
thm AssignNDE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Down> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Down> t"
thm IfE
inductive_cases SelectNDE[elim!]: "(SELECT bs, s) \<Down> t"
thm SelectNDE
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Down> t"
thm WhileE
text\<open>Only [elim]: [elim!] would not terminate.\<close>

text\<open>An automatic example:\<close>

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Down> (t,a) \<Longrightarrow> t = s"
by blast

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Down> (s',True) \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Down> (s,b) \<longleftrightarrow> (c1;; (c2;; c3), s) \<Down> (s,b)" 
by auto

subsection "Command Equivalence"

text \<open>
  We call two statements \<open>c\<close> and \<open>c'\<close> equivalent wrt.\ the
  big-step semantics when \emph{\<open>c\<close> started in \<open>s\<close> terminates
  in \<open>s'\<close> iff \<open>c'\<close> started in the same \<open>s\<close> also terminates
  in the same \<open>s'\<close>}. Formally:
\<close>
text_raw\<open>\snip{BigStepEquiv}{0}{1}{%\<close>
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix \<open>\<sim>\<close> 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Down> t  =  (c',s) \<Down> t)"
text_raw\<open>}%endsnip\<close>

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Down> (t,a)  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Down> (t,a)"
    apply(induction "WHILE b DO c" s t a arbitrary: b c rule: big_step_induct)
  by blast+

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (metis sim_while_cong_aux surj_pair)

text \<open>Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically.\<close>

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

subsection "Execution is deterministic"

text \<open>This proof is automatic.\<close>

(* you could define a (recursive) predicate for ND_free *)
primrec nd_free :: "com \<Rightarrow> bool"
  where
    "nd_free SKIP = True"
  | "nd_free ABORT = True"
  | "nd_free (Assign _ _) = True"
  | "nd_free (AssignND _ _) = False"
  | "nd_free (Seq c1 c2) = (nd_free c1 \<and> nd_free c2)"
  | "nd_free (If _ c1 c2) = (nd_free c1 \<and> nd_free c2)"
  | "nd_free (SelectND _ ) = False"
  | "nd_free (While _ c) = nd_free c"

abbreviation nd_free_cs:: "com \<times> state \<Rightarrow> bool"
  where "nd_free_cs cs \<equiv> nd_free (fst cs)"

theorem big_step_determ:
  shows "\<lbrakk> cs \<Down> t ;  cs \<Down> u ;  nd_free_cs cs\<rbrakk> \<Longrightarrow> u = t"
  apply (induction arbitrary: u rule: big_step.induct)
               apply fastforce
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply (metis SeqE nd_free.simps(5) split_pairs)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply (metis (no_types, lifting) WhileE fstI nd_free.simps(8) prod.inject)
  by (metis WhileE fstI nd_free.simps(8) prod.inject)
end
