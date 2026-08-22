section "Small-Step Semantics of Commands"

theory Small_Step imports Star Big_Step begin

subsection "The transition relation"

datatype post = sOK state | sER state

fun post_state :: "post \<Rightarrow> state" where
  "post_state (sOK Q) = Q"
| "post_state (sER Q) = Q"

inductive
  small_step :: "com * post \<Rightarrow> com * post \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55)
where
Abort: "(ABORT, sOK s) \<rightarrow> (SKIP, sER s)" |

Assign:  "(x ::= a, sOK s) \<rightarrow> (SKIP, sOK (s(x := aval a s)))" |

AssignND: "v \<in> S \<Longrightarrow> (x ::= ND S, sOK s) \<rightarrow> (SKIP, sOK (s(x := aval v s)))" |
AssignNDEmpty: "(x ::= ND {}, sOK s) \<rightarrow> (ABORT, sOK s)" |

Seq1:    "(SKIP;;c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2, sOK s)" |
Seq2:    "(c\<^sub>1,sOK s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,sOK s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

ParL:    "(c\<^sub>1, sOK s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1||c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1'||c\<^sub>2, s')" |
ParR:    "(c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2', s') \<Longrightarrow> (c\<^sub>1||c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1||c\<^sub>2', s')" |
ParSkipR: "(c || SKIP, sOK s) \<rightarrow> (c, sOK s)" |
ParSkipL: "(SKIP || c, sOK s) \<rightarrow> (c, sOK s)" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,sOK s) \<rightarrow> (c\<^sub>1,sOK s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,sOK s) \<rightarrow> (c\<^sub>2,sOK s)" |

While:   "(WHILE b DO c,sOK s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, sOK s)" |

SelectND: "\<lbrakk>(b, c) \<in> set bs; bval b s\<rbrakk> \<Longrightarrow> (SELECT bs, sOK s) \<rightarrow> (c,sOK s)" |
SelectNDN: "\<lbrakk>\<forall>(b, c) \<in> set bs. \<not>bval b s\<rbrakk>  \<Longrightarrow> (SELECT bs, sOK s) \<rightarrow> (ABORT, sOK s)" |

Er: "c \<noteq> SKIP \<Longrightarrow> (c, sER s) \<rightarrow> (SKIP, sER s)"

abbreviation
  small_steps :: "com * post \<Rightarrow> com * post \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55)
where "x \<rightarrow>* y == star small_step x y"

subsection\<open>Executability\<close>

code_pred small_step .

subsection\<open>Proof infrastructure\<close>

subsubsection\<open>Induction rules\<close>

text\<open>The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form \<open>a \<rightarrow> b \<Longrightarrow> \<dots>\<close> where \<open>a\<close> and \<open>b\<close> are
not already pairs \<open>(DUMMY,DUMMY)\<close>. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
\<open>\<rightarrow>\<close> into pairs:\<close>
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection\<open>Proof automation\<close>

declare small_step.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AbortE[elim!]: "(ABORT,s) \<rightarrow> ct"
thm AbortE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases AssignNDE[elim!]: "(x::= ND A,s) \<rightarrow> ct"
thm AssignNDE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases ParE[elim]: "(c1||c2,s) \<rightarrow> ct"
thm ParE
inductive_cases SelectNDE[elim]: "(SELECT S, s) \<rightarrow> ct"
thm SelectNDE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

subsection "Equivalence with big-step semantics"

lemma ok_reachable_from_ok:
  "(c, s) \<rightarrow>* (c', sOK s') \<Longrightarrow> \<exists>x. s = sOK x"
proof (induction "(c, s)" "(c', sOK s')" arbitrary: c s rule: star.induct)
  case refl
  then show ?case
    by auto
next
  case (step y)
  obtain c'' s'' where x_split: "y = (c'', s'')" by force
  thus ?case
    using small_step.cases step.hyps(1,3) by fastforce
qed

(*
proof (induction "(c, s)" "(c', sOK s')" arbitrary: c s rule: star.induct)
  case refl
  then show ?case
    by auto
next
  case (step y)
  obtain c'' s'' where x_split: "y = (c'', s'')" by force
  thus ?case
    using small_step.cases step.hyps(1,3) by fastforce
qed
*)

lemma star_sER: "(SKIP, sER s) \<rightarrow>* (SKIP, sER s)"
  by auto

lemma star_seq2_sOK: "(c1, sOK s) \<rightarrow>* (c1', sOK s') \<Longrightarrow> (c1;;c2, sOK s) \<rightarrow>* (c1';;c2, sOK s')"
proof(induction "(c1, sOK s)" "(c1', sOK s')" arbitrary: c1 s rule: star.induct)
  case refl thus ?case by simp
next
  case (step x c1 s)
  obtain c1'' s'' where x_eq: "x = (c1'', sOK s'')" 
    by (metis ok_reachable_from_ok old.prod.exhaust step.hyps(2))
  thus ?case
    by (metis Seq2 star.simps step.hyps(1,3))
qed

lemma seq_sER_collapse: "(c1;;c2, sER s) \<rightarrow> (SKIP, sER s)"
  by auto

lemma seq_sER_collapse_star: "(c1;;c2, sER s) \<rightarrow>* (SKIP, sER s)"
  by auto

lemma seq_comp_sOK:
  "\<lbrakk> (c1, sOK s1) \<rightarrow>* (SKIP,sOK s2); (c2,sOK s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, sOK s1) \<rightarrow>* (SKIP,s3)"
  by (meson Seq1 star.step star_seq2_sOK star_trans)

lemma seq_comp_sER:
  "(c1, s) \<rightarrow>* (SKIP, sER s2) \<Longrightarrow> (c1;;c2, s) \<rightarrow>* (SKIP, sER s2)"
  apply (induction "(c1, s)" "(SKIP, sER s2)" arbitrary: c1 s rule: star.induct)
   apply simp
  apply(case_tac s)
  apply clarsimp
  defer
   apply clarsimp
  apply(case_tac b)
  using ok_reachable_from_ok apply blast
   defer
  apply(case_tac b)
  apply (metis Seq2 star.step)
   apply (meson Seq2 star.step)
  apply clarsimp 
  by (smt (verit) Pair_inject post.distinct(1) seq_sER_collapse_star small_step.simps
      star.cases)




(*
text\<open>The following proof corresponds to one on the board where one would
show chains of \<open>\<rightarrow>\<close> and \<open>\<rightarrow>*\<close> steps.\<close>

lemma big_to_small:
  "cs \<Down> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule seq_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by simp
  moreover assume "(c0,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  moreover assume "(c1,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by(metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (c;; ?w, s)" by (simp add: b)
  moreover have "(c;; ?w,s) \<rightarrow>* (SKIP,t)" by(rule seq_comp[OF c w])
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix v S  x s
  assume "v \<in> (S::(int set))"
  show "(x ::= ND S, s) \<rightarrow>* (SKIP, s(x := v))"
    by (metis \<open>v \<in> S\<close> small_step.AssignND star_step1)
next
  fix b c bs s t
  assume "(b, c) \<in> set (bs::((bexp \<times> com) list))"
  assume "bval b s"
  assume "(c, s) \<Down> t"
  assume "(c, s) \<rightarrow>* (SKIP, t)"
  show "(SELECT bs, s) \<rightarrow>* (SKIP, t)"
    by (metis \<open>(b, c) \<in> set bs\<close> \<open>(c, s) \<Down> t\<close> \<open>(c, s) \<rightarrow>* (SKIP, t)\<close> \<open>bval b s\<close>
        small_step.SelectND star.simps)
qed
*)

fun isSequential :: "com \<Rightarrow> bool" where
  "isSequential (Par _ _)      = False" |
  "isSequential (Seq c1 c2)    = (isSequential c1 \<and> isSequential c2)" |
  "isSequential (If b c1 c2)   = (isSequential c1 \<and> isSequential c2)" |
  "isSequential (While b c)    = isSequential c" |
  "isSequential (SelectND xs)  = (\<forall>(b,c) \<in> set xs. isSequential c)" |
  "isSequential _              = True"

lemma sequential_imp:
  assumes "isSequential c"
  and "(c, sOK s) \<rightarrow> (c', sOK s')"
shows "isSequential c'"
  sorry

lemma small_to_big_single_ok:
  assumes "isSequential c"
  shows "(c, sOK s) \<rightarrow> (SKIP, sOK s') \<Longrightarrow>  (c, s) \<Down> (s', True)"
  apply (cases rule: small_step.cases)
                  apply blast
                 apply blast
                apply blast
               apply blast
              apply blast
             apply blast
            apply blast
           apply blast
          apply blast
         defer
         defer
         apply blast
        apply blast
       apply blast
      apply blast
     apply blast
    apply blast
  using assms apply auto[1]
  using assms by auto

lemma small_to_big_single_er:
  assumes "isSequential c"
  shows "(c, sOK s) \<rightarrow> (SKIP, sER s') \<Longrightarrow> (c, s) \<Down> (s', False)"
  apply (cases rule: small_step.cases)
  by blast+   

lemma small_to_big_step_ok:
  assumes  "(c, sOK s) \<rightarrow> (c', sOK s')"
      and  "(c', s') \<Down> (t,True)"
      and "isSequential c"
      and "isSequential c'"
    shows "(c,s) \<Down> (t,True)"
  using assms
  apply (induction "(c, sOK s)" "(c', sOK s')" arbitrary: c c' s s' t  rule: small_step.induct)
               apply fast
              apply fast
             apply fast
            apply fast
            defer
           apply simp
          apply force
         apply force
        apply fastforce
       apply fastforce
      apply fastforce
     apply blast
    apply blast
   apply fast
  apply clarsimp
by blast

lemma small_to_big_step_er:
  assumes  "(c, sOK s) \<rightarrow> (c', sOK s')"
      and  "(c', s') \<Down> (t,False)"
      and "isSequential c"
      and "isSequential c'"
    shows "(c,s) \<Down> (t,False)"
  using assms
  apply (induction "(c, sOK s)" "(c', sOK s')" arbitrary: c c' s s' t  rule: small_step.induct)
               apply fast
              apply fast
             apply fast
            apply fast
            defer
           apply force
          apply simp
         apply simp
        apply simp
       apply blast
      apply fast
     apply blast
    apply blast
   apply blast
  by (metis (no_types, lifting) Big_Step.SeqE SeqFalse SeqTrue isSequential.simps(2)
      small_to_big_step_ok)

lemma small_to_big_step:
  assumes  "(c, sOK s) \<rightarrow> (c', sOK s')"
      and  "(c', s') \<Down> ta"
      and "isSequential c"
      and "isSequential c'"
    shows "(c,s) \<Down> ta"
  by (metis (full_types) assms(1,2,3,4) old.prod.exhaust small_to_big_step_er
      small_to_big_step_ok)

lemma small_to_big_ok:
  shows "(c, sOK s) \<rightarrow>* (SKIP, sOK t) 
          \<Longrightarrow> isSequential c 
          \<Longrightarrow> (c,s) \<Down> (t,True)"
proof (induction "(c, sOK s)" "(SKIP,sOK t)" arbitrary: c s rule: star.induct)
  case refl
  then show ?case by blast
next
  case (step y)
  then show ?case proof-
    obtain c' s' where x_eq: "y = (c', sOK s')"
      by (metis ok_reachable_from_ok old.prod.exhaust step.hyps(2))
   then show ?case
     using sequential_imp small_to_big_step step.hyps(1,3) step.prems by blast
 qed
qed

lemma instant_er_eq:
  assumes "(c', sER s) \<rightarrow>* (SKIP, sER t)"
  shows "t = s"
proof-
  show ?thesis 
    by (smt (verit) Pair_inject assms post.distinct(1) post.inject(2) small_step.simps
        star.cases)
qed

lemma pure_er:
  assumes "(c, sOK x) \<rightarrow> (c', sER t)"
  and "(c', sER t) \<rightarrow>* (SKIP, sER t)"
  shows "(c, x) \<Down> (t, False)"
using assms
  apply (induction "(c, sOK x)" "(c', sER t)" arbitrary: c x c' t rule: small_step.induct)
  apply fast
  apply blast
  oops

lemma small_to_big_er:
  "(c, q) \<rightarrow>* (SKIP, sER t) \<Longrightarrow>
   (case q of
      sOK s \<Rightarrow> (c,s) \<Down> (t,False)
    | sER s \<Rightarrow> s = t)" 
  apply (induction "(c, q)" "(SKIP,sER t)" arbitrary: c q rule: star.induct)
   apply clarsimp
  apply (case_tac q)
   apply clarsimp
   apply (case_tac b)
    apply clarsimp
  using small_to_big_step_er apply auto[1]
   apply clarsimp
   defer
   apply (case_tac q)
    apply clarsimp
   apply (cases q)
    apply clarsimp
    apply(case_tac b) oops
     apply (metis instant_er_eq star.step)
    apply (metis instant_er_eq star.step)
   apply (smt (verit, del_insts) post.simps(6) instant_er_eq star.step)
  by (simp add: pure_er)
  oops

lemma small_to_big_er_start:
  assumes  "(c, sOK s) \<rightarrow> (c', sER s')"
  shows "(c,s) \<Down> (s', False)"
  using assms
proof-
  have h0: "c' \<noteq> SKIP \<Longrightarrow> (c,s) \<Down> (s', False)"
    by (metis Er assms post.simps(5) small_to_big_er star.step star_ER)
  oops




text \<open>
  Finally, the equivalence theorem:
\<close>
(*
theorem big_iff_small:
  "cs \<Down> t = cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)
*)

subsection "Final configurations and infinite reductions"

definition "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma finalD_ok: "final (c,sOK s) \<Longrightarrow> c = SKIP"
apply(simp add: final_def)
  apply(induction c)
         apply blast
        apply blast
       apply blast
       defer
      apply blast
     apply blast
    apply blast
    apply blast
  defer
  apply (metis ex_in_conv small_step.AssignND small_step.AssignNDEmpty)
  by blast

lemma finalD_er: "final (c,sER s) \<Longrightarrow> c = SKIP"
apply(simp add: final_def)
  apply(induction c) by blast+

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP"
  by (metis finalD_er finalD_ok post.exhaust)

lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
by (metis SkipE finalD final_def)

text\<open>Now we can show that \<open>\<Rightarrow>\<close> yields a final state iff \<open>\<rightarrow>\<close>
terminates:\<close>
(*
lemma big_iff_small_termination:
  "(\<exists>t. cs \<Rightarrow> t) \<longleftrightarrow> (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
by(simp add: big_iff_small final_iff_SKIP)
*)
text\<open>This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since \<open>\<rightarrow>\<close> is determininistic, there is no difference
between may and must terminate.\<close>

end
