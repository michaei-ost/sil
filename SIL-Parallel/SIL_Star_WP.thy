theory SIL_Star_WP

imports SIL_Star SIL_Big_Step_WP SIL_Single_Step_WP
begin

definition wp :: "com \<Rightarrow> post \<Rightarrow> assn" where
  "wp c R = (\<lambda>s. case R of
      OK Q \<Rightarrow> (\<exists>s'. (c,sOK s) \<rightarrow>* (SKIP,sOK s') \<and> Q s')
    | ER Q \<Rightarrow> (\<exists>s'. (c,sOK s) \<rightarrow>* (SKIP,sER s') \<and> Q s'))"

lemma one_step:
  assumes "c \<noteq> SKIP"
  and "(c, sOK s) \<rightarrow>* (SKIP, s'')"
  shows   "\<exists>c' s'. (c, sOK s) \<rightarrow> (c',s') \<and> (c',s') \<rightarrow>* (SKIP, s'')"
  using assms using star.cases by fastforce

lemma one_step_post:
  assumes "c \<noteq> SKIP"
  and "(c, sOK s) \<rightarrow>* (SKIP, s'') \<and> Q s''"
  shows   "\<exists>c' s'. (c, sOK s) \<rightarrow> (c',s') \<and> (c',s') \<rightarrow>* (SKIP, s'') \<and> Q s''"
using assms using star.cases by fastforce

lemma multi_step:
  assumes "c \<noteq> SKIP"
  and "(c, sOK s) \<rightarrow>* (SKIP, s'')"
  shows   "\<exists>c' s'. (c, sOK s) \<rightarrow>* (c',s') \<and> (c',s') \<rightarrow>* (SKIP, s'')"
  using assms using star.cases by fastforce

lemma multi_step_post:
  assumes "c \<noteq> SKIP"
  and "(c, sOK s) \<rightarrow>* (SKIP, s'') \<and> Q s''"
  shows   "\<exists>c' s'. (c, sOK s) \<rightarrow>* (c',s') \<and> (c',s') \<rightarrow>* (SKIP, s'') \<and> Q s''"
  using assms using star.cases by fastforce

lemma par_step_unfold_ok:
  assumes "c\<^sub>1 \<noteq> SKIP"
  and "c\<^sub>2 \<noteq> SKIP"
  and "(\<exists>s'. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK s') \<and> Q s')"
  shows "((\<exists>c\<^sub>1' s'. (c\<^sub>1, sOK s) \<rightarrow> (c\<^sub>1', sOK s') \<and> (\<exists>s'a. (c\<^sub>1' || c\<^sub>2, sOK s') \<rightarrow>* (SKIP, sOK s'a) \<and> Q s'a))
        \<or> (\<exists>c\<^sub>2' s'. (c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2', sOK s') \<and> (\<exists>s'a. (c\<^sub>1 || c\<^sub>2', sOK s') \<rightarrow>* (SKIP, sOK s'a) \<and> Q s'a)))"
  using ParE assms ok_reachable_from_ok by (smt (verit, best) Pair_inject com.distinct(15)
      sPost.distinct(1) star.simps)

lemma par_step_unfold_er:
  fixes c\<^sub>1 c\<^sub>2 :: com and Q :: assn and s :: state
  assumes hc1: "c\<^sub>1 \<noteq> SKIP"
  assumes hc2: "c\<^sub>2 \<noteq> SKIP"
  shows "(\<exists>s'. (c\<^sub>1 || c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER s') \<and> Q s')
       = ((\<exists>c\<^sub>1' s'. (c\<^sub>1, sOK s) \<rightarrow> (c\<^sub>1', sOK s') \<and>
                     (\<exists>s'a. (c\<^sub>1' || c\<^sub>2, sOK s') \<rightarrow>* (SKIP, sER s'a) \<and> Q s'a))
        \<or> (\<exists>c\<^sub>2' s'. (c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2', sOK s') \<and>
                     (\<exists>s'a. (c\<^sub>1 || c\<^sub>2', sOK s') \<rightarrow>* (SKIP, sER s'a) \<and> Q s'a))
        \<or> (\<exists>c\<^sub>1' s'. (c\<^sub>1, sOK s) \<rightarrow> (c\<^sub>1', sER s') \<and> Q s')
        \<or> (\<exists>c\<^sub>2' s'. (c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2', sER s') \<and> Q s'))"
  apply (intro iffI)
   apply clarsimp
  apply (smt (verit) ParE Small_Step.SkipE hc1 hc2 old.prod.inject sPost.distinct(1)
      star.simps)
  apply (elim disjE exE conjE)
     apply (metis ParL hc2 star.simps)
    apply (meson ParR hc1 star.step)
   apply (metis Er ParL hc2 star.simps)
  apply (metis Er ParR hc1 star.simps)
done

lemma par_skip_left_run_ok:
  assumes "\<exists>s'. (SKIP || c\<^sub>2, sOK x) \<rightarrow>* (SKIP, sOK s') \<and> Q s'"
  shows   "\<exists>s'. (c\<^sub>2, sOK x) \<rightarrow>* (SKIP, sOK s') \<and> Q s'"
  using one_step_post ParE assms by blast


lemma par_skip_left_run_er:
  assumes "\<exists>s'. (SKIP || c\<^sub>2, sOK x) \<rightarrow>* (SKIP, sER s') \<and> Q s'"
  shows   "\<exists>s'. (c\<^sub>2, sOK x) \<rightarrow>* (SKIP, sER s') \<and> Q s'"
  using one_step_post ParE assms by blast

lemma par_skip_right_run_ok:
  assumes "\<exists>s'. (c\<^sub>1 || SKIP, sOK x) \<rightarrow>* (SKIP, sOK s') \<and> Q s'"
  shows   "\<exists>s'. (c\<^sub>1, sOK x) \<rightarrow>* (SKIP, sOK s') \<and> Q s'"
  using one_step_post ParE assms by blast

lemma par_skip_right_run_er:
  assumes "\<exists>s'. (c\<^sub>1 || SKIP, sOK x) \<rightarrow>* (SKIP, sER s') \<and> Q s'"
  shows   "\<exists>s'. (c\<^sub>1 , sOK x) \<rightarrow>* (SKIP, sER s') \<and> Q s'"
  using one_step_post ParE assms by blast

lemma seq_decomp_er_from_c2:
  assumes h1: "(c\<^sub>1;;c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sER s')"
  assumes h2: "Q s'"
  assumes h3: "\<forall>s'. (c\<^sub>1, sOK s) \<rightarrow>* (SKIP, sER s') \<longrightarrow> \<not> Q s'"
  shows "\<exists>u. (c\<^sub>1, sOK s) \<rightarrow>* (SKIP, sOK u) \<and> (\<exists>s'a. (c\<^sub>2, sOK u) \<rightarrow>* (SKIP, sER s'a) \<and> Q s'a)"
  using assms  apply (induction "(c\<^sub>1;;c\<^sub>2, sOK s)" "(SKIP, sER s')" arbitrary: c\<^sub>1 c\<^sub>2 s s' rule: star.induct)
  apply clarsimp
  apply (case_tac "a = SKIP")
   apply clarsimp
   apply blast
  apply (case_tac b)
   apply clarsimp
  defer
   apply clarsimp
  using ErE SeqE final_iff_SKIP final_def
   apply (smt (verit, ccfv_SIG) old.prod.inject star.cases star.step)
by (smt (verit, del_insts) Small_Step.SeqE old.prod.inject star.simps)



lemma If_OK_unfold:
  shows "(bval b s \<longrightarrow>
            ((\<exists>s'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK s') \<and> Q s')
           = (\<exists>s'. (c\<^sub>1, sOK s) \<rightarrow>* (SKIP, sOK s') \<and> Q s')))
       \<and> (\<not> bval b s \<longrightarrow>
            ((\<exists>s'. (IF b THEN c\<^sub>1 ELSE c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK s') \<and> Q s')
           = (\<exists>s'. (c\<^sub>2, sOK s) \<rightarrow>* (SKIP, sOK s') \<and> Q s')))"
  apply (intro conjI impI)
  using IfTrue one_step apply (smt (verit, best) Small_Step.IfE com.distinct(9) sPost.distinct(1)
      sPost.inject(1) star.step)
  using IfFalse one_step
by (smt (verit, del_insts) Small_Step.IfE com.distinct(9) sPost.distinct(1) sPost.inject(1)
      star.simps) 

 (*
ParL:    "(c\<^sub>1, sOK s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1||c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1'||c\<^sub>2, s')" |
ParR:    "(c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>2', s') \<Longrightarrow> (c\<^sub>1||c\<^sub>2, sOK s) \<rightarrow> (c\<^sub>1||c\<^sub>2', s')" |
ParSkipR: "(c || SKIP, sOK s) \<rightarrow> (c, sOK s)" |
ParSkipL: "(SKIP || c, sOK s) \<rightarrow> (c, sOK s)" |
*)


lemma big_iff_small_wp:
  assumes "isSequential c"
  shows "wp c Q = wp_big_step c Q"
  unfolding wp_def wp_big_step_def
  apply(cases Q)
  using big_iff_small assms by fastforce+

lemma wp_SKIP_OK [simp]: 
  "wp SKIP (OK Q) = Q"
  by (simp add: big_iff_small_wp)

lemma wp_SKIP_ER [simp]: 
  "wp SKIP (ER Q) = (\<lambda>s. False)"
  by (simp add: big_iff_small_wp)

lemma wp_ABORT_OK [simp]: 
  "wp ABORT (OK Q) = (\<lambda>s. False)"
  by (simp add: big_iff_small_wp)

lemma wp_ABORT_ER [simp]: 
  "wp ABORT (ER Q) = Q"
  by (simp add: big_iff_small_wp)

lemma wp_Assign_OK [simp]: 
  "wp (x::=a) (OK Q) = (\<lambda>s. Q (s(x := aval a s)))"
  by (simp add: big_iff_small_wp)

lemma wp_Assign_ER [simp]: 
  "wp (x::=a) (ER Q) = (\<lambda>s. False)"
by (simp add: big_iff_small_wp)

lemma wp_AssignND_NonEmpty_OK [simp]: 
  "vals \<noteq> [] \<Longrightarrow> wp (x::= ND vals) (OK Q) = (\<lambda>s. (\<exists>v \<in> set vals. Q (s(x := aval v s))))"
by (simp add: big_iff_small_wp)

lemma wp_AssignND_NonEmpty_ER [simp]: 
  "vals \<noteq> [] \<Longrightarrow> wp (x::= ND vals) (ER Q) = (\<lambda>s. False)"
by (simp add: big_iff_small_wp)

lemma wp_AssignND_Empty_ER [simp]: 
  "vals = [] \<Longrightarrow> wp (x::= ND vals) (ER Q) = Q"
by (simp add: big_iff_small_wp)

lemma wp_AssignND_Empty_OK [simp]: 
  "vals = [] \<Longrightarrow> wp (x::= ND vals) (OK Q) = (\<lambda>s. False)"
  by (simp add: big_iff_small_wp)

lemma wp_Par_OK[simp]:
  "c\<^sub>1 \<noteq> SKIP \<and> c\<^sub>2 \<noteq> SKIP \<Longrightarrow> wp (c\<^sub>1 || c\<^sub>2) (OK Q) = (\<lambda>s. 
    (\<exists>c\<^sub>1'. wp_single c\<^sub>1 c\<^sub>1'  (OK (wp (c\<^sub>1'||c\<^sub>2) (OK Q))) s)
    \<or> (\<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2'  (OK (wp (c\<^sub>1||c\<^sub>2') (OK Q))) s))" 
  apply (rule ext)
  unfolding wp_def wp_single_def
   apply clarsimp
  apply(rule iffI)
  using par_step_unfold_ok apply simp
by (meson ParL ParR star.step)

lemma wp_Par_ER[simp]:
  "c\<^sub>1 \<noteq> SKIP \<and> c\<^sub>2 \<noteq> SKIP \<Longrightarrow> wp (c\<^sub>1 || c\<^sub>2) (ER Q) = (\<lambda>s. 
    (\<exists>c\<^sub>1'. wp_single c\<^sub>1 c\<^sub>1'  (OK (wp (c\<^sub>1'||c\<^sub>2) (ER Q))) s)
    \<or> (\<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2'  (OK (wp (c\<^sub>1||c\<^sub>2') (ER Q))) s)
    \<or> (\<exists>c\<^sub>1'. wp_single c\<^sub>1 c\<^sub>1'  (ER Q) s)
    \<or> (\<exists>c\<^sub>2'. wp_single c\<^sub>2 c\<^sub>2'  (ER Q) s))"
  apply (rule ext)
  unfolding wp_def wp_single_def
  apply clarsimp
using par_step_unfold_er by auto

lemma wp_Par_SKIP_L[simp]:
  " wp (SKIP || c\<^sub>2) Q = wp c\<^sub>2 Q"
  apply (rule ext)
  unfolding wp_def
  apply(cases Q)
  apply clarsimp
  apply(rule iffI)
   defer
    apply (meson ParSkipL star.step)
   apply clarsimp
   apply (metis ParSkipL par_skip_left_run_er star.step)
using par_skip_left_run_ok by blast

lemma wp_Par_SKIP_R[simp]:
  " wp (c\<^sub>1 || SKIP) Q = wp c\<^sub>1 Q"
  apply (rule ext)
  unfolding wp_def
  apply(cases Q)
  apply clarsimp
  apply(rule iffI)
    defer
    apply (meson ParSkipR star.step)
   apply clarsimp
  apply (metis ParSkipR par_skip_right_run_er star.step)
using par_skip_right_run_ok by blast

lemma wp_SelectND_OK[simp]: 
  "wp (SelectND S) (OK Q) = (\<lambda>s. \<exists>(b,c) \<in> set S. (bval b s) \<and> (wp c (OK Q) s))"
  apply (rule ext)
  apply (simp add: wp_def)
  apply (rule iffI)
   apply clarsimp
  apply (smt (verit, ccfv_threshold) Big_Step.AbortE Pair_inject Small_Step.SelectNDE case_prodI
      com.distinct(11) isSequential.simps(7) one_step_post sPost.inject(1) small_step.Abort small_to_big_er
      small_to_big_ok star.step star_sER)
  by (smt (verit, del_insts) case_prodE small_step.SelectND star_step1 star_trans)

lemma wp_SelectND_ER[simp]: 
  "wp (SelectND S) (ER Q) = 
    (\<lambda>s. (\<exists>(b,c) \<in> set S. (bval b s) \<and> (wp c (ER Q) s)) 
                \<or> ((\<forall>(b,c) \<in> set S. \<not>bval b s) \<and> Q s))"
  apply (rule ext)
  apply (simp add: wp_def)
  apply (rule iffI)
   apply clarsimp
  apply (smt (verit, best) Small_Step.AbortE Small_Step.SelectNDE case_prodI2 instant_er_eq
      isSequential.simps(6) old.prod.inject post_state.simps(1) sPost.distinct(1) split_cong
      star.simps)
  by (smt (verit, ccfv_threshold) Small_Step.SelectNDE case_prodE case_prod_conv com.distinct(11)
      final_def final_iff_SKIP post_state.simps(1) sPost.distinct(1) small_step.Abort small_step.SelectND
      star.simps)

lemma wp_Seq_OK[simp]: 
  "wp (c\<^sub>1;;c\<^sub>2) (OK Q) = wp c\<^sub>1 (OK (wp c\<^sub>2 (OK Q)))"
  apply (rule ext)
  apply (simp add: wp_def)
  apply (rule iffI)
  defer
   apply clarsimp
   apply (metis seq_comp_sOK)
by (metis ok_reachable_from_ok seq_decomp)

lemma wp_Seq_ER[simp]: 
  "wp (c\<^sub>1;;c\<^sub>2) (ER Q) = (\<lambda>s. wp c\<^sub>1 (OK (wp c\<^sub>2 (ER Q))) s \<or> wp c\<^sub>1 (ER Q) s )"
  apply (rule ext)
  apply (simp add: wp_def)
  apply (rule iffI)
   apply clarsimp
   defer
   apply (metis seq_comp_sER seq_comp_sOK)
using seq_decomp_er_from_c2 by auto

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
 apply (rule ext)
  apply (simp add: wp_def)
  apply (cases Q)
   apply clarsimp
   defer
  apply (smt (verit) Small_Step.IfE com.distinct(9) finalD_ok final_def old.prod.inject post.simps(6)
      sPost.distinct(1) sPost.inject(1) star.cases star.step)
using If_OK_unfold by auto

lemma wp_While_If:
 "wp (WHILE b DO c) Q = wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q "
  apply (rule ext)
  apply (simp add: wp_def)
  apply (cases Q)
   apply clarsimp
  apply (metis (full_types) Small_Step.WhileE While com.distinct(13) final_iff_SKIP sPost.distinct(1)
      star.cases star.step)
  by (smt (verit, best) Small_Step.WhileE While finalD_ok final_iff_SKIP post.simps(6) sPost.distinct(1)
      star.cases star.step)

lemma wp_While_True[simp]: 
  "bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
  by(fastforce simp: wp_While_If)

lemma wp_While_False_OK[simp]: 
  "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) (OK Q) s  = Q s"
  by (simp add: wp_While_If)

lemma wp_While_False_ER[simp]: 
  "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) (ER Q) s  = False"
  by (simp add: wp_While_If)

lemma wp_Post_Disjunction_OK[simp]:
  "wp c (OK (\<lambda>s. Q\<^sub>1 s \<or> Q\<^sub>2 s)) =
   (\<lambda>s. wp c (OK Q\<^sub>1) s \<or> wp c (OK Q\<^sub>2) s)"
  apply (rule ext)
  apply (simp add: wp_def)
  by blast

lemma wp_Post_Disjunction_ER[simp]:
  "wp c (ER (\<lambda>s. Q\<^sub>1 s \<or> Q\<^sub>2 s)) =
   (\<lambda>s. wp c (ER Q\<^sub>1) s \<or> wp c (ER Q\<^sub>2) s)"
  apply (rule ext)
  apply (simp add: wp_def)
by blast

datatype pred =
    PTrue
  | PFalse
  | PNot pred
  | PAnd pred pred
  | POr pred pred
  | PAtom bexp

fun pred_sem :: "pred \<Rightarrow> state \<Rightarrow> bool" where
  "pred_sem PTrue s = True"
| "pred_sem PFalse s = False"
| "pred_sem (PNot p) s = (\<not>pred_sem p s)"
| "pred_sem (PAnd p q) s =
     (pred_sem p s \<and> pred_sem q s)"
| "pred_sem (POr p q) s =
     (pred_sem p s \<or> pred_sem q s)"
| "pred_sem (PAtom b) s = bval b s"

datatype post' =
    OK' pred
    | ER' pred

fun post_sem :: "post' \<Rightarrow> post" where
  "post_sem (OK' p) = OK (pred_sem p)"
| "post_sem (ER' p) = ER (pred_sem p)"

fun subst_aexp :: "aexp \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> aexp" where 
  "subst_aexp (N n) x a = N n" 
| "subst_aexp (V y) x a = (if x = y then a else V y)" 
| "subst_aexp (Plus e1 e2) x a = Plus (subst_aexp e1 x a) (subst_aexp e2 x a)" 

fun subst_bexp :: "bexp \<Rightarrow> string \<Rightarrow> aexp \<Rightarrow> bexp" where 
  "subst_bexp (Bc v) x a = Bc v" 
| "subst_bexp (Not b) x a = Not (subst_bexp b x a)" 
| "subst_bexp (And b\<^sub>1 b\<^sub>2) x a = And (subst_bexp b\<^sub>1 x a) (subst_bexp b\<^sub>2 x a)" 
| "subst_bexp (Less a\<^sub>1 a\<^sub>2) x a' = Less (subst_aexp a\<^sub>1 x a') (subst_aexp a\<^sub>2 x a')"
| "subst_bexp (Equal a\<^sub>1 a\<^sub>2) x a' = Equal (subst_aexp a\<^sub>1 x a') (subst_aexp a\<^sub>2 x a')"

fun subst_pred :: "pred \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> pred" where
  "subst_pred PTrue x a = PTrue" 
| "subst_pred PFalse x a = PFalse" 
| "subst_pred (PNot p) x a = PNot (subst_pred p x a)" 
| "subst_pred (PAnd p q) x a = PAnd (subst_pred p x a) (subst_pred q x a)" 
| "subst_pred (POr p q) x a = POr (subst_pred p x a) (subst_pred q x a)" 
| "subst_pred (PAtom b) x a = PAtom (subst_bexp b x a)"

fun bexp_simp :: "bexp \<Rightarrow> bexp" where
  "bexp_simp (Not b) =
     (case bexp_simp b of
        Bc v \<Rightarrow> Bc (\<not>v)
      | b' \<Rightarrow> Not b')" |
  "bexp_simp (And b1 b2) =
     (case (bexp_simp b1, bexp_simp b2) of
        (Bc v1, Bc v2) \<Rightarrow> Bc (v1 \<and> v2)
      | (Bc True, b2') \<Rightarrow> b2'
      | (b1', Bc True) \<Rightarrow> b1'
      | (Bc False, _) \<Rightarrow> Bc False
      | (_, Bc False) \<Rightarrow> Bc False
      | (b1', b2') \<Rightarrow> And b1' b2')" |
  "bexp_simp b = b"

fun aexp_simp :: "aexp \<Rightarrow> aexp" where 
  "aexp_simp (N n) = N n" 
| "aexp_simp (V x) = V x" 
| "aexp_simp (Plus a\<^sub>1 a\<^sub>2) = 
  (case (aexp_simp a\<^sub>1, aexp_simp a\<^sub>2) of 
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N (n\<^sub>1 + n\<^sub>2) 
  | (a\<^sub>1', a\<^sub>2') \<Rightarrow> Plus a\<^sub>1' a\<^sub>2')"

fun pred_simp :: "pred \<Rightarrow> pred" where 
  "pred_simp PTrue = PTrue" 
| "pred_simp PFalse = PFalse" 
| "pred_simp (PNot p) = 
  (case pred_simp p of 
    PTrue \<Rightarrow> PFalse 
  | PFalse \<Rightarrow> PTrue
  | p' \<Rightarrow> PNot p')" 
| "pred_simp (PAnd p q) = 
  (case (pred_simp p, pred_simp q) of 
    (PFalse, _) \<Rightarrow> PFalse 
  | (_, PFalse) \<Rightarrow> PFalse 
  | (PTrue, q') \<Rightarrow> q' 
  | (p', PTrue) \<Rightarrow> p' 
  | (p', q') \<Rightarrow> PAnd p' q')" 
| "pred_simp (POr p q) = 
  (case (pred_simp p, pred_simp q) of 
    (PTrue, _) \<Rightarrow> PTrue 
  | (_, PTrue) \<Rightarrow> PTrue 
  | (PFalse, q') \<Rightarrow> q' 
  | (p', PFalse) \<Rightarrow> p' 
  | (p', q') \<Rightarrow> POr p' q')" 
| "pred_simp (PAtom (Bc v)) = (if v then PTrue else PFalse)" 
| "pred_simp (PAtom (Less a\<^sub>1 a\<^sub>2)) = 
  (case (aexp_simp a\<^sub>1, aexp_simp a\<^sub>2) of 
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> if n\<^sub>1 < n\<^sub>2 then PTrue else PFalse 
  | (a\<^sub>1', a\<^sub>2') \<Rightarrow> PAtom (Less a\<^sub>1' a\<^sub>2'))"
| "pred_simp (PAtom (Equal a\<^sub>1 a\<^sub>2)) = 
  (case (aexp_simp a\<^sub>1, aexp_simp a\<^sub>2) of 
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> if n\<^sub>1 = n\<^sub>2 then PTrue else PFalse 
  | (a\<^sub>1', a\<^sub>2') \<Rightarrow> PAtom (Equal a\<^sub>1' a\<^sub>2'))"
| "pred_simp (PAtom (Not b)) =
     (case bexp_simp (Not b) of
        Bc True  \<Rightarrow> PTrue
      | Bc False \<Rightarrow> PFalse
      | b'       \<Rightarrow> PAtom b')"
| "pred_simp (PAtom (And b1 b2)) =
     (case bexp_simp (And b1 b2) of
        Bc True  \<Rightarrow> PTrue
      | Bc False \<Rightarrow> PFalse
      | b'       \<Rightarrow> PAtom b')"


(*
fun wp_calc :: "com \<Rightarrow> post' \<Rightarrow> pred" where
  "wp_calc SKIP (OK' Q) = Q"
| "wp_calc (x ::= a) (OK' Q) = (subst_pred Q x a)"
| "wp_calc (c1;;c2) (OK' Q) = (wp_calc c1 (OK' (wp_calc c2 (OK' Q))))"
| "wp_calc (c1 || c2) (OK' Q) =
     POr
       (wp_calc c1 (OK' (wp_calc (c1' || c2) (OK' Q))))
       (wp_calc c2 (OK' (wp_calc (c1 || c2') (OK' Q))))"
*)

type_synonym while_limit = "com \<Rightarrow> (nat \<times> nat)"

datatype trace =
    BigStep com
  | ParLeft com com
  | ParRight com com
  | SelectTrace bexp com
  | AssignNDTrace aexp
  | SeqTrace trace trace
  | TraceList "trace list"
  | IfTrace bexp bool trace
  | IterationTrace nat trace trace
  | IterationLimitTrace nat
  | IterationRemaining nat

fun wp_calc ::
  "nat \<Rightarrow> while_limit \<Rightarrow> com \<Rightarrow> post' \<Rightarrow> (pred \<times> trace) list"
where

  "wp_calc 0 w c (OK' Q) = []"

| "wp_calc 0 w c (ER' Q) = []"

| "wp_calc (Suc n) w SKIP (OK' Q) =
     [(Q, BigStep SKIP)]"

| "wp_calc (Suc n) w SKIP (ER' Q) =
     [(PFalse, BigStep SKIP)]"

| "wp_calc (Suc n) w ABORT (OK' Q) =
     [(PFalse, BigStep SKIP)]"

| "wp_calc (Suc n) w ABORT (ER' Q) =
     [(Q, BigStep SKIP)]"

| "wp_calc (Suc n) w (x ::= a) (OK' Q) =
     [(subst_pred Q x a, BigStep (x ::= a))]"

| "wp_calc (Suc n) w (x ::= a) (ER' Q) =
     [(PFalse, BigStep (x ::= a))]"

| "wp_calc (Suc n) w (c1;;c2) (OK' Q) =
    concat (map
      (\<lambda>(p2,t2).
        map
          (\<lambda>(p1,t1).
            (p1, SeqTrace t1 t2))
          (wp_calc n w c1 (OK' p2)))
      (wp_calc n w c2 (OK' Q)))"

| "wp_calc (Suc n) w (SELECT S) (OK' Q) =
    
      (concat (map
        (\<lambda>(b,c).
          map
            (\<lambda>(p,t).
              (pred_simp (PAnd (PAtom b) p),
               SeqTrace (SelectTrace b c) t))
            (wp_calc n w c (OK' Q)))
        S))"

| "wp_calc (Suc n) w (AssignND x []) (OK' Q) =
    [(PFalse, BigStep (x ::= ND []))]"

| "wp_calc (Suc n) w (AssignND x []) (ER' Q) =
    [(Q, BigStep (x ::= ND []))]"

| "wp_calc (Suc n) w (AssignND x (S1 # S)) (ER' Q) =
    [(PFalse, BigStep (x ::= ND S))]"

| "wp_calc (Suc n) w (AssignND x (S1 # S)) (OK' Q) =
    concat (map
      (\<lambda>a.
        map
          (\<lambda>(p,t).
            (p, AssignNDTrace a))
          (wp_calc n w (x ::= a) (OK' Q)))
      (S1 # S))"

| "wp_calc (Suc n) w (IF b THEN c1 ELSE c2) Q =
    filter
      (\<lambda>(p,t). pred_simp p \<noteq> PFalse)
      (append
        (map
          (\<lambda>(p,t).
            (pred_simp (PAnd (PAtom b) p),
             IfTrace b True t))
          (wp_calc n w c1 Q))
        (map
          (\<lambda>(p,t).
            (pred_simp (PAnd (PAtom (Not b)) p),
             IfTrace b False t))
          (wp_calc n w c2 Q)))"

| "wp_calc (Suc fuel) limits (WHILE b DO c) (OK' Q) =
    (let
       (i,n) = limits (WHILE b DO c);
       xs = wp_calc fuel limits c (OK' Q)
     in
       concat (map
         (\<lambda>(p,t).
           (let
              next_limits = limits((WHILE b DO c) := (Suc i,n));
              Q' =
                if i = 0 then
                  pred_simp (PAnd (PAtom (Not b)) Q)
                else
                  pred_simp (PAnd (PAtom b) p)
            in
              if i > n then
                [(PFalse, IterationLimitTrace n)]
              else if Q' = PFalse then
                [(PFalse, IterationRemaining (n-i))]
              else
              [(Q', IterationRemaining (n-i))] @
                map
                  (\<lambda>(p',t').
                    (p', IterationTrace i t t'))
                  (wp_calc fuel next_limits
                    (WHILE b DO c)
                    (OK' Q'))))
         xs))"



definition example :: com where
  "example = (''x'' ::= Plus (V ''x'') (N 1));; (''y'' ::= N 10) || (''x'' ::= Plus (V ''x'') (N 40))"

definition select_example :: "com" where
  "select_example =
     SelectND [
       (Less (V ''y'') (N 10), ''x'' ::= N 1),
       (Bc True, ''x'' ::= N 10),
       (Bc True, ''x'' ::= N 100)
     ]"

definition assignND_example :: "com" where
  "assignND_example =
     AssignND ''x'' [N 1, N 2, N 3]"

definition AS_example :: "com" where
  "AS_example =
     AssignND ''x'' [N 5,N 10];;
     SelectND [
        (Equal (V ''x'') (N 5), ''y'' ::= N 2),
        (Equal (V ''x'') (N 10), ''y'' ::= N 11)
    ] 
  "


definition if_example :: "com" where
  "if_example =
     AssignND ''x'' [Plus (V ''x'') (N 5), Plus (V ''x'') (N 8)];;
     IF Less (V ''x'') (N 10)
     THEN ''y'' ::= N 1
     ELSE ''y'' ::= N 20"

definition while_example :: com where
  "while_example =
     WHILE Less (V ''x'') (N 10)
     DO ''x'' ::= Plus (V ''x'') (N 2)"

definition aQ :: post' where 
  "aQ = OK' (PAtom (Less (N 9) (V ''x'')))"



value "
  map
    (\<lambda>(p,t). (pred_simp p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      ((''y'' ::= (V ''x'')) ;;
      (WHILE (Less (V ''y'') (N 3))
         DO AssignND ''y''
              [Plus (V ''y'') (N 1),
               Plus (V ''y'') (N 2)]))
      (OK' (PAtom (Less (V ''x'') (N 5)))))"


value "(pred_simp (fst (wp_calc 100 while_example aQ)),
        snd (wp_calc 100 while_example aQ))"

end