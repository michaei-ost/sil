theory SIL_Star_Calc

imports SIL_Star_WP
begin
datatype pred =
    PTrue
  | PFalse
  | PNot pred
  | PAnd pred pred
  | POr pred pred
  | PAtom bexp
  | PComEq com com

fun pred_sem :: "pred \<Rightarrow> state \<Rightarrow> bool" where
  "pred_sem PTrue s = True"
| "pred_sem PFalse s = False"
| "pred_sem (PNot p) s = (\<not>pred_sem p s)"
| "pred_sem (PAnd p q) s =
     (pred_sem p s \<and> pred_sem q s)"
| "pred_sem (POr p q) s =
     (pred_sem p s \<or> pred_sem q s)"
| "pred_sem (PAtom b) s = bval b s"
| "pred_sem (PComEq c1 c2) s = (\<lambda>s. c1 = c2) s"

datatype pred_post  =
    OK' pred
    | ER' pred

fun post_sem :: "pred_post \<Rightarrow> post" where
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
| "subst_pred (PComEq c1 c2) x a = (PComEq c1 c2)"

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
| "pred_simp (PComEq c1 c2) =
     (if c1 = c2 then PTrue else PFalse)"

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

fun next_com :: "com  \<Rightarrow> com list" where

  "next_com SKIP = []"

| "next_com ABORT = [SKIP]"

| "next_com (x ::= a) = [SKIP]"

| "next_com (x ::= ND  a) = [SKIP, ABORT]"

| "next_com (IF b THEN c1 ELSE c2) = [c1, c2, SKIP]"

| "next_com (WHILE b DO c) = [IF b THEN c;; WHILE b DO c ELSE SKIP, SKIP]"

| "next_com (SELECT S) = map snd S @ [ABORT, SKIP]"

| "next_com (c1;;c2) = 
    [SKIP] @ (if c1 = SKIP then
       [c2]
     else
       map (\<lambda>c1'. c1';;c2) (next_com c1))" 

| "next_com (c1 || c2) =
     [SKIP] @ (if c2 = SKIP then
        [c1]
      else
        map (\<lambda>c1'. c1' || c2) (next_com c1))
     @
     (if c1 = SKIP then
        [c2]
      else
        map (\<lambda>c2'. c1 || c2') (next_com c2))"

fun no_selection :: "(bexp \<times> com) list \<Rightarrow> pred \<Rightarrow> pred" where
  "no_selection [] Q = Q"
| "no_selection ((b,c)#S) Q =
     PAnd (PAtom (Not b)) (no_selection S Q)"

type_synonym while_limit = "com \<Rightarrow> (nat \<times> nat)"

datatype trace =
    BigStep com
    | SmallStep com
    | SmallStepTrace trace
    | SmallStepER com
  | SmallStepIf bool com
  | SmallStepSelect bexp com
  | ParLeft trace trace
  | ParRight trace trace
  | ParExitTrace trace
  | SelectTrace bexp com
  | AssignNDTrace aexp
  | SeqTrace trace trace
  | TraceList "trace list"
  | IfTrace bexp bool trace
  | IterationTrace nat trace trace
  | IterationLimitTrace nat
  | IterationRemaining nat

fun wp_single_calc :: 
  "com \<Rightarrow> com \<Rightarrow> pred_post \<Rightarrow> (pred \<times> trace) list" 
where
  "wp_single_calc SKIP c' (OK' Q) =
     [(PFalse, SmallStep SKIP)]"

| "wp_single_calc SKIP c' (ER' Q) =
     [(PFalse, SmallStepER  SKIP)]"

| "wp_single_calc ABORT c' (OK' Q) =
     [(PFalse, SmallStep ABORT)]"

| "wp_single_calc ABORT c' (ER' Q) =
     [(PAnd (PComEq c' SKIP) Q , SmallStepER ABORT)]"

| "wp_single_calc (x ::= a) c' (OK' Q) =
     [(PAnd (PComEq c' SKIP) (subst_pred Q x a), SmallStep (x ::= a))]"

| "wp_single_calc (x ::= a) c' (ER' Q) =
     [(PFalse, SmallStep (x ::= a))]"

| "wp_single_calc (x ::= ND A) c' (OK' Q) =
     (if A = [] then
        [(PAnd (PComEq c' ABORT) Q, SmallStepER (x ::= ND A))]
      else
        map (\<lambda>a. (PAnd (PComEq c' SKIP) (subst_pred Q x a), AssignNDTrace a)) A)"

| "wp_single_calc (x ::= ND A) c' (ER' Q) =
     [(PFalse, SmallStep (x ::= ND A))]"

| "wp_single_calc (c1;;c2) c' (OK' Q) =
    (case c1 of
       SKIP \<Rightarrow>
         [(PAnd (PComEq c' c2) Q, SmallStep SKIP)]
     | _ \<Rightarrow>
         concat (map (\<lambda>c1'.
             map (\<lambda>(p,t).
                 (PAnd (PComEq c' (c1';;c2)) p, SmallStepTrace t))
             (wp_single_calc c1 c1' (OK' Q)))
         (next_com c1)))"

| "wp_single_calc (c1;;c2) c' (ER' Q) =
    (case c1 of
       SKIP \<Rightarrow>
         [(PFalse, SmallStepER SKIP)]
     | _ \<Rightarrow>
         concat (map (\<lambda>c1'.
             map (\<lambda>(p,t).
                 (PAnd (PComEq c' (c1';;c2)) p, SmallStepTrace t))
             (wp_single_calc c1 c1' (ER' Q)))
         (next_com c1)))"

| "wp_single_calc (IF b THEN c1 ELSE c2) c' (OK' Q) =
    [(PAnd (PAnd (PAtom b) (PComEq c' c1)) Q, SmallStepIf True c1),
    (PAnd (PAnd (PAtom (Not b)) (PComEq c' c2)) Q, SmallStepIf False c2)]"

| "wp_single_calc (IF b THEN c1 ELSE c2) c' (ER' Q) =
    [(PFalse, SmallStepER (IF b THEN c1 ELSE c2))]"

| "wp_single_calc (WHILE b DO c) c' (OK' Q) =
    [(PAnd (PComEq c' (IF b THEN c;;WHILE b DO c ELSE SKIP))Q, SmallStep (WHILE b DO c))]"

| "wp_single_calc (WHILE b DO c) c' (ER' Q) =
    [(PFalse, SmallStepER (WHILE b DO c))]"

| "wp_single_calc (SELECT S) c' (OK' Q) =
       map (\<lambda>(b,c).
           (PAnd (PAtom b)(PAnd (PComEq c' c) Q), SmallStepSelect b c))
       S @
       [(PAnd (no_selection S Q) (PComEq c' ABORT), SmallStep (SELECT S))]"

| "wp_single_calc (SELECT S) c' (ER' Q) =
    [(PFalse, SmallStepER (SELECT S))]"

| "wp_single_calc (c1 || c2) c' (OK' Q) =
    (if c1 = SKIP then
       [(PAnd (PComEq c' c2) Q, SmallStep SKIP)]
     else if c2 = SKIP then
       [(PAnd (PComEq c' c1) Q, SmallStep SKIP)]
     else
       (let left_paths =
            concat (map (\<lambda>c1'.
               map (\<lambda>(p,t).
                   (PAnd (PComEq c' (c1' || c2)) p,t))
               (wp_single_calc c1 c1' (OK' Q)))
            (next_com c1));

          right_paths =
            concat (map (\<lambda>c2'.
               map (\<lambda>(p,t).
                   (PAnd(PComEq c' (c1 || c2'))p,t))
               (wp_single_calc c2 c2' (OK' Q)))
            (next_com c2))
        in left_paths @ right_paths))"

| "wp_single_calc (c1 || c2) c' (ER' Q) =
    (if c1 = SKIP \<or> c2 = SKIP then
       [(PFalse, SmallStepER (c1 || c2))]
     else
       (let left_paths =
            concat (map(\<lambda>c1'.
               map(\<lambda>(p,t).
                    (PAnd (PComEq c' (c1' || c2)) p,t))
               (wp_single_calc c1 c1' (ER' Q)))
            (next_com c1));

          right_paths =
            concat (map (\<lambda>c2'.
               map (\<lambda>(p,t).
                   (PAnd (PComEq c' (c1 || c2')) p,t))
               (wp_single_calc c2 c2' (ER' Q)))
           (next_com c2))
        in left_paths @ right_paths))"

fun wp_calc ::
  "nat \<Rightarrow> while_limit \<Rightarrow> com \<Rightarrow> pred_post \<Rightarrow> (pred \<times> trace) list"
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
    concat (map (\<lambda>(p2,t2).
        map (\<lambda>(p1,t1).
            (pred_simp p1, SeqTrace t1 t2))
       (wp_calc n w c1 (OK' p2)))
    (wp_calc n w c2 (OK' Q)))"

| "wp_calc (Suc n) w (c1;;c2) (ER' Q) =
    (let
       xs = wp_calc n w c2 (ER' Q);
       ys = wp_calc n w c1 (ER' Q)
     in
       concat (map (\<lambda>(p2,t2).
           map (\<lambda>(p1,t1).
               (pred_simp p1, SeqTrace t1 t2))
           (wp_calc n w c1 (OK' p2)))
        xs)
       @ ys)"

| "wp_calc (Suc n) w (SELECT S) (OK' Q) =
      (concat (map (\<lambda>(b,c).
          map (\<lambda>(p,t).
              (pred_simp (PAnd (PAtom b) p), SeqTrace (SelectTrace b c) t))
          (wp_calc n w c (OK' Q)))
       S))"

| "wp_calc (Suc n) w (SELECT S) (ER' Q) =
       (concat (map (\<lambda>(b,c).
          map (\<lambda>(p,t).
              (pred_simp (PAnd (PAtom b) p), SeqTrace (SelectTrace b c) t))
          (wp_calc n w c (ER' Q)))
       S)) @
       [(pred_simp (no_selection S Q), BigStep SKIP)]"

| "wp_calc (Suc n) w (AssignND x []) (OK' Q) =
    [(PFalse, BigStep (x ::= ND []))]"

| "wp_calc (Suc n) w (AssignND x []) (ER' Q) =
    [(Q, BigStep (x ::= ND []))]"

| "wp_calc (Suc n) w (AssignND x (S1 # S)) (ER' Q) =
    [(PFalse, BigStep (x ::= ND S))]"

| "wp_calc (Suc n) w (AssignND x (S1 # S)) (OK' Q) =
    concat (map (\<lambda>a.
       map (\<lambda>(p,t).
           (pred_simp p, AssignNDTrace a))
       (wp_calc n w (x ::= a) (OK' Q)))
    (S1 # S))"

| "wp_calc (Suc n) w (IF b THEN c1 ELSE c2) Q =
    filter
      (\<lambda>(p,t). pred_simp p \<noteq> PFalse)
      (append 
        (map (\<lambda>(p,t).
            (pred_simp (PAnd (PAtom b) p), IfTrace b True t))
        (wp_calc n w c1 Q))
        (map (\<lambda>(p,t).
            (pred_simp (PAnd (PAtom (Not b)) p),IfTrace b False t))
        (wp_calc n w c2 Q)))"

| "wp_calc (Suc m) limits (WHILE b DO c) (OK' Q) =
    (let
       (i,n) = limits (WHILE b DO c);
       xs = wp_calc m limits c (OK' Q)
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
                map (\<lambda>(p',t').
                    (pred_simp p', IterationTrace i t t'))
                  (wp_calc m next_limits (WHILE b DO c) (OK' Q'))))
         xs))"

| "wp_calc (Suc m) limits (WHILE b DO c) (ER' Q) =
    (let
       (i,n) = limits (WHILE b DO c);
       xs = 
          if i = 0 then 
            wp_calc m limits c (ER' Q) 
          else 
            wp_calc m limits c (OK' Q)
     in
       concat (map (\<lambda>(p,t).
           (let
              next_limits = limits((WHILE b DO c) := (Suc i,n));
              Q' =
                if i = 0 then
                  pred_simp p
                else
                  pred_simp (PAnd (PAtom b) p)
            in
              if i > n then
                [(PFalse, IterationLimitTrace n)]
              else if Q' = PFalse then
                [(PFalse, IterationRemaining (n-i))]
              else
              [(Q', IterationRemaining (n-i))] @
                map (\<lambda>(p',t').
                    (p', IterationTrace i t t'))
                (wp_calc m next_limits (WHILE b DO c) (OK' Q'))))
         xs))"

| "wp_calc (Suc n) w (c1 || c2) (OK' Q) =
    (if c1 = SKIP then
      map (\<lambda>(p,t).
        (p, ParExitTrace t)) 
      (wp_calc n w c2 (OK' Q))
     else if c2 = SKIP then
       map (\<lambda>(p,t).
        (p, ParExitTrace t)) 
      (wp_calc n w c1 (OK' Q))
     else
       (let
          left_paths =
            concat (map (\<lambda>c1'.
                concat (map (\<lambda>(p,t).
                    map (\<lambda>(p',t').
                        (pred_simp p', ParLeft t' t))
                    (wp_single_calc c1 c1' (OK' p)))
                (wp_calc n w (c1' || c2) (OK' Q))))
            (next_com c1));

          right_paths =
            concat (map (\<lambda>c2'.
                concat (map (\<lambda>(p,t).
                    map (\<lambda>(p',t').
                        (pred_simp p', ParRight t' t))
                    (wp_single_calc c2 c2' (OK' p)))
                (wp_calc n w (c1 || c2') (OK' Q))))
            (next_com c2))
        in left_paths @ right_paths))"

| "wp_calc (Suc n) w (c1 || c2) (ER' Q) =
    (if c1 = SKIP then
       map (\<lambda>(p,t).
          (pred_simp p, ParExitTrace t)) 
      (wp_calc n w c2 (ER' Q))
     else if c2 = SKIP then
       map (\<lambda>(p,t).
          (pred_simp p, ParExitTrace t)) 
      (wp_calc n w c1 (ER' Q))
     else
       (let left_paths =
            concat (map (\<lambda>c1'.
                (let
                   er_first =
                     map (\<lambda>(p,t).
                       (pred_simp p, ParLeft (BigStep c1) t))
                    (wp_single_calc c1 c1' (ER' Q));

                   ok_first =
                     concat (map (\<lambda>(p,t).
                        map (\<lambda>(p',t').
                           (pred_simp p', ParLeft t' t))
                        (wp_single_calc c1 c1' (OK' p)))
                     (wp_calc n w (c1' || c2) (ER' Q)))
                 in er_first @ ok_first))
            (next_com c1));

          right_paths =
            concat (map (\<lambda>c2'.
                (let
                   er_first =
                     map (\<lambda>(p,t).
                        (pred_simp p,ParRight (BigStep c2) t))
                     (wp_single_calc c2 c2' (ER' Q));

                   ok_first =
                     concat (map (\<lambda>(p,t).
                        map (\<lambda>(p',t').
                            (pred_simp p', ParRight t' t))
                         (wp_single_calc c2 c2' (OK' p)))
                     (wp_calc n w (c1 || c2') (ER' Q)))
                 in er_first @ ok_first))
           (next_com c2))
        in left_paths @ right_paths))"

value "
  map
    (\<lambda>(p,t). ( p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      ((''y'' ::= (V ''x'')) ;;
      (WHILE (Less (V ''y'') (N 3))
         DO AssignND ''y''
              [Plus (V ''y'') (N 1),
               Plus (V ''y'') (N 2)]))
      (OK' (PAtom (Less (V ''x'') (N 5)))))"

value "
  map
    (\<lambda>(p,t). (p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      ((''x'' ::= (N 1)) ;;
       AssignND ''y'' [])
      (ER' (PAtom (Less (V ''y'') (N 5)))))"


value "
  map
    (\<lambda>(p,t). (p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      ((AssignND ''y'' []) ;;
       (''x'' ::= (N 1)))
      (ER' (PAtom (Less (V ''y'') (N 5)))))"

value "
  map
    (\<lambda>(p,t). (p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      (SELECT [
        (Less (N 10) (N 5), ''x'' ::= N 1),
        (Less (N 20) (N 5), ''x'' ::= N 2),
        (Less (N 30) (N 5), ''x'' ::= N 3)
      ])
      (ER' (PAtom (Less (V ''x'') (N 10)))))"

value "
  map
    (\<lambda>(p,t). (p, t))
    (wp_calc 10
      (\<lambda>_. (0, 3))
      (SELECT [
        (Less (V ''x'') (N 10),
          AssignND ''y'' []),
        (Less (V ''x'') (N 20),
          ''y'' ::= N 2),
        (Less (V ''x'') (N 30),
          AssignND ''y'' [])
      ])
      (ER' (PAtom (Less (V ''y'') (N 5)))))"

value "
  map
    (\<lambda>(p,t). (p,t))
    (wp_calc 20
      (\<lambda>_. (0,10))
      (WHILE (Less (N 0) (N 1)) DO
        ((''x'' ::= Plus (V ''x'') (N 1));;
          IF (Less (V ''x'') (N 3))
          THEN SKIP
          ELSE AssignND ''y'' []))
      (ER' PTrue))"

value "
  map
    (\<lambda>(p,t). (p,t))
    (wp_calc 20
      (\<lambda>_. (0,10))
      ((''x'' ::= N 1) || (''y'' ::= N 2))
      (OK' PTrue))
"

value "
  map
    (\<lambda>(p,t). (p,t))
    (wp_calc 20
      (\<lambda>_. (0,10))
      ((''x'' ::= N 1) || (''y'' ::= N 2))
      (OK'
        (PAnd
          (PAtom (Less (N 0) (V ''x'')))
          (PAtom (Less (N 0) (V ''y''))))))
"

value "
  map
    (\<lambda>(p,t). (pred_simp p,t))
    (wp_calc 10
      (\<lambda>_. (0,10))
      ((''x'' ::= ND [N 1, N 2, V ''x'']) || (''x'' ::= Plus (V ''x'') (N 10)))
      (OK'
        (PAtom (Equal (V ''x'') (N 11)))))
"
value "
  map
    (\<lambda>(p,t). (pred_simp p,t))
    (filter
      (\<lambda>(p,t). pred_simp p \<noteq> PFalse)
      (wp_calc 10
        (\<lambda>_. (0,10))
        ((''x'' ::= ND [N 1, N 2, V ''x''];;
          ''x'' ::= Plus (V ''x'') (N 5))
          ||
         (''x'' ::= Plus (V ''x'') (N 2);;
          ''x'' ::= Plus (V ''x'') (N 3)))
        (OK'
          (PAtom (Equal (V ''x'') (N 11))))))
"

value "
  map
    (\<lambda>(p,t). (pred_simp p,t))
    (filter
      (\<lambda>(p,t). pred_simp p \<noteq> PFalse)
      (wp_calc 10
        (\<lambda>_. (0,10))
        (SKIP
          ||
         (''x'' ::= ND [];;
          ''x'' ::= N 5))
        (ER' PTrue)))
"

value "
  map
    (\<lambda>(p,t). (pred_simp p,t))
      (wp_calc 10
        (\<lambda>_. (0,10))
        ((''x'' ::= N 1;;
          ''x'' ::= Plus (V ''x'') (N 2))
          ||
         (''x'' ::= ND [];;
          ''x'' ::= Plus (V ''x'') (N 5)))
        (ER' PTrue))
"

value "
  map (\<lambda>(p,t). (pred_simp p,t))
  (wp_single_calc
    (SELECT
      [(Equal (V ''x'') (N 2), ''x'' ::= N 1),
       (Equal (V ''x'') (N 12), ''x'' ::= N 10),
       (Equal (V ''x'') (N 120), ''x'' ::= N 100)])
    (''x'' ::= N 1)
    (OK' PTrue))
"
end