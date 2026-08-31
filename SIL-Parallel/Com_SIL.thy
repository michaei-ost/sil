section "IMP --- A Simple Imperative Language"

theory Com_SIL imports BExp begin

datatype
  com = SKIP | ABORT
      | Assign vname aexp       (\<open>_ ::= _\<close> [1000, 61] 61)
      | AssignND  vname "aexp  set"    (\<open>_ ::= ND _\<close> [1000, 61] 61)
      | Seq    com  com         (\<open>_;;/ _\<close>  [60, 61] 60)
      | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
      | SelectND " (bexp  \<times> com) list" (\<open>SELECT _\<close> [0] 61)
      | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)
      | Par   com  com         (\<open>_||/ _\<close>  [60, 61] 60)

fun isSequential :: "com \<Rightarrow> bool" where
  "isSequential (Par _ _)      = False" |
  "isSequential (Seq c1 c2)    = (isSequential c1 \<and> isSequential c2)" |
  "isSequential (If b c1 c2)   = (isSequential c1 \<and> isSequential c2)" |
  "isSequential (While b c)    = isSequential c" |
  "isSequential (SelectND xs)  = (\<forall>(b,c) \<in> set xs. isSequential c)" |
  "isSequential _              = True"

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


end
