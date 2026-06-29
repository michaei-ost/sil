section "IMP --- A Simple Imperative Language"

theory Com_SIL imports BExp begin

datatype
  com = SKIP 
      | Assign vname aexp       (\<open>_ ::= _\<close> [1000, 61] 61)
      | AssignND  vname "int  set"    (\<open>_ ::= ND _\<close> [1000, 61] 61)
      | Seq    com  com         (\<open>_;;/ _\<close>  [60, 61] 60)
      | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
      | SelectND " (bexp  \<times> com) list" (\<open>SELECT _\<close> [0] 61)
      | ChoiceND "com list" (\<open>CHOICE _ ]\<close> [0] 61)
      | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)

end
