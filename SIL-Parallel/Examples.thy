theory Examples
  imports SIL_Sound_Complete
begin

text \<open>
  This theory contains a collection of simple example programs
  together with proofs of their correctness using the Hoare logic
  developed in the preceding chapters.
\<close>

subsection \<open>Skip\<close>

lemma wp_normalise_example:
  "wp (''x'' ::= ND {N 0,N 1,N 2,N 3,N 4,N 5};;
      (IF Less (V ''x'') (N 2)
       THEN ''x'' ::= N 2
       ELSE SKIP);;
      WHILE Less (V ''x'') (N 5)
      DO ''x'' ::= Plus (V ''x'') (N 1)) (OK (\<lambda>s. s ''x'' = 5)) = (\<lambda>s. True)"
  by force

lemma normalise_example:
  "\<turnstile> \<langle>\<lambda>s. True\<rangle>
      ''x'' ::= ND {N 0,N 1,N 2,N 3,N 4,N 5};;
      (IF Less (V ''x'') (N 2)
       THEN ''x'' ::= N 2
       ELSE SKIP);;
      WHILE Less (V ''x'') (N 5)
      DO ''x'' ::= Plus (V ''x'') (N 1)
    \<langle>OK (\<lambda>s. s ''x'' = 5)\<rangle>"
  by (smt (verit, ccfv_SIG) strengthen_pre wp_is_pre wp_normalise_example)

lemma random_loop:
  "wp (WHILE Less (V ''x'') (N 10)
        DO ''x'' ::= ND {V ''x'',Plus (V ''x'') (N 1)}) (OK (\<lambda>s. s ''x'' = 10)) 
    = (\<lambda>s. s ''x'' \<le> 10)"
  oops


