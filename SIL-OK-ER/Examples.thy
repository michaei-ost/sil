theory Examples
  imports SIL_Sound_Complete
begin

subsection \<open>Skip\<close>

lemma wp_normalise_example:
  "wp (''x'' ::= ND {N 0,N 1,N 2,N 3,N 4,N 5};;
      (IF Less (V ''x'') (N 2)
       THEN ''x'' ::= N 2
       ELSE SKIP);;
      WHILE Less (V ''x'') (N 5)
      DO ''x'' ::= Plus (V ''x'') (N 1)) (OK (\<lambda>s. s ''x'' = 5)) = (\<lambda>s. True)"
  by force

lemma select_example
  "\<turnstile> \<langle>\<lambda>s. s ''x'' \<le> 3\<rangle>
      SELECT [(Less (N 3) (V ''x''), SKIP)]
    \<langle>ER (\<lambda>s. True)\<rangle>"
proof-
  have "\<turnstile> \<langle>\<lambda>s. s ''x'' \<le> 3\<rangle>
      SELECT [(Less (N 3) (V ''x''), SKIP)]
    \<langle>ER (\<lambda>s. s ''x'' \<le> 3)\<rangle>" using tSelectNDNP by auto
  then show "\<turnstile> \<langle>\<lambda>s. s ''x'' \<le> 3\<rangle>
      SELECT [(Less (N 3) (V ''x''), SKIP)]
    \<langle>ER (\<lambda>s. True)\<rangle>" using conseqER
    by (metis (lifting))

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


