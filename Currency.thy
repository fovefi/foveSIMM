(* Version 0.1, started around 2016-11-01, last changed 2017-04-12 
 * Copyright: fovefi ltd, all rights reserved 
 * In this file, currencies are model via natural numbers: 
 *  0 for EUR, 1 for USD, and 2 for GBP.
 *)

theory Currency
  imports  "~~/src/HOL/Library/Complex_Main"
begin

type_synonym currency = nat

definition EUR :: currency
    where "EUR = 0"
definition USD :: currency
    where "USD = 1"
definition GBP :: currency
    where "GBP = 2"

(* The lemma states that EUR and USD are different currencies. *)
lemma [simp]:
  shows Euro_neq_Dollar: "EUR \<noteq> USD"
    and Dollar_neq_Euro: "USD \<noteq> EUR"
  by (auto simp add: EUR_def USD_def)

end

