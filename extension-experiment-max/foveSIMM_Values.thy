(* Version 0.4, last changed 2019-02-01
 * (C) fovefi ltd, www.fovefi.co 
 * (author: Manfred Kerber [make@fovefi.co])
 *
 * Dually licenced under
 * Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
 * ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
 * See LICENSE files for details.
 * (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
 *
 * In this file we redefine the example given in openSIMM in Isabelle/HOL.
 *)

(*text \<open>
  See values in
  @{file "../OpenSIMM/src/main/java/com/opengamma/opensimm/src/test/resources/"}
\<close>

*)

theory foveSIMM_Values
  imports  "~~/src/HOL/Library/Complex_Main" "~~/src/HOL/Library/Code_Target_Int"
begin

(* There are three currencies in the example, EUR, USD, and GBP. The reference (main) currency in
 * the example is EUR, that is, the risks are all converted to EUR. *)
definition currencies :: "(string list)"
  where "currencies = [''EUR'', ''USD'', ''GBP'']"

(* The currencies are represented by the 0, 1, and 2 for EUR, USD, and GBP, resp. *)
type_synonym currency = nat

definition EUR :: currency
    where "EUR = 0"
definition USD :: currency
    where "USD = 1"
definition GBP :: currency
    where "GBP = 2"

(* The method returns the currency number of the corresponding string. *)
fun get_currency_number :: "string \<Rightarrow> nat" where
  "get_currency_number x = (if (x = ''EUR'')
                          then 0
                          else (if (x = ''USD'')
                                then 1
                                else 2))"

(* The lemma states that EUR and USD are different currencies. *)
lemma [simp]:
  shows Euro_neq_Dollar: "EUR \<noteq> USD"
    and Dollar_neq_Euro: "USD \<noteq> EUR"
  by (auto simp add: EUR_def USD_def)

chapter \<open>Declaration of the values in the example\<close>

(* The matrix is used for the conversion of the three currencies, order EUR, USD, GBP. Values
 * taken from fx-rates.csv, completed to a full matrix. *)
definition fx_matrix:: "real list list"
  where "fx_matrix = 
         [[1, 7/5, 7/8],
          [5/7, 1, 5/8],
          [8/7, 8/5, 1]]
        "
(* Next we introduce the fx-rate-shocks taken from fx-rate-shocks.csv *)
record fx_rate_shock =
  name :: string
  currency :: nat
  shocks :: "real list"

definition fx_rate_shocks_source :: "fx_rate_shock list"
  where "fx_rate_shocks_source =
      [
        \<lparr> name = ''USD'', currency = EUR, shocks = [1, 1.001, 0.9975, 0.995, 1.0002, 1.01, 0.995, 0.997, 1.001, 1.0002,
1.01, 0.995, 0.997, 1.001, 1.0002, 1.01, 0.995, 0.997, 1.001, 1.0002,
1.01, 0.995, 0.997, 1.001, 1.0002] \<rparr>,

        \<lparr> name = ''GBP'', currency = USD, shocks = [0.9985, 1.002, 1, 0.995, 1.0003, 1.01, 0.994, 0.996, 1.001, 1.0002,
1.01, 1.005, 0.9999, 0.9999, 1.0011, 1.005, 0.996, 0.998, 1.0025, 1.01,
0.995, 0.997, 1.001, 1.0002, 1.0001] \<rparr>
     ]"

chapter \<open>Basic computations\<close>

(* Let a list be given such as [(a,b,c,''d''),...]. The function produces sublist of
 * elements for which the selector on an element is equal to the compare element. For instance,
 * value "filter fx_rate_shocks ''USD'' fx_rate_shock.name" will give the values in the fx_rate_shocks
 * list where the name of the shock is ''USD''. *)
fun filter :: "('a list) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a list)"
  where "filter [] compare selector = []" |
        "filter (x#xs) compare selector =
         (if (selector x) = compare
             then x # (filter xs compare selector)
             else filter xs compare selector)"

(* Let a non-empty list be given such as [(a,b,c,''d''),...],
 * the lookup function returns the first corresponding element in the list. *)
fun lookup
  where "lookup list compare selector = 
      (filter list compare selector)!0"   

(* mapfun applies a function fun to a list (x#xs) *)
fun mapfun where
  "mapfun fun [] = []" |
  "mapfun fun (x#xs) = (fun x) # (mapfun fun xs)"   

fun mapfun2 where
  "mapfun2 fun [][] = []" |
  "mapfun2 fun (x#xs) (y#ys) = (fun x y) # (mapfun2 fun xs ys)" |
  "mapfun2 fun xs ys = undefined"   

value "get_currency_number ''USD''"
value "(fx_rate_shock.shocks (lookup fx_rate_shocks_source ''USD'' fx_rate_shock.name))"

(* The shocks of USD are converted to EUR. *)
definition USD_shocks_in_euros
  where "USD_shocks_in_euros = mapfun (\<lambda> usd. (usd - 1) * (fx_matrix!0!(get_currency_number ''USD'')))
                     (fx_rate_shock.shocks (lookup fx_rate_shocks_source ''USD'' fx_rate_shock.name))"

(* The EUR value of the GBP is calculated via USD. The following definition makes the conversion according to the 
 * conversion performed in the openSIMM computation in which the shocks to the GBP are combined
 * with the shocks to USD. *)
definition GBP_shocks_in_euros
  where "GBP_shocks_in_euros = mapfun2 
           (\<lambda> usd. \<lambda> gbp. fx_matrix!0!(get_currency_number ''USD'')/
                          fx_matrix!(get_currency_number ''GBP'')!(get_currency_number ''USD'') * 
                           (usd/gbp -1))
             (fx_rate_shock.shocks (lookup fx_rate_shocks_source ''USD'' fx_rate_shock.name))
             (fx_rate_shock.shocks (lookup fx_rate_shocks_source ''GBP'' fx_rate_shock.name))"

(* The shocks for the three currencies used in the example. *)
definition fx_rate_shocks :: "fx_rate_shock list"
  where "fx_rate_shocks =
      [ \<lparr> name = ''USD'', currency = 0, shocks = USD_shocks_in_euros\<rparr>,
        \<lparr> name = ''GBP'', currency = 0, shocks = GBP_shocks_in_euros \<rparr>,
        \<lparr> name = ''EUR'', currency = 0, shocks = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]  \<rparr>
      ]"

(* portfolio-derivatives from portfolio-derivatives.csv 
 * RiskFactorName, Amount,   Currency *)
record portfolio_derivative =
  name :: string
  amount :: int
  currency :: currency

definition portfolio_derivatives :: "portfolio_derivative list"
  where "portfolio_derivatives =
         [
            \<lparr> name = ''EUR_OIS_2Y'',   amount = 100000,   currency = EUR \<rparr>,
            \<lparr> name = ''EUR_OIS_5Y'',   amount = -20000,   currency = EUR \<rparr>,
            \<lparr> name = ''USD_IRSL3M_2Y'',amount =  20000,   currency = EUR \<rparr>,
            \<lparr> name = ''IBM'',          amount =   30300,  currency = EUR \<rparr>,
            \<lparr> name = ''SP500'',        amount =  100000,  currency = USD \<rparr>,
            \<lparr> name = ''XAU'',          amount = -123456,  currency = USD \<rparr>,
            \<lparr> name = ''EUR'',          amount = 1000000,  currency = EUR \<rparr>,
            \<lparr> name = ''USD'',          amount = -1400000, currency = GBP \<rparr>,
            \<lparr> name = ''GBP'',          amount =  200000,  currency = USD \<rparr>
         ]"

(* portfolio-initial-margin from portfolio-initial-margin.csv 
 * RiskFactorName, Amount,   Currency*)
record portfolio_initial_margin =
  name :: string
  amount :: int
  currency :: currency

definition portfolio_initial_margins :: "portfolio_initial_margin list"
  where "portfolio_initial_margins =
     [
       \<lparr> name = ''USD_IRSL3M_2Y'', amount =  2000,    currency = EUR \<rparr>,
       \<lparr> name =''USD'',            amount = -1300000, currency = GBP \<rparr>
     ]"

(* portfolio-initial-margin from portfolio-initial-margin.csv 
 * RiskFactorName, Amount,   Currency *)
record portfolio_variation_margin =
  name :: string
  amount :: int
  currency :: currency

definition portfolio_variation_margins :: "portfolio_variation_margin list"
  where "portfolio_variation_margins =
     [
       \<lparr> name =''GBP'',            amount = 150000, currency = USD \<rparr>
     ]"

(* risk-factor-base-levels from risk-factor-base-levels.csv 
 * RiskFactorName, BaseLevel *)
record risk_factor_base_level =
   name :: string
   base_level :: real

definition risk_factor_base_levels :: "risk_factor_base_level list"
   where "risk_factor_base_levels =
             [
                     \<lparr> name = ''EUR_OIS_2Y'',  base_level = -0.0005 \<rparr>,
                     \<lparr> name = ''EUR_OIS_5Y'',  base_level =  0.0025 \<rparr>,
                     \<lparr> name = ''USD_IRSL3M_2Y'', base_level = 0.01 \<rparr>,
                     \<lparr> name = ''IBM'',         base_level =  0.012 \<rparr>,
                     \<lparr> name = ''SP500'',       base_level =  1000 \<rparr>,
                     \<lparr> name =''XAU'',          base_level =  1200 \<rparr>
             ]"
(* risk-factor-definitions from risk-factor-definitions.csv 
 * RiskFactorName, AssetClass, RiskType,    ShockType, Shift *)
record risk_factor =
  name :: string
  asset_class :: string
  risk_type :: string
  shock_type :: string
  shift :: real

definition risk_factors :: "risk_factor list"
  where "risk_factors =
         [
           \<lparr> name = ''EUR_OIS_2Y'',       asset_class = ''IR'',  
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''EUR_OIS_5Y'',       asset_class = ''IR'',         
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''USD_IRSL3M_2Y'',    asset_class = ''IR'',
             risk_type = ''SENSITIVITY'', shock_type = ''RE'', shift = 0.04\<rparr>,
           \<lparr> name = ''IBM'',              asset_class = ''CR'',   
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''SP500'',            asset_class = ''EQ'', 
             risk_type = ''EXPOSURE'',    shock_type = ''RE'', shift = 0.0\<rparr>,
           \<lparr> name = ''XAU'',              asset_class = ''CO'',
             risk_type = ''EXPOSURE'',    shock_type = ''RE'', shift = 0.0\<rparr>
         ]"

(* risk-factor-shocks from risk-factor-shocks.csv
 * RiskFactorName, Shocks *)

record risk_factor_shock =
  name :: string
  shocks :: "(real list)"

definition risk_factor_shocks :: "risk_factor_shock list"
   where "risk_factor_shocks =
             [
               \<lparr> name = ''EUR_OIS_2Y'',  shocks = [0.0001, -0.0005, -0.005, 0, 0.0002, 0.0001, -0.0005,
                                 -0.005, 0.0001, -0.0005, -0.005, 0, 0, 0.0002, 0.0001,
                                 -0.0005, -0.005, 0, 0.0002, 0.0002, 0.0001, -0.0005,
                                 -0.005, 0, 0.0002]\<rparr>,
               \<lparr> name = ''EUR_OIS_5Y'', shocks = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]\<rparr>,
               \<lparr> name = ''USD_IRSL3M_2Y'', shocks = [1.0025, 1.0025, 0.9975, 0.9975, 1, 1, 1.0025, 0.9975, 1,
                                    1, 1, 1, 1, 1, 1.0025, 0.9975, 1, 1, 1, 1, 1.0025,
                                    0.9975, 1, 1, 1]\<rparr>,
               \<lparr> name = ''IBM'', shocks = [0.0001, -0.0005, -0.005, 0.0002, -0.0006, -0.0051, 0.0003,
                          -0.0007, -0.0052, 0, 0.0004, -0.0001, 0.0011, 0.0008, 0.0012]\<rparr>,
               \<lparr> name = ''SP500'', shocks = [1.011, 0.995, 0.997, 1.001, 1.0002, 1.01, 0.9955, 0.9975,
                            1.0012, 1.0003, 1.0101, 0.9951]\<rparr>,
               \<lparr> name = ''XAU'',   shocks = [1.01, 0.995, 0.997, 1.001, 0.9955, 1.0002, 1.011, 0.994,
                          0.9975, 1.003, 0.99, 1.0004, 1.012, 0.9945]\<rparr>
             ]"

(* The risk level, i.e., the var level, in the example is 0.9. *)
definition "var_level = 0.9"
end
