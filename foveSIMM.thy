section \<open>A Formalization of the Standard Model\<close>

(* Version 0.1, started 2016-07-21, last changed 2017-04-19 
 * Copyright: fovefi ltd, all rights reserved 
 *)

theory foveSIMM 
  imports Percentile Currency  "~~/src/HOL/Library/Code_Target_Int"
begin

(*****************************************************************************************)
(*****************************************************************************************)
chapter \<open>Declaration of some values as an example\<close>
(*****************************************************************************************)
(*****************************************************************************************)

(* Initially we want to reproduce the numbers from the opensimm implementation,
 * that is, the following Var values:
 *   ------------- ----------
 *   Asset Class   Var       
 *   ------------- ----------
 *   COMMODITY       564.3703
 *   EQUITY          740.7143
 *   INTEREST_RATE   447.5351
 *   CREDIT           33.3300
 *   ------------- ----------
 *   Total         1,785.9496
 *   ------------- ----------
 *)

(* The matrix is used for the conversion of the three currencies, order EUR, USD, GBP *)
definition fx_matrix:: "real list list"
  where "fx_matrix = 
         [[1, 7/5, 7/8],
          [5/7, 1, 5/8],
          [8/7, 8/5, 1]]
        "

(* Next we introduce the values in the example *)
(* fx-rate-shocks from fx-rate-shocks.csv*)
record fx_rate_shock =
  name :: string
  shocks :: "real list"

definition fx_rate_shocks :: "fx_rate_shock list"
  where "fx_rate_shocks =
      [
        \<lparr> name = ''ShocksEURvsUSD'', shocks = [1, 1.001, 0.9975, 0.995, 1.0002, 1.01, 0.995, 0.997, 1.001, 1.0002,
1.01, 0.995, 0.997, 1.001, 1.0002, 1.01, 0.995, 0.997, 1.001, 1.0002,
1.01, 0.995, 0.997, 1.001, 1.0002] \<rparr>,

        \<lparr> name = ''ShocksGBPvsUSD'', shocks = [0.9985, 1.002, 1, 0.995, 1.0003, 1.01, 0.994, 0.996, 1.001, 1.0002,
1.01, 1.005, 0.9999, 0.9999, 1.0011, 1.005, 0.996, 0.998, 1.0025, 1.01,
0.995, 0.997, 1.001, 1.0002, 1.0001] \<rparr>
      ]"

(* portfolio-derivatives from portfolio-derivatives.csv *)
(* Need to adjust currency *)
type_synonym portfolio_derivative_type = "string \<times> real \<times> currency"
(* RiskFactorName, Amount,   Currency *)
record portfolio_derivative =
  name :: string
  amount :: int
  currency :: currency

definition portfolio_derivatives :: "portfolio_derivative list"
  where "portfolio_derivatives =
         [
            \<lparr> name = ''EUR_OIS_2Y'',   amount = 100000, currency = EUR \<rparr>,
            \<lparr> name = ''EUR_OIS_5Y'',   amount = -20000, currency = EUR \<rparr>,
            \<lparr> name = ''USD_IRSL3M_2Y'',amount =  20000, currency = EUR \<rparr>,
            \<lparr> name = ''IBM'',         amount =   30300, currency = EUR \<rparr>,
            \<lparr> name = ''SP500'',       amount =  100000, currency = USD \<rparr>,
            \<lparr> name = ''XAU'',         amount = -123456, currency = USD \<rparr>,
            \<lparr> name = ''EUR'',         amount = 1000000, currency = EUR \<rparr>,
            \<lparr> name = ''USD'',        amount = -1400000, currency = GBP \<rparr>,
            \<lparr> name = ''GBP'',         amount =  200000, currency = USD \<rparr>
         ]"

(* portfolio-initial-margin from portfolio-initial-margin.csv *)
(* RiskFactorName, Amount,   Currency*)
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

(* risk-factor-base-levels from risk-factor-base-levels.csv *)
(* RiskFactorName, BaseLevel *)
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
(*risk-factor-definitions from risk-factor-definitions.csv *)

record risk_factor =
  name :: string
  asset_class :: string
  risk_type :: string
  shock_type :: string
  shift :: real

(* RiskFactorName, AssetClass, RiskType,    ShockType, Shift *)
(* better as record? better own type for IR, CR, EQ, CO then also case analysis by case, or  *)
definition risk_factors :: "risk_factor list"
  where "risk_factors =
         [
           \<lparr> name = ''EUR_OIS_2Y'',   asset_class = ''IR'',  
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''EUR_OIS_5Y'',   asset_class = ''IR'',         
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''USD_IRSL3M_2Y'', asset_class = ''IR'',
             risk_type = ''SENSITIVITY'', shock_type = ''RE'', shift = 0.04\<rparr>,
           \<lparr> name = ''IBM'',            asset_class = ''CR'',   
             risk_type = ''SENSITIVITY'', shock_type = ''AB'', shift = 0.0\<rparr>,
           \<lparr> name = ''SP500'',          asset_class = ''EQ'', 
             risk_type = ''EXPOSURE'',  shock_type = ''RE'', shift = 0.0\<rparr>,
           \<lparr> name = ''XAU'',            asset_class = ''CO'',
             risk_type = ''EXPOSURE'', shock_type = ''RE'', shift = 0.0\<rparr>
         ]"

(* risk-factor-shocks from risk-factor-shocks.csv *)
(* RiskFactorName, Shocks *)

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

definition "var_level = 0.9"

definition ir_string :: string
   where "ir_string = ''IR''"
definition co_string :: string
   where "co_string = ''CO''"
definition eq_string :: string
   where "eq_string = ''EQ''"
definition cr_string :: string
   where "cr_string = ''CR''"

(*************************** END EXAMPLE *****************************************)

(*****************************************************************************************)
(*****************************************************************************************)
chapter \<open>Computation of sums\<close>
(*****************************************************************************************)
(*****************************************************************************************)


(* Let a list be given such as [(a,b,c,''d''),...]. The function produces sublist of
 * elements for which the selector on an element is equal to the compare element.  *)
fun filter :: "('a list) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a list)"
  where "filter [] compare selector = []" |
        "filter (x#xs) compare selector =
         (if (selector x) = compare
             then x # (filter xs compare selector)
             else filter xs compare selector)"

(* let a non-empty list be given such as [(a,b,c,''d''),...] 
   we want to lookup the corresponding element in the list/ *)
fun lookup
  where "lookup list compare selector = 
     (filter list compare selector)!0"

(* The asset type of a risk factor is returned. *)
fun risk_factors_asset_type
  where "risk_factors_asset_type asset_type = filter risk_factors asset_type asset_class"


(* Converts a given amount in the corresponding EUR amount *)
fun amount_in_euro :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "amount_in_euro value_in_curr xcurr = value_in_curr * fx_matrix!xcurr!0"

(* Lookup the amount of a given asset. *)
fun get_amount :: "string \<Rightarrow> real"
  where "get_amount asset_name = portfolio_derivative.amount
              (lookup portfolio_derivatives asset_name portfolio_derivative.name)" 

(* Lookup the currency of a given asset. *)
fun get_currency :: "string \<Rightarrow> currency"
   where "get_currency asset_name = portfolio_derivative.currency
              (lookup portfolio_derivatives asset_name portfolio_derivative.name)"

(* Lookup whether a given asset is relative (True) or not (False). *)
fun get_relative :: "string \<Rightarrow> bool"
  where "get_relative asset_name = 
          (let shock_type = risk_factor.shock_type
              (lookup risk_factors asset_name risk_factor.name) 
           in (if shock_type = ''RE''
               then True
               else False))"

(* Lookup the shift of a given asset. *)
fun get_shift :: "string \<Rightarrow> real"
  where "get_shift asset_name = risk_factor.shift
              (lookup risk_factors asset_name risk_factor.name)"

(* Lookup the base level (current value) of a given asset. *)
fun get_base_level :: "string \<Rightarrow> real"
   where "get_base_level asset_name = risk_factor_base_level.base_level
              (lookup risk_factor_base_levels asset_name risk_factor_base_level.name)"

(* Lookup the shocks of a given asset. *)
fun get_shocks :: "string \<Rightarrow> (real list)"
   where "get_shocks asset_name = risk_factor_shock.shocks
            (lookup risk_factor_shocks asset_name risk_factor_shock.name)"

(* Lookup the shock type of a given asset. *)
fun get_shock_type :: "string \<Rightarrow> bool"
   where "get_shock_type asset_name = 
          (if (risk_factor.shock_type  
                 (lookup risk_factors asset_name risk_factor.name)) = 
              ''AB''
           then True 
           else False)"

(* Lookup the sensitivity of a given asset, if type is SENSITIVITY then True, else (i.e., 
  if type is EXPOSURE) False. *)
fun get_sensitivity :: "string \<Rightarrow> bool"
   where "get_sensitivity asset_name = 
           (if (risk_factor.risk_type 
                   (lookup risk_factors asset_name risk_factor.name)) = 
                ''SENSITIVITY''
           then True
           else False)"

(* The market level is computed as the base level plus the shock assumed
 * the asset is given in absolute terms; if it is given in relative terms
 * then the market level is the shock times the base level minus the shift value.
 *)
fun compute_market_level :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real" 
  where "compute_market_level shock local_base_level shift_value is_relative =
       (if is_relative 
        then (local_base_level * shock - shift_value)
        else local_base_level + shock)"

(* profitLoss are computed - depending of whether it is a sensitivity or not - as the market level minus the base level
 * in EUR times the amount, if necessary normalized by the base level. 
 *)
fun profit_loss :: "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> nat
                   \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real"
   where "profit_loss x_shock x_is_sensitivity x_amount x_curr x_base_level x_shift_value x_is_relative =
          (if x_is_sensitivity
           then x_amount * (amount_in_euro 
                            ((compute_market_level x_shock x_base_level x_shift_value x_is_relative)
                              - x_base_level) x_curr)
           else x_amount * (amount_in_euro 
                           (((compute_market_level x_shock x_base_level x_shift_value x_is_relative)
                               - x_base_level) / x_base_level) x_curr))"

(* mapfun applies a function fun to a list (x#xs) *)
fun mapfun where
  "mapfun fun [] = []" |
  "mapfun fun (x#xs) = (fun x) # (mapfun fun xs)"   

(* The simulated profit loss is the application of the profitLoss function to all the shocks. *)
fun simulated_profit_loss :: "string \<Rightarrow> (real list)"
   where "simulated_profit_loss asset =
            (let shocks :: (real list) =  get_shocks asset;
                 is_sensitivity :: bool = get_sensitivity asset;
                 x_amount :: real = get_amount asset;
                 x_curr :: nat = get_currency asset;
                 base_level :: real     =  get_base_level asset;
                 is_relative  :: bool  = get_relative asset;
                 shift :: real = get_shift asset 
           in mapfun (\<lambda> x. (profit_loss x is_sensitivity x_amount x_curr base_level shift is_relative)) shocks)" 

(* The names of the risk factors in the list. *)
fun names_of :: "(risk_factor list) \<Rightarrow> (string list)"
   where "names_of l = mapfun risk_factor.name l" 

(* The function returns all the holdings in a particular risk category *) 
fun accumulate_holding_names :: "string \<Rightarrow> (string list)"
  where "accumulate_holding_names str =
     (let (risk_factor_of_type :: (risk_factor list)) =
               filter risk_factors str risk_factor.asset_class
     in names_of risk_factor_of_type)"

(*
value "accumulate_holding_names ''CO''"
value "accumulate_holding_names ''EQ''"
value "accumulate_holding_names ''CR''"
value "accumulate_holding_names ''IR''"
*)

(* member returns True if an element is member of a list, else False. *)
fun member where
   "member el [] = False" |
   "member el (xs#x) = (if (el=xs) then True else member el x)"

(* sum sums up the values in a list of real values. *)
fun sum :: "(real list) \<Rightarrow> real" where
  "sum [] = 0" |
  "sum (xs#x) = xs + sum x"

(* pairwise_sum takes two lists of real values of equal lengths and returns a list of
 * equal lengths with the pairwise sum of the elements.
 *)
fun pairwise_sum :: "(real list) \<Rightarrow> (real list) \<Rightarrow> (real list)" where
  "pairwise_sum [] [] = []" |
  "pairwise_sum (xs#x) (ys#y) = ((xs + ys)#(pairwise_sum x y))" |
  "pairwise_sum xs ys = []" (* In all non-matching cases the empty list is returned. *)

(* sum_up_list takes a list of  lists of real values of equal lengths and returns a list of
 * equal lengths with the sums of the corresponding elements.
 *)
fun sum_up_list :: "((real list) list) \<Rightarrow> (real list)" where
    "sum_up_list [] = []" |
    "sum_up_list [xs] = xs" |
    "sum_up_list (xs#(ys#x)) = (sum_up_list ((pairwise_sum xs ys)#x))"

(* Compute the risk in a particular asset class. *)
fun asset_risk :: "string \<Rightarrow> real"
   where "asset_risk local_risk_type =
  (let holding_names = accumulate_holding_names local_risk_type;
       risk_list = (sum_up_list (mapfun simulated_profit_loss holding_names))
    in percentile risk_list var_level)"


(*****************************************************************************************)
(*****************************************************************************************)
chapter \<open>Code extraction\<close>
(*****************************************************************************************)
(*****************************************************************************************)
(* The following code exports the functions and defined constants to scala. *)
export_code ir_string co_string eq_string cr_string percentile asset_risk fx_matrix fx_rate_shocks 
            portfolio_derivatives risk_factors risk_factor_shocks 
            in Scala module_name foveSIMM file "foveSIMM_scala_src/foveSIMM_without_main.scala"
end
