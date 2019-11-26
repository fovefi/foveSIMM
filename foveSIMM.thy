text \<open> Version 0.5, last changed 2019-02-01
  (C) fovefi ltd, www.fovefi.co 
  (author: Manfred Kerber [make@fovefi.co])
 
  Dually licenced under
  Creative Commons Attribution (CC-BY) 4.0 [https://creativecommons.org/licenses/by/4.0/]
  ISC License (1-clause BSD License)       [https://www.isc.org/downloads/software-support-policy/isc-license/]
  See LICENSE files for details.
  (Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
 
  In this file we redefine the example given in openSIMM in Isabelle/HOL.
 \<close>

section \<open>A Formalization of the Standard Model\<close>

theory foveSIMM
  imports  Percentile_Code foveSIMM_Values  "~~/src/HOL/Library/Code_Target_Int"
begin

text \<open> The asset type of a risk factor is returned. In the example, the asset types are ''CO'', ''EQ'', 
     ''IR'', and ''CR''. \<close>
fun risk_factors_asset_type
  where "risk_factors_asset_type asset_type = filter risk_factors asset_type asset_class"

text \<open> Converts a given amount in the corresponding EUR amount \<close>
fun amount_in_euro :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "amount_in_euro value_in_curr xcurr = value_in_curr * fx_matrix!xcurr!0"

text \<open> The method looks up the amount of a given asset. If the asset is not in the corresponding list, the
  amount is returned as 0. \<close>
fun get_amount_portfolio_derivative :: "string \<Rightarrow> real"
  where "get_amount_portfolio_derivative asset_name = 
          (let derivatives = (filter portfolio_derivatives asset_name portfolio_derivative.name)
           in
           (if derivatives = []
            then 0
            else portfolio_derivative.amount (derivatives!0)))"

text \<open> The method looks up the initial margin of a given asset. If the asset is not in the corresponding list, the
  amount is returned as 0. \<close>
fun get_amount_portfolio_initial_margin :: "string \<Rightarrow> real"
  where "get_amount_portfolio_initial_margin asset_name =
          (let initial_margins = (filter portfolio_initial_margins asset_name portfolio_initial_margin.name)
           in
           (if initial_margins = []
            then 0
            else portfolio_initial_margin.amount (initial_margins!0)))"

text \<open> The method looks up the variation margin of a given asset. If the asset is not in the corresponding list, the
  amount is returned as 0. \<close>
fun get_amount_portfolio_variation_margin :: "string \<Rightarrow> real"
  where "get_amount_portfolio_variation_margin asset_name = 
          (let portfolio_variation_margins = (filter portfolio_variation_margins asset_name portfolio_variation_margin.name)
           in
           (if portfolio_variation_margins = []
            then 0
            else portfolio_variation_margin.amount (portfolio_variation_margins!0)))"

text \<open> The method returns the amount of a given asset as the difference of the amount of derivatives
  minus the initial margin minus the variation margin. \<close>
fun get_amount :: "string \<Rightarrow> real"
  where "get_amount asset_name = (get_amount_portfolio_derivative asset_name) -
                                 (get_amount_portfolio_initial_margin asset_name) -
                                 (get_amount_portfolio_variation_margin asset_name)"

text \<open> Look up the currency in which a given asset is noted. \<close>
fun get_currency :: "string \<Rightarrow> currency"
   where "get_currency asset_name = portfolio_derivative.currency
              (lookup portfolio_derivatives asset_name portfolio_derivative.name)"

text \<open> Lookup whether a given asset is relative (True) or not (False). Per default it is not.\<close>
fun get_relative :: "string \<Rightarrow> bool"
  where "get_relative asset_name = 
          (if (filter risk_factors asset_name risk_factor.name) = []
            then False
            else
          (let shock_type = risk_factor.shock_type
              (lookup risk_factors asset_name risk_factor.name) 
           in (if shock_type = ''RE''
               then True
               else False)))"

text \<open> Lookup the shift of a given asset. By default it is 0. \<close>
fun get_shift :: "string \<Rightarrow> real"
  where "get_shift asset_name = 
        (if (filter risk_factors asset_name risk_factor.name) = []
            then 0
            else
        risk_factor.shift
              (lookup risk_factors asset_name risk_factor.name))"

text \<open> Lookup the base level (current value) of a given asset. By default it is 0.\<close>
fun get_base_level :: "string \<Rightarrow> real"
  where "get_base_level asset_name = 
        (if (filter risk_factor_base_levels asset_name risk_factor_base_level.name) = []
          then 0
        else risk_factor_base_level.base_level
              (lookup risk_factor_base_levels asset_name risk_factor_base_level.name))"

text \<open> Lookup the shocks of a given asset, separately for currencies (type FX) and others.\<close>
fun get_shocks :: "string \<Rightarrow> (real list)"
  where "get_shocks (asset_name :: string) = (if (List.member currencies asset_name)
             then (fx_rate_shock.shocks (lookup fx_rate_shocks asset_name fx_rate_shock.name))
             else (risk_factor_shock.shocks
            (lookup risk_factor_shocks asset_name risk_factor_shock.name)))"

text \<open> Lookup the shock type of a given asset (absolute vs relative). \<close>
fun get_shock_type :: "string \<Rightarrow> bool"
   where "get_shock_type asset_name = 
          (if (risk_factor.shock_type  
                 (lookup risk_factors asset_name risk_factor.name)) = 
              ''AB''
           then True 
           else False)"

text \<open> Lookup the sensitivity of a given asset, if type is SENSITIVITY then True, else (i.e., 
  if type is EXPOSURE) False. \<close>
fun get_sensitivity :: "string \<Rightarrow> bool"
   where "get_sensitivity asset_name = 
           (if  (filter risk_factors asset_name risk_factor.name) = [] \<or>
                (risk_factor.risk_type 
                   (lookup risk_factors asset_name risk_factor.name)) = 
                ''SENSITIVITY''
           then True
           else False)"

text \<open> The market level is computed as the base level plus the shock assumed
  the asset is given in absolute terms; if it is given in relative terms
  then the market level is the shock times the base level minus the shift value.
 \<close>
fun compute_market_level :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> real" 
  where "compute_market_level shock local_base_level shift_value is_relative is_sensitivity =
       (if is_relative 
              then  (if is_sensitivity
                   then (shock - 1)  * (local_base_level + shift_value)
                   else shock  * local_base_level)
        else (if is_sensitivity
                   then shock
                   else shock * (local_base_level + shift_value)))"

text \<open> profitLoss are computed - depending of whether it is a sensitivity or not - as the market level minus the base level
  in EUR times the amount, if necessary normalized by the base level. \<close>
fun profit_loss :: "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> nat
                   \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real"
   where "profit_loss x_shock x_is_sensitivity x_amount x_curr x_base_level x_shift_value x_is_relative =
          (if x_is_sensitivity
           then (amount_in_euro 
                            (x_amount * (compute_market_level x_shock x_base_level x_shift_value x_is_relative x_is_sensitivity))
                             x_curr) 
           else (amount_in_euro 
                           (x_amount * (((compute_market_level x_shock x_base_level x_shift_value x_is_relative x_is_sensitivity)
                               - x_base_level) / x_base_level)) x_curr))"

text \<open> The simulated profit loss is the application of the profitLoss function to all the shocks. \<close>
fun simulated_profit_loss :: "string \<Rightarrow> (real list)"
  where "simulated_profit_loss asset =
      (if (List.member currencies asset)
            then 
             (let shocks :: (real list) =  get_shocks asset;
                  x_amount :: real = get_amount asset
              in mapfun (\<lambda> (x::real). 
                    (amount_in_euro (amount_in_euro x (get_currency asset)) (get_currency_number asset)) *  x_amount) shocks)
          else
           (let shocks :: (real list) =  get_shocks asset;
                 is_sensitivity :: bool = get_sensitivity asset;
                 x_amount :: real = get_amount asset;
                 x_curr :: nat = get_currency asset;
                 base_level :: real     =  get_base_level asset;
                 is_relative  :: bool  = get_relative asset;
                 shift :: real = get_shift asset 
           in mapfun (\<lambda> x. (profit_loss x is_sensitivity x_amount x_curr 
                            base_level shift is_relative)) shocks))" 

text \<open> The names of the risk factors in the list. \<close>
fun names_of :: "(risk_factor list) \<Rightarrow> (string list)"
   where "names_of l = mapfun risk_factor.name l" 

text \<open> The function returns all the holdings in a particular risk category \<close> 
fun accumulate_holding_names_aux :: "string \<Rightarrow> (string list)"
  where "accumulate_holding_names_aux str =
     (let (risk_factor_of_type :: (risk_factor list)) =
               filter risk_factors str risk_factor.asset_class
     in names_of risk_factor_of_type)"

text \<open> The function determines the assets which is given by looking them up in the 
  risk_factor_of_type list, except for the ''IR'' class, where the currencies need to be added. \<close>
fun accumulate_holding_names :: "string \<Rightarrow> (string list)"
   where "accumulate_holding_names str =
   (if  str = ''IR''
        then (currencies @ (accumulate_holding_names_aux str))
        else (accumulate_holding_names_aux str))"

text \<open> sum sums up the values in a list of real values. \<close>
fun sum :: "(real list) \<Rightarrow> real" where
  "sum [] = 0" |
  "sum (xs#x) = xs + sum x"

text \<open> pairwise_sum takes two lists of real values of equal lengths and returns a list of
  equal lengths with the pairwise sum of the elements.
 \<close>
fun pairwise_sum :: "(real list) \<Rightarrow> (real list) \<Rightarrow> (real list)" where
  "pairwise_sum [] [] = []" |
  "pairwise_sum (xs#x) (ys#y) = ((xs + ys)#(pairwise_sum x y))" |
  "pairwise_sum xs ys = []" text \<open> In all non-matching cases the empty list is returned. \<close>

text \<open> sum_up_list takes a list of lists of real values of equal lengths and returns a list of
  equal lengths with the sums of the corresponding elements.
 \<close>
fun sum_up_list :: "((real list) list) \<Rightarrow> (real list)" where
    "sum_up_list [] = []" |
    "sum_up_list [xs] = xs" |
    "sum_up_list (xs#(ys#x)) = (sum_up_list ((pairwise_sum xs ys)#x))"

text \<open> Compute the risk in a particular asset class. \<close>
fun asset_risk :: "string \<Rightarrow> real"
   where "asset_risk local_risk_type =
  (let holding_names = accumulate_holding_names local_risk_type;
       risk_list = (sum_up_list (mapfun simulated_profit_loss holding_names))
    in percentile_impl risk_list var_level)"

text \<open> The total risk is the some of the risks in the categories ''CO'', ''EQ'',
  ''IR'', and ''CR'' \<close>
definition total_risk :: real
  where "total_risk = (asset_risk ''CO'') + (asset_risk ''EQ'') +
                      (asset_risk ''IR'') + (asset_risk ''CR'')"

text \<open> We want to reproduce the numbers from the openSIMM implementation,
  that is, the following Var values:
    ------------- ----------
    Asset Class   Var       
    ------------- ----------
    COMMODITY       564.3703
    EQUITY          740.7143
    INTEREST_RATE   447.5351
    CREDIT           33.3300
    ------------- ----------
    Total         1,785.9496
    ------------- ----------
 \<close>

value GBP_shocks_in_euros
value "fx_matrix!0!(get_currency_number ''USD'')"
value "fx_matrix!(get_currency_number ''GBP'')!(get_currency_number ''USD'')"
value " fx_matrix!0!(get_currency_number ''USD'')/
                          fx_matrix!(get_currency_number ''GBP'')!(get_currency_number ''USD'')"

(* We get with the values as defined in foveSIMM_Values.thy: *)
value "asset_risk ''CO''" (* 493824 / 875       =   564.3702857142857... *)
value "asset_risk ''EQ''" (* 5185 / 7           =   740.7142857142857... *)
value "asset_risk ''IR''" (* 12493389 / 27916   =   447.5350694941969... *)
value "asset_risk ''CR''" (* 3333 / 100         =    33.33               *)
value "total_risk"        (* 222573974 / 124625 =  1785.9496409227684... *)

chapter \<open>Code extraction\<close> 

text \<open> The following code exports the functions and defined constants to scala in a directory
       foveSIMM_scala_src. \<close>
export_code percentile_impl asset_risk fx_matrix fx_rate_shocks 
            portfolio_derivatives risk_factors risk_factor_shocks
            in Scala module_name foveSIMM 
            file "foveSIMM_scala_src/foveSIMM_without_main.scala"
end
