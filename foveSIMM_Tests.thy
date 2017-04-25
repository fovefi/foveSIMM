theory foveSIMM_Tests
  imports foveSIMM  "~~/src/HOL/Library/Code_Target_Int"
begin

(* Tests for the fx matrix. *)
value "fx_matrix!0!1"
value "amountInEuro 10 0"
value "amountInEuro 10 1"
value "amountInEuro 10 2"

(* Tests for the pairwise_sum of lists.*)
value "pairwise_sum [3] [5]"
value "3 # [4]"
value "pairwise_sum [2, 3] [4, 5]"
value "pairwise_sum [1, 2, 3] [3, 4, 5]"
value "sum_up_list [[2::real, 3::real], [4::real, 5::real]]"

value "filterList risk_factor_shocks (accumulate_holding_names ''CO'') 
                risk_factor_shock.name"
value "(mapfun risk_factor_shock.shocks (filterList risk_factor_shocks (accumulate_holding_names ''CO'') 
                                            risk_factor_shock.name))"

value "accumulate_holding_names ''CO''"   
value "accumulate_holding_names ''EQ''"   
value "accumulate_holding_names ''IR''"   
value "accumulate_holding_names ''CR''"   


value "risk_factors_asset_type ''IR''"
value "risk_factors_asset_type ''CR''"
value "risk_factors_asset_type ''EQ''"
value "risk_factors_asset_type ''CO''"

value "portfolio_derivative.amount 
       ((filter portfolio_derivatives ''XAU'' portfolio_derivative.name)!0)"


definition IR_risk :: real
   where "IR_risk = asset_risk ''IR''"

definition CR_risk :: real
   where "CR_risk = asset_risk ''CR''"

definition EQ_risk :: real
   where "EQ_risk = asset_risk ''EQ''"

definition CO_risk :: real
   where "CO_risk = asset_risk ''CO''"


value IR_string

value CO_risk
value EQ_risk
value IR_risk
value CR_risk



(*   Asset Class   Var       
 *   ------------- ----------
 *   COMMODITY       564.3703
 *   EQUITY          740.7143
 *   INTEREST_RATE   447.5351
 *   CREDIT           33.3300
 *   ------------- ----------
 *   Total         1,785.9496
 *   ------------- ----------
*)
value "percentile [1,2,3,4,5,6,7,8,9,10,11,12,13,14] 0.97"

value "fx_rate_shocks"


value "percentile (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 0.92"
value "percentile_java (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 0.92"
value "percentile (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 0.99"
value "percentile_java (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 0.99"
value "percentile (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 1"
value "percentile_java (fx_rate_shock.shocks (lookup fx_rate_shocks ''ShocksGBPvsUSD'' 
                   fx_rate_shock.name)) 1"
end
