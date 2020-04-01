/************************************************************************
Author: Aluisio J D Barros
Email: abarros@equidade.org
Date: 2010, 2012, April 14, Jan 15, Jun 17, Mar 18

This program calculates both the slope index of inequality (SII) and the
relative index of inequality (RII) using a logistic regression model.

This approach is suitable for binary outcomes where the probability of
the outcome is estimated, instead of its mean.

The logistic model avoids adjusted values out of the zero-one interval
that sometimes happen when a linear model is used for binary outcomes.

Version history
April 2014 - corrected for the case where SII/RII were calculated even when the rank variable was missing for all obs.

Jan 2015 - adjustments made to situations where the coverage is very high (~1) or very low (~0) in several of the quintiles, results would be unstable. 
           We now replace these values with .99 or .01 to improve the results. The SII is probably still an overestimate.

Jun 2017 - Sort stable is now in use to make the results be the same in every run of the routine.  

Mar 2018 - A line was added to drop from the dataset missing variables for either the stratifier or outcome.

Jan 2019 - the observed probabilities for each group are now calculated using a logistic model as well, with the stratifier as a categorical variable in the model.
           This allows weights to be taken into account properly. Also, a change in the outcome from 1 to .99 and 0 to .01 was removed. The code was changed to 
           include the clusters in the model using a local macro instead of if's. 
*************************************************************************/

/************************************************************************
Usage:

siilogit rankvar outcomevar [if] [in] [w=weightvar], cluster(clustervar) [nograph]

rankvar must be ordinal and ordered so that low is poor/worst and high is rich/best

The use of w=weight allows for the use a (sample) weights.
The use of cluster(clustervar) allows for clustered samples.
If the option nograph is used, the graph to check for linearity is not displayed.

Example:

siilogit v190 sba [w=v005], cluster(v021)
*************************************************************************/


program define siilogit, rclass
version 11.0

syntax varlist(max=3 numeric) [if] [in] [fweight/] , [CONTinous] [Cluster(varname numeric)] [NOGRaph]

*** Values to 1, 2 e 3
tokenize `varlist'
preserve
quietly {
  set more off
  
  *** Apply "if" and "in" restrictions and remove missings for concentration variable
  gen byte _use = 1 `if' `in'
  keep if _use==1                                               // drop observations not to be used in the temporary dataset
  drop if missing(`1',`2')                                      // drop observations missing for either rank or outcome variables
  
  *** Check for variables being missing
  inspect `1'
  if r(N) == 0 {
    di as error "Error! Rank variable [" "`1'" "] is missing for all observations."
    error 416
  }
  inspect `2'
  if r(N) == 0 {
    di as error "Error! Outcome variable [" "`2'" "] is missing for all observations."
    error 416
  }
  keep if `2' ~=.
  *replace `2' = .99 if `2' > .99                               // I DONT UNDERSTAND WHY THIS HERE
  *replace `2' = .01 if `2' < 0.01
  
  *** Id rank variable
  local rkv `1'
  tabulate `rkv'
  local grouped = r(N)==r(r)                                    // local macro grouped = 1 if no. of observations = no. of groups
  if r(r)>20 {                                                  // too many groups to calculate SII/RII
    noisily display _newline as error "Error! too many groups in ranking variable" _newline
    return scalar er = 1
    error 1001                                                  // program aborts
  }
  
  if `grouped' == 1 {
    
    *** Create midpoints for ranked groups === GROUPED DATA
    sort `rkv', stable
    if "`exp'" == "" gen _freq=1
    else gen _freq = `exp'
    sum _freq
    gen _rfi =_freq / r(sum)
    gen _rfcum = sum(_rfi)
    gen _rkmidp =_rfi/2 + _rfcum[_n-1]
    replace _rkmidp = _rfi/2 in 1
  }
  else {
    
    *** Create midpoints for ranked groups === MICRODATA
    sort `rkv', stable
    tab `rkv', g(_group)
    if "`exp'" == "" gen _freq=1
    else gen _freq = `exp'
    sum _freq
    gen _rfi =_freq / r(sum)
    gen _rfcum = sum(_rfi)
    by `rkv', sort: egen _rkmidp=mean( _rfcum)
  }
  
  *** Logistic regression fitted with weights and clusters
  describe, short                                               // This block adds two observations
  local nobs2 = r(N)+2                                          // including values 0 and 1 for 
  local nobs1 = r(N)+1                                          // the midpoint rank
  set obs `nobs2'                                               // so that the graph includes a line that goes
  replace _rkmidp=0 in `nobs2'                                  // from zero to one
  replace _rkmidp=1 in `nobs1'                                  // end of block
  
  *** Define the condition of using clusters or not
  if "`cluster'" == "" {
    local vcecond                                               // condition is blank
  }
  else {
    local vcecond  vce(cluster `cluster')                       // condition is vce(cluster var)
  }
  
  *** Estimating fitted values for each group (as a categorical variable)
  capture glm `2' i.`rkv' [pw=_freq], f(bin) l(logit) `vcecond' search iterate(100)
  if _rc==0 {
    predict _om                                                 // predicted probabilities from the model
    gen _lom = logit(cond(_om==0,.01,cond(_om==1,.99,_om)))     // logit observed probabilities
  }
  
  
  *** Fitting the model that will be used for calculating the SII 
  capture glm `2' _rkmidp [pw=_freq], f(bin) l(logit) `vcecond' search iterate(100)
  if _rc==0 {
    return scalar er = 0
    predict _pm                                                 // predicted probabilities from the model
    gen _lpm = logit(_pm)                                       // logit predicted probabilities
    
    *** Estimating the SII
    noisily nlcom SII: exp(_b[_cons]+_b[_rkmidp]) / (1+exp(_b[_cons] +_b[_rkmidp])) - exp(_b[_cons])/(1+exp(_b[_cons])), post noheader
    mat def sii=e(b)
    mat def siise=e(V)
    return scalar sii = sii[1,1]
    return scalar sii_se = sqrt(siise[1,1])
    
    *** Estimating the RII 
    capture glm `2' _rkmidp [pw=_freq], f(bin) l(logit) `vcecond' search iterate(100)
    noisily nlcom RII: (exp(_b[_cons]+_b[_rkmidp]) / (1+exp(_b[_cons] +_b[_rkmidp]))) / (exp(_b[_cons])/(1+exp(_b[_cons]))), post noheader
    mat def rii=e(b)
    mat def riise=e(V)
    return scalar rii = rii[1,1]
    return scalar rii_se = sqrt(riise[1,1])
    
    *** Graph to check for linearity
    if "`nograph'"=="" {
      noisily sc _lom _lpm  _rkmidp, c(. l) s(o i) xlabel(0 (.1) 1) legend(label(1 "Observed") label(2 "Fitted")) xtitle(Fractional rank) ytitle(Logit prob.)
    }
  }
  else {
    noisily display _newline as error "Error calculating SII/RII" _newline
    return scalar er = 1
    error 999
  }
} // end quietly

end // program

