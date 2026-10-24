import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
open Finset StatMech StatMech.FrontierA


/--
[analyticAt_hadamardQuadraticFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticAt_hadamardQuadraticFactor_eq
  {r : Real}
  {z : ℂ} :
-- imply
  AnalyticAt ℂ (hadamardQuadraticFactor r) z := by
-- proof
  apply StatMech.FrontierA.analyticAt_hadamardQuadraticFactor r z

/--
[hasDerivAt_hadamardQuadraticFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma hasDerivAt_hadamardQuadraticFactor_eq
  {r : Real}
  {z : ℂ} :
-- imply
  HasDerivAt (hadamardQuadraticFactor r) (2 * (r : ℂ) * z) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_hadamardQuadraticFactor r z

/--
[analyticOrderAt_hadamardQuadraticFactor_eq_one_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardQuadraticFactor_eq_one_of_zero_eq
  {r : Real}
  {z : ℂ}
-- given
  (hr : 0 < r)
  (hz : hadamardQuadraticFactor r z = 0) :
-- imply
  analyticOrderAt (hadamardQuadraticFactor r) z = 1 := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_hadamardQuadraticFactor_eq_one_of_zero hr hz

/--
[analyticOrderAt_hadamardQuadraticFactor_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardQuadraticFactor_eq_zero_of_ne_eq
  {r : Real}
  {z : ℂ}
-- given
  (hz : hadamardQuadraticFactor r z ≠ 0) :
-- imply
  analyticOrderAt (hadamardQuadraticFactor r) z = 0 := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_hadamardQuadraticFactor_eq_zero_of_ne hz

/--
[analyticOrderAt_hadamardQuadraticFactor_eq_ite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardQuadraticFactor_eq_ite_eq
  {r : Real}
  {z : ℂ}
-- given
  (hr : 0 < r) :
-- imply
  analyticOrderAt (hadamardQuadraticFactor r) z = if hadamardQuadraticFactor r z = 0 then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_hadamardQuadraticFactor_eq_ite hr z

/--
[analyticOrderAt_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticOrderAt_finset_prod_eq
  {s : Finset ι}
  {f : ι → ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
-- imply
  analyticOrderAt (fun w => ∏ i ∈ s, f i w) z = ∑ i ∈ s, analyticOrderAt (f i) z := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_finset_prod s f z hf

/--
[analyticOrderAt_hadamardQuadraticFactor_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean)
-/
@[path]
private lemma analyticOrderAt_hadamardQuadraticFactor_prod_eq
  {s : Finset ι}
  {r : ι → Real}
  {z : ℂ}
-- given
  (hr : ∀ i ∈ s, 0 < r i) :
-- imply
  analyticOrderAt (fun w => ∏ i ∈ s, hadamardQuadraticFactor (r i) w) z = (#{i ∈ s | hadamardQuadraticFactor (r i) z = 0} : Nat) := by
-- proof
  apply StatMech.FrontierA.analyticOrderAt_hadamardQuadraticFactor_prod s r hr z


-- created on 2026-10-23
