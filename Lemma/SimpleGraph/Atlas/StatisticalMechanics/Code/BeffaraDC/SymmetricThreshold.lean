import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricThreshold
open StatMech StatMech.BeffaraDC


/--
[symmetricThreshold_of_maxInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricThreshold.lean)
-/
@[path]
private lemma symmetricThreshold_of_maxInfluence_eq
  {n edgeCount : ℕ}
  {μ deriv totalInfluence maxInfluence cRusso cMax : ℝ}
-- given
  (hn : 1 ≤ n)
  (hne : n ≤ edgeCount)
  (hμ0 : 0 ≤ μ)
  (hμ1 : μ ≤ 1)
  (hcRusso : 0 ≤ cRusso)
  (hcMax : 0 ≤ cMax)
  (hderiv : cRusso * totalInfluence ≤ deriv)
  (hsymm : (edgeCount : ℝ) / 2 * maxInfluence ≤ totalInfluence)
  (hmax : cMax * μ * (1 - μ) * Real.log (edgeCount : ℝ) / edgeCount ≤ maxInfluence) :
-- imply
  (cRusso * cMax / 2) * μ * (1 - μ) * Real.log (n : ℝ) ≤ deriv := by
-- proof
  apply StatMech.BeffaraDC.symmetricThreshold_of_maxInfluence hn hne hμ0 hμ1 hcRusso hcMax hderiv hsymm hmax


-- created on 2026-10-23
