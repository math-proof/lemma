import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.GaussHypergeometricSummationFrisch.Part2
open Finset Filter Topology

/-!
# Gauss summation specialized to Frisch's binomial identity
-/


namespace MetaMathlibExt

section

-- Step 5: finite product and induction on beta
noncomputable def Pprod (C c : ℝ) (β : ℕ) : ℝ :=
  ∏ j ∈ Finset.range β, ((C - ((j : ℝ) + 1)) / (c - ((j : ℝ) + 1)))

end
end MetaMathlibExt
