module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.GaussHypergeometricSummationFrisch.Part2

@[expose] public section

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
