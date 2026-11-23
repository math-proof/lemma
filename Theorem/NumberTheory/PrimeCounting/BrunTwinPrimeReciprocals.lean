/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Def.NumberTheory.SelbergSieve
public import Theorem.Nat.SelbergSieve
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals

/-!
# Brun's theorem on twin-prime reciprocals

This file records the convergence of the reciprocal series over twin-prime pairs.
-/

public section


section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open MathlibExt.SelbergSieve

@[simp] theorem brunNu_apply (d : ℕ) : brunNu d = (brunRho d : ℝ) / (d : ℝ) := rfl

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted
end
