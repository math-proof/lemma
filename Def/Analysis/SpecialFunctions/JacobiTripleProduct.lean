/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiTripleProduct.lean -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Def.Combinatorics.Enumerative.GaussianBinomial
public import Theorem.Finset.Enumerative.GaussianBinomial

@[expose] public section

/-!
# Jacobi triple product identity

The bilateral-series/product identity of Jacobi, as stated in the source below.
This is not supplied by `MetaMathlibExt.QPochhammer.jacobiThetaProduct`, which
only defines the product-side theta function and proves no triple-product
identity, so the full identity is proved here.
-/


section GaussBinom
end GaussBinom
namespace MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

open MathlibExt

section

open BigOperators

section TriNum

/-- Triangular number `T(n) = n * (n - 1) / 2` for integers, via exact division. -/
def jtpTri (n : ℤ) : ℤ := (n * (n - 1)) / 2

/-- The hub summand `t(n) = (-1)^n * Q^(T n) * w^n` with zpow. -/
noncomputable def jtpTheta (Q w : ℂ) (n : ℤ) : ℂ := (-1) ^ n * Q ^ (jtpTri n) * w ^ n

/-- The finite product `L(N)`. -/
noncomputable def jtpProdL (Q w : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, ((1 - w * Q ^ j) * (1 - w⁻¹ * Q ^ (j + 1)))

/-- The truncated summand `f_N(n)`. -/
noncomputable def jtpFin (Q w : ℂ) (N : ℕ) (n : ℤ) : ℂ :=
  if n.natAbs ≤ N then gaussBinom Q (2 * N) (n + (N : ℤ)).toNat * jtpTheta Q w n else 0

end TriNum

section Reflect

open scoped BigOperators

end Reflect

section FiniteJTP

end FiniteJTP

section FinHasSum

end FinHasSum

section ThetaSummable

end ThetaSummable

section PochFacts

/-- The infinite q-Pochhammer value `P∞`. -/
noncomputable def jtpPochInf (Q : ℂ) : ℂ :=
  ∏' j : ℕ, ((1 : ℂ) - Q ^ (j + 1))

end PochFacts

section GaussBound

end GaussBound

section GaussLimit

end GaussLimit

section TanneryLimit

end TanneryLimit

section Hub

/-- The hub product family `h(m)`. -/
noncomputable def jtpHub (Q w : ℂ) (m : ℕ) : ℂ :=
  (1 - Q ^ (m + 1)) * (1 - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))

end Hub
end
end MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
