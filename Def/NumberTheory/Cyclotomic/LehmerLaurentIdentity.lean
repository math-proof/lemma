/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

module

public import Def.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- The canonical primitive `n`-th root of unity `ζₙ = exp (2 * π * I / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The quadratic `X² - sX + 1` over `ℚ⟮s⟯`, where `s = ζ + ζ⁻¹`. -/
noncomputable def quadPoly (n : ℕ) :
    Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) :=
  Polynomial.X ^ 2 + (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
        IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ * Polynomial.X) + 1)

end MetaMathlibExt
