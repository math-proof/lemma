/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

import Def.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


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
