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
import Theorem.NumberTheory.Cyclotomic.LehmerLaurentIdentity.Part2


namespace MetaMathlibExt

/-- The cleared polynomial `R(X) = Σₖ aₖ X^(e-k) (X²+1)^k`, where `ψ = Σₖ aₖ X^k`
is the real cyclotomic polynomial of degree `e`. -/
noncomputable def clearPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + 1),
    Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
        * (Polynomial.X ^ 2 + 1) ^ k)

end MetaMathlibExt
