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
public import Theorem.NumberTheory.Cyclotomic.LehmerLaurentIdentity.Part2

@[expose] public section

namespace MetaMathlibExt

/-- The cleared polynomial `R(X) = Σₖ aₖ X^(e-k) (X²+1)^k`, where `ψ = Σₖ aₖ X^k`
is the real cyclotomic polynomial of degree `e`. -/
noncomputable def clearPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + 1),
    Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
        * (Polynomial.X ^ 2 + 1) ^ k)

end MetaMathlibExt
