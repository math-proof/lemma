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
public import Def.NumberTheory.Cyclotomic.LehmerLaurentIdentity

@[expose] public section


namespace MetaMathlibExt

/-- `ℚ⟮s⟯`, the base field for the quadratic step, where `s = ζ + ζ⁻¹`. -/
noncomputable abbrev baseField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)

end MetaMathlibExt
