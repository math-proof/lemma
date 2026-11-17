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
public import Abbrev.NumberTheory.Cyclotomic.LehmerLaurentIdentity

public section

namespace MetaMathlibExt

/-- `ℚ⟮s⟯ ≤ ℚ⟮ζ⟯`. -/
lemma baseField_le (n : ℕ) :
    baseField n ≤ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [hx]
  apply add_mem
  · exact IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  · exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (zeta n))

end MetaMathlibExt
