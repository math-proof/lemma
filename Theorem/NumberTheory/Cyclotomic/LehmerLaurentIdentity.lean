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
import Abbrev.NumberTheory.Cyclotomic.LehmerLaurentIdentity


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
