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
import Theorem.NumberTheory.Cyclotomic.LehmerLaurentIdentity


namespace MetaMathlibExt

/-- Tower algebra `ℚ⟮s⟯ → ℚ⟮ζ⟯` from the inclusion. -/
noncomputable instance towerAlgebra (n : ℕ) : Algebra ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  (IntermediateField.inclusion (baseField_le n)).toRingHom.toAlgebra

/-- Tower property for `ℚ → ℚ⟮s⟯ → ℚ⟮ζ⟯`. -/
noncomputable instance towerIsScalarTower (n : ℕ) : IsScalarTower ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    have hcomm := (IntermediateField.inclusion (baseField_le n)).commutes x
    have hdef : ∀ y : ↥(baseField n),
        algebraMap ↥(baseField n)
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) y
        = IntermediateField.inclusion (baseField_le n) y := fun y => rfl
    rw [hdef]
    exact hcomm)

end MetaMathlibExt
