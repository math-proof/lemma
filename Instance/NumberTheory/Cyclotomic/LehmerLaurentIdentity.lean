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
public import Theorem.NumberTheory.Cyclotomic.LehmerLaurentIdentity

@[expose] public section

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
