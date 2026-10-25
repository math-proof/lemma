import Lemma.AlgebraicCurve.Correspondence
import Instance.AlgebraicCurve_IsCurveOver
import Abbrev.CerednikDrinfeld_HeckeTower
import Instance.CerednikDrinfeld_HeckeTower
import Structure.CerednikDrinfeld_HeckeTower

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve


def arrowDegree (N : ℕ) (α : Arr q q') : ℕ :=
  if (α.1.1 : ℕ) ∣ N then (α.1.1 : ℕ) else (α.1.1 : ℕ) + 1


namespace TowerData

variable {Fbase : Type} [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] (T : TowerData q q' Fbase)

@[reducible] def objField : Obj q q' → Type
  | none => Fbase
  | some ℓ => T.F ℓ

@[reducible] noncomputable def algF (α : Arr q q') : Algebra (T.objField (cod α)) (T.objField (dom α)) :=
  algebraAlong (T.φ α)

theorem isScalarTower_algF (α : Arr q q') :
    letI := T.algF α
    IsScalarTower (AlgebraicClosure ℚ) (T.objField (cod α)) (T.objField (dom α)) :=
  isScalarTower_along (T.φ α)

theorem finiteDimensional_algF (α : Arr q q') :
    letI := T.algF α
    FiniteDimensional (T.objField (cod α)) (T.objField (dom α)) :=
  T.finite α

end TowerData

end HeckeTower
end CerednikDrinfeld
