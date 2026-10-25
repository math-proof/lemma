import Lemma.AlgebraicCurve.Correspondence
import Instance.AlgebraicCurve_IsCurveOver
import Abbrev.CerednikDrinfeld_HeckeTower
import Instance.CerednikDrinfeld_HeckeTower

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve


structure TowerData (q q' : ℕ) (Fbase : Type) [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] : Type 1 where

  F : AwayPrime q q' → Type
  [instField : ∀ ℓ, Field (F ℓ)]
  [instAlgebra : ∀ ℓ, Algebra (AlgebraicClosure ℚ) (F ℓ)]
  [instCurve : ∀ ℓ, IsCurveOver (AlgebraicClosure ℚ) (F ℓ)]
  [instEss : ∀ ℓ, Algebra.EssFiniteType (AlgebraicClosure ℚ) (F ℓ)]

  φ : ∀ α : Arr q q', Fbase →ₐ[AlgebraicClosure ℚ] F α.1

  finite : ∀ α : Arr q q', FiniteAlong (AlgebraicClosure ℚ) (φ α)

  integral : ∀ α : Arr q q', (φ α).toRingHom.IsIntegral

attribute [instance] TowerData.instField TowerData.instAlgebra TowerData.instCurve TowerData.instEss

namespace TowerData

variable {Fbase : Type} [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] (T : TowerData q q' Fbase)


end TowerData

end HeckeTower
end CerednikDrinfeld
