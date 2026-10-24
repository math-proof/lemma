import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_IsCurveOver

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve

abbrev AwayPrime (q q' : ℕ) : Type := {ℓ : Nat.Primes // (ℓ : ℕ) ≠ q ∧ (ℓ : ℕ) ≠ q'}

abbrev Obj (q q' : ℕ) : Type := Option (AwayPrime q q')

abbrev Arr (q q' : ℕ) : Type := AwayPrime q q' × Fin 2

variable {q q' : ℕ}

abbrev dom (α : Arr q q') : Obj q q' := some α.1

abbrev cod (_α : Arr q q') : Obj q q' := none

def arrowDegree (N : ℕ) (α : Arr q q') : ℕ :=
  if (α.1.1 : ℕ) ∣ N then (α.1.1 : ℕ) else (α.1.1 : ℕ) + 1

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

@[reducible] def objField : Obj q q' → Type
  | none => Fbase
  | some ℓ => T.F ℓ

instance instFieldObj : ∀ j : Obj q q', Field (T.objField j)
  | none => inferInstanceAs (Field Fbase)
  | some ℓ => inferInstanceAs (Field (T.F ℓ))

instance instAlgebraObj : ∀ j : Obj q q', Algebra (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra (AlgebraicClosure ℚ) (T.F ℓ))

instance instCurveObj [IsCurveOver (AlgebraicClosure ℚ) Fbase] : ∀ j : Obj q q', IsCurveOver (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) (T.F ℓ))

instance instEssFiniteTypeObj [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase] :
    ∀ j : Obj q q', Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.F ℓ))

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
