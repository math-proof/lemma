import Lemma.Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace CerednikDrinfeld.QM

def IsFormalCompletionAlong {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (h : A ⟶ A') (hh : h ≫ f' = f) (φ : Fin g' → MvPowerSeries (Fin g) B) : Prop :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
    ∀ s : Fin g → B', (∀ i, s i ∈ J) →
      θ' B' (fun i => MvFormalGroup.nilEval n (φ i) s) = mapPt h hh (θ B' s)

end CerednikDrinfeld.QM

end
