import Mathlib
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Abbrev.GoodReductionJacobian_RelativeGroupLawAction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

def actionFstPoint (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.fst (ι ≫ f) f ≫ ι, by rw [Category.assoc, pullback.condition]⟩

def actionSndPoint (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.snd (ι ≫ f) f, rfl⟩

def action (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) : pullback (ι ≫ f) f ⟶ J :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1

theorem action_def (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι = (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1 := rfl

@[simp] theorem actionFstPoint_coe (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionFstPoint ι).1 = pullback.fst (ι ≫ f) f ≫ ι := rfl

@[simp] theorem actionSndPoint_coe (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionSndPoint ι).1 = pullback.snd (ι ≫ f) f := rfl

theorem action_over (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι ≫ f = actionSource f ι :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).2

end GoodReductionJacobian.RelativeGroupLaw

end
