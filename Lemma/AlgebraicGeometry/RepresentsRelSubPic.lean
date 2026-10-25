import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Structure.JacJ1Iface
import Structure.AlgebraicGeometry_RepresentsRelSubPic

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}


def SubPicCondition.top (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ _ => True
  unit_mem := fun _ => trivial
  congr := fun _ _ _ _ _ => trivial
  pullback_mem := fun _ _ _ _ _ => trivial


namespace RepresentsRelSubPic

variable {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

noncomputable def classify (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) : SchemeHomOver t D.toBase :=
  (h.univ t M hM).choose

theorem classify_spec (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) :
    Nonempty ((h.poincare.pullbackAlong (h.classify t M hM)).L ≅ M.L) :=
  (h.univ t M hM).choose_spec.1

theorem classify_unique (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) (g : SchemeHomOver t D.toBase)
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L)) : g = h.classify t M hM :=
  (h.univ t M hM).unique hg (h.classify_spec t M hM)

theorem ext_of_iso (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (g g' : SchemeHomOver t D.toBase)
    (hgg' : Nonempty ((h.poincare.pullbackAlong g).L ≅ (h.poincare.pullbackAlong g').L)) : g = g' := by
  have hmem : P.P t (h.poincare.pullbackAlong g') := P.pullback_mem _ _ g' _ h.poincare_mem
  have h1 := h.classify_unique t _ hmem g hgg'
  have h2 := h.classify_unique t _ hmem g' ⟨Iso.refl _⟩
  exact h1.trans h2.symm

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard
