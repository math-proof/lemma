import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace NeronModelInfra

def stalkAlgebraMap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem stalkAlgebraMap_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) (r : R) :
    stalkAlgebraMap f x r =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) :=
  rfl

abbrev stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  (stalkAlgebraMap f x).toAlgebra

abbrev pointAlgebra {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) :
    Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' :=
  (Scheme.stalkClosedPointTo a).hom.toAlgebra

def smoothnessDefect {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) : ℕ∞ :=
  letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
    stalkAlgebra f (a (IsLocalRing.closedPoint R'))
  letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
  Module.length R'
    (Submodule.torsion R'
      (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
        Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))

theorem smoothnessDefect_def {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) :
    smoothnessDefect f a =
      (letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
        stalkAlgebra f (a (IsLocalRing.closedPoint R'))
      letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
      Module.length R'
        (Submodule.torsion R'
          (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
            Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))) :=
  rfl

section Gate

variable (R : Type u) [CommRing R]

theorem stalkAlgebraMap_id (p : PrimeSpectrum R) :
    stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p = (StructureSheaf.toStalk R p).hom := by
  apply RingHom.ext
  intro r
  simp only [stalkAlgebraMap, Scheme.Hom.id_appTop, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_id, RingHom.id_apply, StructureSheaf.toStalk, CommRingCat.hom_comp,
    Scheme.ΓSpecIso_inv, CommRingCat.hom_ofHom]
  rfl

theorem smoothnessDefect_id {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    smoothnessDefect (𝟙 (Spec (CommRingCat.of R))) a = 0 := by
  rw [smoothnessDefect_def]
  set p : PrimeSpectrum R := a (IsLocalRing.closedPoint R') with hp
  letI iRB : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    stalkAlgebra (𝟙 (Spec (CommRingCat.of R))) p
  letI : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p) R' := pointAlgebra a
  have hAlg : iRB = StructureSheaf.stalkAlgebra R p := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    change stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p r = _
    rw [stalkAlgebraMap_id]
    rfl
  have hunr : @Algebra.FormallyUnramified R ((Spec (CommRingCat.of R)).presheaf.stalk p) _ _ iRB := by
    rw [hAlg]
    exact @Algebra.FormallyUnramified.of_isLocalization _ _ _ _ p.asIdeal.primeCompl _
      (StructureSheaf.IsLocalization.to_stalk R p)
  haveI : Subsingleton Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  haveI : Subsingleton
      (R' ⊗[(Spec (CommRingCat.of R)).presheaf.stalk p] Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R]) :=
    inferInstance
  exact Module.length_eq_zero

end Gate

end NeronModelInfra

end

/--
info: 'NeronModelInfra.smoothnessDefect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect

/--
info: 'NeronModelInfra.smoothnessDefect_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.smoothnessDefect_id
