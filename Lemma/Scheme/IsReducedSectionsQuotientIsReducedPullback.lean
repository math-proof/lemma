import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isReduced_quotient_of_isReduced_tensorProduct
  [CommRing R] [Field κ] [Algebra R κ]
  (ϖ : R) (hϖ : algebraMap R κ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
  (B : Type*) [CommRing B] [Algebra R B] [_root_.IsReduced (TensorProduct R B κ)] :
    _root_.IsReduced (B ⧸ Ideal.span {algebraMap R B ϖ}) := by
  set I : Ideal R := Ideal.span {ϖ} with hI
  let _ : I.IsMaximal := hmax
  let _ : Field (R ⧸ I) := Ideal.Quotient.field I
  have hIle : ∀ r ∈ I, Algebra.ofId R κ r = 0 := by
    intro r hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [map_mul, show Algebra.ofId R κ ϖ = algebraMap R κ ϖ from rfl, hϖ, mul_zero]
  let ι : AlgHom R (R ⧸ I) κ := Ideal.Quotient.liftₐ I (Algebra.ofId R κ) hIle
  let _ : Algebra (R ⧸ I) κ := ι.toRingHom.toAlgebra
  let _ : IsScalarTower R (R ⧸ I) κ := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R κ r = ι (Ideal.Quotient.mk I r)
    simp [ι]
  have hmap : I.map (algebraMap R B) = Ideal.span {algebraMap R B ϖ} := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  let e : RingEquiv (B ⧸ Ideal.span {algebraMap R B ϖ}) (TensorProduct R B (R ⧸ I)) :=
    (Ideal.quotEquivOfEq hmap.symm).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv
  let g : AlgHom R (TensorProduct R B (R ⧸ I)) (TensorProduct R B κ) := Algebra.TensorProduct.map (AlgHom.id R B) ι
  have hmk : Function.Injective (TensorProduct.mk (R ⧸ I) κ (TensorProduct R (R ⧸ I) B) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := R ⧸ I) (B := κ) (TensorProduct R (R ⧸ I) B)
  have hg : ∀ x, g x = TensorProduct.comm R κ B (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) κ B (TensorProduct.mk (R ⧸ I) κ (TensorProduct R (R ⧸ I) B) 1 (TensorProduct.comm R B (R ⧸ I) x))) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      simp [g, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.comm_tmul, TensorProduct.mk_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => simp [map_add, hx, hy]
  have hginj : Function.Injective g := by
    intro x y hxy
    rw [hg, hg] at hxy
    apply (TensorProduct.comm R B (R ⧸ I)).injective (hmk ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) κ B).injective ((TensorProduct.comm R κ B).injective hxy)))
  let _ : _root_.IsReduced (TensorProduct R B (R ⧸ I)) := isReduced_of_injective g hginj
  apply isReduced_of_injective e e.injective

/--
[AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_sections_quotient_of_isReduced_pullback.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {κ : Type u} [Field κ] (φ : RingHom R κ) (ϖ : R)
  (hϖ : φ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback f (Spec.map (CommRingCat.ofHom φ)))]
  (V : X.Opens) (hV : IsAffineOpen V) :
    let _ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
    _root_.IsReduced ((X.presheaf.obj (op V)) ⧸ Ideal.span {algebraMap R (X.presheaf.obj (op V)) ϖ}) := by
  let _ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  let _ := φ.toAlgebra
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.obj (op V)))) = hV.fromSpec ≫ f := by
    change Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV le_top]
  let j : Spec (CommRingCat.of (TensorProduct R (X.presheaf.obj (op V)) κ)) ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
    (pullbackSpecIso R (X.presheaf.obj (op V)) κ).inv ≫ (pullback.congrHom e₁ rfl).hom ≫
    (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) hV.fromSpec).inv ≫
    pullback.snd hV.fromSpec (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))
  let _ : IsOpenImmersion j := inferInstance
  let _ : IsReduced (Spec (CommRingCat.of (TensorProduct R (X.presheaf.obj (op V)) κ))) := isReduced_of_isOpenImmersion j
  let _ : _root_.IsReduced (TensorProduct R (X.presheaf.obj (op V)) κ) := (affine_isReduced_iff (CommRingCat.of (TensorProduct R (X.presheaf.obj (op V)) κ))).mp inferInstance
  apply isReduced_quotient_of_isReduced_tensorProduct (κ := κ) ϖ hϖ hmax (X.presheaf.obj (op V))


-- created on 2026-10-20
