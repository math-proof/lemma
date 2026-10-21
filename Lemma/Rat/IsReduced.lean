import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma _root_.Algebra.Etale.isReduced_of_field
  {K B : Type*} [Field K] [CommRing B] [Algebra K B] [Algebra.Etale K B] :
  IsReduced B := by
  let _ : Algebra.FormallyUnramified K B :=
    ((Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth).mp
      Algebra.Etale.formallyEtale).1
  let _ : Algebra.EssFiniteType K B := inferInstance
  apply Algebra.FormallyUnramified.isReduced_of_field K B
private lemma Algebra.Etale.isReduced_of_isDomain
  {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.Etale R B] :
  IsReduced B := by
  let K := FractionRing R
  let _ : Algebra.Etale K (TensorProduct R K B) := inferInstance
  let _ : IsReduced (TensorProduct R K B) := Algebra.Etale.isReduced_of_field (K := K)
  apply isReduced_of_injective (Algebra.TensorProduct.includeRight : AlgHom R B (TensorProduct R K B))
  have hRK : Function.Injective (Algebra.linearMap R K) := IsFractionRing.injective R K
  have hrT : Function.Injective (LinearMap.rTensor B (Algebra.linearMap R K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap R K) hRK
  intro b₁ b₂ hb
  have key : ∀ b : B, (Algebra.TensorProduct.includeRight : AlgHom R B (TensorProduct R K B)) b =
      LinearMap.rTensor B (Algebra.linearMap R K) (TensorProduct.tmul R 1 b) := by
    intro b
    simp [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
  rw [key, key] at hb
  simpa using congrArg (TensorProduct.lid R B) (hrT hb)
private lemma _root_.Algebra.Smooth.isReduced_of_field
  {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] :
  IsReduced A := by
  let _ : Algebra.FinitePresentation K A := Algebra.Smooth.finitePresentation
  constructor
  intro a ha
  set J : Ideal A := (Ideal.span {a}).annihilator with hJ
  suffices h1 : (1 : A) ∈ J by
    have := (Submodule.mem_annihilator_span_singleton a 1).mp h1
    simpa using this
  by_contra h1
  have hJne : J ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
  obtain ⟨m, hm, hsub⟩ := Ideal.exists_le_maximal J hJne
  let _ : m.IsPrime := hm.isPrime
  have hsa : Algebra.IsSmoothAt K m := by
    have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus K A := by
      rw [(Algebra.smoothLocus_eq_univ_iff).mpr Algebra.Smooth.formallySmooth]
      trivial
    apply this
  let _ := hsa
  obtain ⟨f, hfm, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := A) (p := m)
  let _ : Algebra.Etale (MvPolynomial (Fin n) K) (Localization.Away f) := inferInstance
  let _ : IsReduced (Localization.Away f) :=
    Algebra.Etale.isReduced_of_isDomain (R := MvPolynomial (Fin n) K)
  have hzero : algebraMap A (Localization.Away f) a = 0 :=
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).mp hzero
  apply hfm
  apply hm.isPrime.mem_of_pow_mem k
  apply hsub
  rw [hJ, Submodule.mem_annihilator_span_singleton]
  rw [smul_eq_mul, hk]
private lemma ringHomSmooth_appTop
  {K : Type u} [Field K] {X : (Scheme : Type (u + 1))}
  [IsAffine X] (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] :
  RingHom.Smooth ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) := by
  apply RingHom.Smooth.comp
  apply RingHom.Smooth.of_bijective
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
  apply HasRingHomProperty.appTop (P := @Smooth) g ‹Smooth g›
private lemma AlgebraicGeometry.isReduced_of_smooth_of_field
  {K : Type u} [Field K] {X : (Scheme : Type (u + 1))} (sX : X ⟶ Spec (CommRingCat.of K)) [Smooth sX] :
  IsReduced X := by
  let _ : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let U := X.affineCover.X i
    let g : U ⟶ Spec (CommRingCat.of K) := X.affineCover.f i ≫ sX
    let _ : IsAffine U := inferInstance
    let _ : Smooth g := inferInstance
    have hψ := ringHomSmooth_appTop g
    let _ : Algebra K (U.presheaf.obj (op ⊤)) :=
      ((g.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    let _ : Algebra.Smooth K (U.presheaf.obj (op ⊤)) := hψ
    let _ : _root_.IsReduced ↑(U.presheaf.obj (op ⊤)) := Algebra.Smooth.isReduced_of_field (K := K)
    apply isReduced_of_isAffine_isReduced U
  apply IsReduced.of_openCover X X.affineCover
/--
[AlgebraicGeometry_isReduced_of_smooth_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_of_field.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] {X : (Scheme : Type (u + 1))} (sX : X ⟶ Spec (CommRingCat.of K)) [Smooth sX] :
  IsReduced X :=
  AlgebraicGeometry.isReduced_of_smooth_of_field sX


-- created on 2026-10-20
