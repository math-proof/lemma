import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma ringHom_flat_of_torsionFree
  {R A : Type u} [CommRing R] [IsDedekindDomain R] [CommRing A] (r : RingHom R A)
  (htf : ∀ (c : R) (s : A), c ≠ 0 → r c * s = 0 → s = 0) :
  -- imply
  r.Flat := by
  -- proof
  let _ : Algebra R A := r.toAlgebra
  let _ : Module.IsTorsionFree R A := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c s hcs
    if hc : c = 0 then
      apply Or.inl hc
    else
      apply Or.inr (htf c s hc _)
      simp [Algebra.smul_def] at hcs
      apply hcs
  show Module.Flat R A
  infer_instance

private lemma torsionFree_of_ringHom_flat
  {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] (r : RingHom R A) (hr : r.Flat)
  (c : R) (s : A) (hc : c ≠ 0) (hcs : r c * s = 0) :
  -- imply
  s = 0 := by
  -- proof
  let _ : Algebra R A := r.toAlgebra
  let _ : Module.Flat R A := hr
  let _ : Module.IsTorsionFree R A := inferInstance
  have h0 : c • s = c • (0 : A) := by
    rw [smul_zero, Algebra.smul_def]
    apply hcs
  refine (IsRegular.of_ne_zero hc).isSMulRegular h0

private lemma flat_appLE_iff
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :
  -- imply
  RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom ↔ RingHom.Flat ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (U : X.Opens) le_top).hom := by
  -- proof
  rw [CommRingCat.hom_comp]
  apply (RingHom.Flat.respectsIso.cancel_left_isIso _ _).symm

private lemma flat_iff
  {R : Type u} [CommRing R] [IsDedekindDomain R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R)) :
  -- imply
  Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : X.presheaf.obj (Opposite.op (U : X.Opens))), c ≠ 0 → ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 := by
  -- proof
  constructor
  ·
    intro hf U c s hc hcs
    have h1 : RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom := HasRingHomProperty.appLE (P := @Flat) f hf ⟨⊤, isAffineOpen_top _⟩ U le_top
    rw [flat_appLE_iff] at h1
    apply torsionFree_of_ringHom_flat _ h1 c s hc hcs
  ·
    intro htf
    refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : X.affineOpens => U) (iSup_affineOpens_eq_top X) (fun U => ?_)
    rw [flat_appLE_iff]
    apply ringHom_flat_of_torsionFree _ (fun c s hc hcs => htf U c s hc hcs)

/--
[AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDedekindDomain R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R)) :
  -- imply
  Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : X.presheaf.obj (Opposite.op (U : X.Opens))), c ≠ 0 → ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 :=
  flat_iff f


-- created on 2026-10-20
