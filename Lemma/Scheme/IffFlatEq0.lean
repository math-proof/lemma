import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R A : Type*} [CommRing R] [CommRing A]
private lemma ringHom_flat_of_torsionFree [IsDedekindDomain R] (r : R →+* A)
    (htf : ∀ (c : R) (s : A), c ≠ 0 → r c * s = 0 → s = 0) : r.Flat := by
  let _ : Algebra R A := r.toAlgebra
  let _ : Module.IsTorsionFree R A := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c s hcs
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (htf c s hc (by simp [Algebra.smul_def] at hcs; exact hcs))
  show Module.Flat R A
  infer_instance
private lemma torsionFree_of_ringHom_flat [IsDomain R] (r : R →+* A) (hr : r.Flat)
    (c : R) (s : A) (hc : c ≠ 0) (hcs : r c * s = 0) : s = 0 := by
  let _ : Algebra R A := r.toAlgebra
  let _ : Module.Flat R A := hr
  let _ : Module.IsTorsionFree R A := inferInstance
  have hreg : IsSMulRegular A c := (IsRegular.of_ne_zero hc).isSMulRegular
  have h0 : c • s = c • (0 : A) := by
    rw [smul_zero, Algebra.smul_def]
    exact hcs
  exact hreg h0
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
private lemma flat_appLE_iff (U : X.affineOpens) :
    RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom ↔
      RingHom.Flat ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ (U : X.Opens) le_top).hom := by
  rw [CommRingCat.hom_comp]
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).symm
private lemma flat_iff [IsDedekindDomain R] :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 := by
  constructor
  · intro hf U c s hc hcs
    have h1 : RingHom.Flat (f.appLE ⊤ (U : X.Opens) le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) f hf ⟨⊤, isAffineOpen_top _⟩ U le_top
    rw [flat_appLE_iff] at h1
    exact torsionFree_of_ringHom_flat _ h1 c s hc hcs
  · intro htf
    refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : X.affineOpens ↦ U)
      (iSup_affineOpens_eq_top X) (fun U ↦ ?_)
    rw [flat_appLE_iff]
    exact ringHom_flat_of_torsionFree _ (fun c s hc hcs ↦ htf U c s hc hcs)
/--
[AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 :=
  flat_iff f

-- created on 2026-10-20
