import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (σ : Y ⟶ X) [IsClosedImmersion σ] (y : Y)
  (U : X.affineOpens) (hx : σ.base y ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) (σ.base y) hx).hom (σ.ker.ideal U) = RingHom.ker (σ.stalkMap y).hom := by
  classical
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have hV : IsAffineOpen ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)) := hU.preimage σ
  have hy : y ∈ (TopologicalSpace.Opens.map σ.base).obj (U : X.Opens) := hx
  let algX := X.presheaf.algebra_section_stalk (⟨σ.base y, hx⟩ : (U : X.Opens))
  let locX := hU.isLocalization_stalk ⟨σ.base y, hx⟩
  let algY := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : (TopologicalSpace.Opens.map σ.base).obj (U : X.Opens))
  let locY := hV.isLocalization_stalk ⟨y, hy⟩
  set φ := (σ.app (U : X.Opens)).hom with hφ
  have hφsurj : Function.Surjective φ := σ.app_surjective U hU
  have hker : σ.ker.ideal U = RingHom.ker φ := Scheme.Hom.ker_apply σ U
  have hcomm : ∀ a : (X.presheaf.obj (Opposite.op (U : X.Opens))), (σ.stalkMap y).hom (algebraMap (X.presheaf.obj (Opposite.op (U : X.Opens))) (X.presheaf.stalk (σ.base y)) a) =
      algebraMap (Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)))) (Y.presheaf.stalk y) (φ a) := by
    intro a
    apply Scheme.Hom.germ_stalkMap_apply σ (U : X.Opens) y hy a
  have happ : σ.appLE (U : X.Opens) ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)) le_rfl = σ.app (U : X.Opens) :=
    (Scheme.Hom.app_eq_appLE σ).symm
  have hcomap : (hV.primeIdealOf ⟨y, hy⟩).comap φ = hU.primeIdealOf ⟨σ.base y, hx⟩ := by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := σ) (U : X.Opens) hU ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)) hV le_rfl hy
    rwa [happ] at this
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [hker] at ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (σ.stalkMap y).hom (algebraMap (X.presheaf.obj (Opposite.op (U : X.Opens))) (X.presheaf.stalk (σ.base y)) a) = 0
    rw [hcomm, RingHom.mem_ker.mp ha, map_zero]
  ·
    intro s hs
    rw [RingHom.mem_ker] at hs
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨σ.base y, hx⟩).asIdeal.primeCompl s
    simp only at hat
    subst hat
    have h1 : (σ.stalkMap y).hom (IsLocalization.mk' (X.presheaf.stalk (σ.base y)) a t) *
        (σ.stalkMap y).hom (algebraMap (X.presheaf.obj (Opposite.op (U : X.Opens))) (X.presheaf.stalk (σ.base y)) (t : (X.presheaf.obj (Opposite.op (U : X.Opens))))) =
        algebraMap (Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)))) (Y.presheaf.stalk y) (φ a) := by
      rw [← map_mul, IsLocalization.mk'_spec, hcomm]
    rw [hs, zero_mul] at h1
    have h2 : algebraMap (Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map σ.base).obj (U : X.Opens)))) (Y.presheaf.stalk y) (φ a) = 0 := h1.symm
    rw [IsLocalization.map_eq_zero_iff (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl] at h2
    obtain ⟨⟨u, hu⟩, hua⟩ := h2
    obtain ⟨r, rfl⟩ := hφsurj u
    have hr : r ∈ (hU.primeIdealOf ⟨σ.base y, hx⟩).asIdeal.primeCompl := by
      intro hr'
      apply hu
      rwa [← hcomap] at hr'
    have hra : a * r ∈ σ.ker.ideal U := by
      rwa [hker, RingHom.mem_ker, map_mul, mul_comm]
    rw [← IsLocalization.mk'_cancel a t ⟨r, hr⟩, IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hra)


-- created on 2026-10-20
