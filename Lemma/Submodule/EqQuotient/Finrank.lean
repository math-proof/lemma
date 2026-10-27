import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma smul_top_le_comap [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (u : M →ₗ[R] N) : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R N).comap u := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  apply Submodule.smul_mono le_rfl le_top
private lemma mk_smul_eq_mk [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) {r : R} (hr : r - 1 ∈ I) (x : M) : Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) (r • x) = Submodule.Quotient.mk x := by
  rw [Submodule.Quotient.eq]
  have : r • x - x = (r - 1) • x := by rw [sub_smul, one_smul]
  rw [this]
  apply Submodule.smul_mem_smul hr Submodule.mem_top
private lemma exists_linearEquiv [CommRing R] (𝔪 : Ideal R) [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L] [AddCommGroup C] [Module R C] (f : Y →ₗ[R] L) (g : L →ₗ[R] C) (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g) [Module.Finite R C] (hC : (𝔪 • ⊤ : Submodule R C) = ⊤) : ∃ e : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) ≃ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)), ∀ y : Y, e (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y) := by
  obtain ⟨r, hr1, hrC⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule R C) Module.Finite.fg_top (by rw [hC])
  have hrange : ∀ l : L, r • l ∈ LinearMap.range f := by
    intro l
    rw [hfg, LinearMap.mem_ker, map_smul]
    apply hrC _ Submodule.mem_top
  let e := LinearEquiv.ofInjective f hf
  let h : L →ₗ[R] Y :=
    e.symm.toLinearMap.comp (LinearMap.codRestrict (LinearMap.range f) (r • LinearMap.id) (fun l => hrange l))
  have hfh : ∀ l : L, f (h l) = r • l := by
    intro l
    show f (e.symm ⟨r • l, hrange l⟩) = r • l
    have := LinearEquiv.ofInjective_apply f (h := hf) (e.symm ⟨r • l, hrange l⟩)
    rw [LinearEquiv.apply_symm_apply] at this
    apply this.symm
  have hhf : ∀ y : Y, h (f y) = r • y := by
    intro y
    apply hf
    rw [hfh, map_smul]
  let φ : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) →ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)) :=
    Submodule.mapQ _ _ f (smul_top_le_comap 𝔪 f)
  let ψ : (L ⧸ (𝔪 • ⊤ : Submodule R L)) →ₗ[R] (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) :=
    Submodule.mapQ _ _ h (smul_top_le_comap 𝔪 h)
  have h1 : ψ.comp φ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext y
    show ψ (φ (Submodule.Quotient.mk y)) = Submodule.Quotient.mk y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, hhf, mk_smul_eq_mk 𝔪 hr1]
  have h2 : φ.comp ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext l
    show φ (ψ (Submodule.Quotient.mk l)) = Submodule.Quotient.mk l
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, hfh, mk_smul_eq_mk 𝔪 hr1]
  refine ⟨LinearEquiv.ofLinearMap φ ψ h2 h1, fun y => rfl⟩
/--
[LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top.lean)
-/
@[path]
private lemma main
  [CommRing R]
  (𝔪 : Ideal R)
  [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L]
  (f : Y →ₗ[R] L) (hf : Function.Injective f)
  [Module.Finite R (L ⧸ LinearMap.range f)]
  (hC : (𝔪 • ⊤ : Submodule R (L ⧸ LinearMap.range f)) = ⊤) :
  -- imply
  (∃ e : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) ≃ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)), ∀ y : Y, e (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)) ∧ Module.finrank (R ⧸ 𝔪) (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) = Module.finrank (R ⧸ 𝔪) (L ⧸ (𝔪 • ⊤ : Submodule R L)) := by
  -- proof
  obtain ⟨e, he⟩ := exists_linearEquiv 𝔪 f (LinearMap.range f).mkQ hf (Submodule.ker_mkQ _).symm hC
  exact ⟨⟨e, he⟩, (e.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := 𝔪))).finrank_eq⟩


-- created on 2026-10-20
