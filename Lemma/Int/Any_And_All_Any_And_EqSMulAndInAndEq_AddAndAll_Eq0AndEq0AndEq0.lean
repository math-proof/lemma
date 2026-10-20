import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IharaLemma_exists_isCompl_orthogonal_of_isIdempotentElem_of_selfAdjoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_exists_isCompl_orthogonal_of_isIdempotentElem_of_selfAdjoint.lean)
-/
@[path]
private lemma main
  {𝒪 : Type} [CommRing 𝒪]
  {B' : Type} [CommRing B'] [Algebra 𝒪 B']
  {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
  (U : Submodule B' V')
  (Bf : ↥(U.restrictScalars 𝒪) →ₗ[𝒪] ↥(U.restrictScalars 𝒪) →ₗ[𝒪] 𝒪)
  (hadj : ∀ (t : B') (x y : ↥(U.restrictScalars 𝒪)), Bf ⟨t • (x : V'), U.smul_mem t x.2⟩ y = Bf x ⟨t • (y : V'), U.smul_mem t y.2⟩)
  (e : B') (he : IsIdempotentElem e) :
  -- imply
  ∃ C : Submodule B' V', C ≤ U ∧ (∀ u ∈ U, ∃ u₁ u₂ : V', u₁ ∈ U ∧ e • u₁ = u₁ ∧ u₂ ∈ C ∧ u = u₁ + u₂) ∧ (∀ v : V', v ∈ U → e • v = v → v ∈ C → v = 0) ∧ (∀ (x y : ↥(U.restrictScalars 𝒪)), e • (x : V') = x → (y : V') ∈ C → Bf x y = 0 ∧ Bf y x = 0) := by
  -- proof
  refine ⟨U ⊓ LinearMap.ker (e • (LinearMap.id : V' →ₗ[B'] V')), inf_le_left, ?_, ?_, ?_⟩
  ·
    intro u hu
    refine ⟨e • u, u - e • u, U.smul_mem e hu, ?_, ?_, ?_⟩
    · rw [smul_smul, he.eq]
    ·
      refine ⟨U.sub_mem hu (U.smul_mem e hu), ?_⟩
      change (e • (LinearMap.id (R := B') (u - e • u)) : V') = 0
      rw [LinearMap.id_apply, smul_sub, smul_smul, he.eq, sub_self]
    · rw [add_sub_cancel]
  ·
    rintro v - hev ⟨-, hker⟩
    have hzero : e • v = 0 := hker
    rw [← hev, hzero]
  ·
    rintro x y hx ⟨-, hker⟩
    have hey : e • (y : V') = 0 := hker
    have hx' : (⟨e • (x : V'), U.smul_mem e x.2⟩ : ↥(U.restrictScalars 𝒪)) = x := Subtype.ext hx
    have hy' : (⟨e • (y : V'), U.smul_mem e y.2⟩ : ↥(U.restrictScalars 𝒪)) = 0 := Subtype.ext hey
    constructor
    ·
      have h := hadj e x y
      rw [hx', hy', map_zero] at h
      apply h
    ·
      have h := hadj e y x
      rw [hy', hx', LinearMap.map_zero, LinearMap.zero_apply] at h
      apply h.symm


-- created on 2026-10-20
