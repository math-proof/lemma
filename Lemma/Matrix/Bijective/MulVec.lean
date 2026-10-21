import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card.lean)
-/
@[path]
private lemma main
  {K : Type} [Field K]
  {D : Type} [Ring D] [Algebra K D]
  {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
  (ι : AlgHom K D (Matrix N N K))
  (e₀ : N → K)
  -- given
  (hdiv : ∀ d : D, d ≠ 0 → IsUnit d)
  (hdim : Module.finrank K D = Fintype.card N)
  (he₀ : e₀ ≠ 0) :
  -- imply
  Function.Bijective (fun d : D => (ι d).mulVec e₀) ∧ ∀ T : Matrix N N K, (∀ d : D, T * ι d = ι d * T) → ∃ ξ : D, ∀ d : D, T.mulVec ((ι d).mulVec e₀) = (ι (d * ξ)).mulVec e₀ := by
  -- proof
  classical
  let f : D →ₗ[K] (N → K) := {
    toFun := fun d => (ι d).mulVec e₀
    map_add' := fun x y => by
      simp only [map_add, Matrix.add_mulVec]
    map_smul' := fun c x => by
      simp only [map_smul, Matrix.smul_mulVec, RingHom.id_apply] }
  have hf : ∀ d : D, f d = (ι d).mulVec e₀ := fun _ => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    by_contra hne
    obtain ⟨u, rfl⟩ := hdiv d hne
    have h0 : (ι ((↑u⁻¹ : D) * (↑u : D))).mulVec e₀ = 0 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← hf (↑u : D), hd, Matrix.mulVec_zero]
    rw [Units.inv_mul, map_one, Matrix.one_mulVec] at h0
    apply he₀ h0
  have hpos : 0 < Module.finrank K D := by
    rw [hdim]
    apply Fintype.card_pos
  let _ : Module.Finite K D := Module.finite_of_finrank_pos hpos
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hdim, Module.finrank_fintype_fun_eq_card])).mp hinj
  refine ⟨⟨hinj, hsurj⟩, ?_⟩
  intro T hT
  obtain ⟨ξ, hξ⟩ := hsurj (T.mulVec e₀)
  refine ⟨ξ, fun d => ?_⟩
  rw [Matrix.mulVec_mulVec, hT d, ← Matrix.mulVec_mulVec, map_mul, ← Matrix.mulVec_mulVec, ← hf ξ, hξ]


-- created on 2026-10-20
