import Mathlib
import Initialize.Tactic.Attr.Basic


namespace LinearMap

/--
[exact_and_surjective_iff_forall_lcomp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/LeftExact.lean)
-/
@[path]
lemma exact_and_surjective_iff_forall_lcomp
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type w} [AddCommGroup P] [Module R P]
  {φ : M →ₗ[R] N}
  {ψ : N →ₗ[R] P} :
-- imply
  (Function.Exact φ ψ ∧ Function.Surjective ψ) ↔
      ∀ (D : Type w) [AddCommGroup D] [Module R D],
        Function.Injective (lcomp R D ψ) ∧
        Function.Exact (lcomp R D ψ) (lcomp R D φ) := by
-- proof
  constructor
  · rintro ⟨hex, hsurj⟩ D _ _
    exact ⟨lcomp_injective_of_surjective ψ hsurj,
      exact_lcomp_of_exact_of_surjective (N := D) hex hsurj⟩
  · intro h
    have hker : ker ψ ≤ range φ := by
      intro x hx
      have hexD := (h (N ⧸ range φ)).2
      have hq : (lcomp R (N ⧸ range φ) φ) (range φ).mkQ = 0 :=
        range_mkQ_comp φ
      obtain ⟨θ, hθ⟩ := (hexD (range φ).mkQ).mp hq
      have hqx : (range φ).mkQ x = 0 := by
        have e : θ (ψ x) = (range φ).mkQ x := DFunLike.congr_fun hθ x
        rw [← e, mem_ker.mp hx, map_zero]
      have hmem : x ∈ ker (range φ).mkQ := mem_ker.mpr hqx
      rwa [Submodule.ker_mkQ] at hmem
    have hcomp : ψ ∘ₗ φ = 0 := by
      have hexP := (h P).2
      have hmem : ψ ∈ Set.range (lcomp R P ψ) := ⟨id, by ext x; rfl⟩
      exact (hexP ψ).mpr hmem
    have hsurj : Function.Surjective ψ := by
      rw [← range_eq_top]
      apply range_eq_top_of_cancel
      intro u v huv
      have hinj := (h (P ⧸ range ψ)).1
      exact hinj huv
    exact ⟨exact_iff.mpr (le_antisymm hker (range_le_ker_iff.mpr hcomp)), hsurj⟩

end LinearMap


-- created on 2026-10-20
-- updated on 2026-10-26
