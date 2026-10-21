import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[IsArtinianRing_finite_of_isLocalRing_of_finite_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField.lean)
-/
@[path]
private lemma main
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] : Finite C := by
  classical
  let σ : ResidueField C → C := Function.surjInv (IsLocalRing.residue_surjective (R := C))
  have hσ : ∀ a, IsLocalRing.residue C (σ a) = a := Function.surjInv_eq (IsLocalRing.residue_surjective (R := C))
  have aux : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (maximalIdeal C) ^ k • (⊤ : Submodule C M) = ⊥ → Finite M := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ h
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at h
      let _ : Subsingleton M := subsingleton_of_forall_eq 0 fun x => by
        have : x ∈ (⊤ : Submodule C M) := Submodule.mem_top; rw [h] at this; exact (Submodule.mem_bot C).mp this
      infer_instance
    | succ k ih =>
      intro M _ _ _ h
      let N : Submodule C M := (maximalIdeal C) • ⊤
      let _ : IsNoetherian C M := isNoetherian_of_isNoetherianRing_of_finite C M
      let _ : Module.Finite C N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
      have hN : (maximalIdeal C) ^ k • (⊤ : Submodule C N) = ⊥ := by
        apply Submodule.map_injective_of_injective N.injective_subtype
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Submodule.map_bot,
          show (maximalIdeal C) ^ k • N = (maximalIdeal C) ^ (k + 1) • (⊤ : Submodule C M) by
            rw [pow_succ, Submodule.mul_smul]]
        exact h
      have hfinN : Finite N := ih N hN
      obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := C) (M := M)
      have hfinQ : Finite (M ⧸ N) := by
        let f : (S → ResidueField C) → M ⧸ N := fun a => Submodule.Quotient.mk (∑ s : S, σ (a s) • (s : M))
        refine Finite.of_surjective f fun q => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
        have hx : x ∈ Submodule.span C (S : Set M) := by rw [hS]; exact Submodule.mem_top
        obtain ⟨c, -, hc⟩ := (Submodule.mem_span_finset).mp hx
        refine ⟨fun s => IsLocalRing.residue C (c s), ?_⟩
        show Submodule.Quotient.mk (∑ s : S, σ (IsLocalRing.residue C (c s)) • (s : M)) = Submodule.Quotient.mk x
        rw [Submodule.Quotient.eq]
        have : (∑ s : S, σ (IsLocalRing.residue C (c s)) • (s : M)) - x =
            ∑ s : S, (σ (IsLocalRing.residue C (c s)) - c s) • (s : M) := by
          rw [← hc, ← Finset.sum_coe_sort S (fun s => c s • s), ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [sub_smul]
        rw [this]
        refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hσ, sub_self]
      let τ : M ⧸ N → M := Function.surjInv (Submodule.Quotient.mk_surjective N)
      have hτ : ∀ q, Submodule.Quotient.mk (τ q) = q := Function.surjInv_eq (Submodule.Quotient.mk_surjective N)
      let _ := hfinN; haveI := hfinQ
      refine Finite.of_surjective (fun p : N × (M ⧸ N) => (p.1 : M) + τ p.2) fun m => ?_
      have hm : m - τ (Submodule.Quotient.mk m) ∈ N := by
        rw [← Submodule.Quotient.eq, hτ]
      exact ⟨(⟨m - τ (Submodule.Quotient.mk m), hm⟩, Submodule.Quotient.mk m), by simp⟩
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hk
  exact aux k C (by rw [Ideal.smul_eq_mul, Ideal.mul_top, hk, Ideal.zero_eq_bot])

-- created on 2026-10-20
