import Mathlib
import sympy.Basic


/--
[Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field.lean)
-/

private lemma  faithfullyFlat_of_exists_ringHom_field' {B : Type u} {S : Type v} [CommRing B]
    [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨K, _, ψ, hker⟩ := h m hm
  have h1 : (1 : S) ∈ Ideal.map (algebraMap B S) m := by
    have hle : I • (⊤ : Submodule B S) ≤ m • ⊤ := Submodule.smul_mono_left hIm
    rw [hI, top_le_iff, Ideal.smul_top_eq_map] at hle
    have h := (hle ▸ Submodule.mem_top : (1 : S) ∈ (Ideal.map (algebraMap B S) m).restrictScalars B)
    exact h
  have h2 : ψ 1 ∈ Ideal.map ψ (Ideal.map (algebraMap B S) m) := Ideal.mem_map_of_mem ψ h1
  rw [Ideal.map_map, map_one] at h2
  have h3 : Ideal.map (ψ.comp (algebraMap B S)) m = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]; exact hker
  rw [h3] at h2
  exact one_ne_zero ((Submodule.mem_bot K).mp h2)
@[main]
private lemma main
  {B : Type u} [CommRing B]
  {S : Type v} [CommRing S] [Algebra B S] [Module.Flat B S]
-- given
  (h : ∀ m : Ideal B, m.IsMaximal → ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
-- imply
  Module.FaithfullyFlat B S :=
-- proof
  faithfullyFlat_of_exists_ringHom_field' h


-- created on 2026-10-05
