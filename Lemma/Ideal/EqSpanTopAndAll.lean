import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_finset_span_eq_top_of_forall_isMaximal_exists_not_mem.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S] (P : S → Prop)
  (h : ∀ 𝔭 : PrimeSpectrum S, 𝔭.asIdeal.IsMaximal → ∃ g : S, g ∉ 𝔭.asIdeal ∧ P g) :
  -- imply
  ∃ (k : ℕ) (g : Fin k → S), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by
  -- proof
  classical
  have htop : Ideal.span {g : S | P g} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg𝔪, hPg⟩ := h ⟨𝔪, h𝔪.isPrime⟩ h𝔪
    apply hg𝔪 (hle (Ideal.subset_span hPg))
  have h1 : (1 : S) ∈ Ideal.span {g : S | P g} := by
    rw [htop]
    apply Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i : ↥T) : S)) = (↑T : Set S) := by
    ext x
    constructor
    ·
      rintro ⟨i, rfl⟩
      apply (T.equivFin.symm i).2
    ·
      intro hx
      refine ⟨T.equivFin ⟨x, hx⟩, by simp only [Equiv.symm_apply_apply]⟩
  refine ⟨T.card, fun i => ((T.equivFin.symm i : ↥T) : S), ?_, fun i => hTsub (T.equivFin.symm i).2⟩
  rw [hrange, Ideal.eq_top_iff_one]
  apply h1T


-- created on 2026-10-20
