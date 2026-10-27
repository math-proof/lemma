import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S] (P : S → Prop)
  (h : ∀ 𝔭 : PrimeSpectrum S, ∃ g : S, g ∉ 𝔭.asIdeal ∧ P g) :
  -- imply
  ∃ (k : ℕ) (g : Fin k → S), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by
  -- proof
  classical
  have htop : Ideal.span {g : S | P g} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg, hPg⟩ := h ⟨𝔪, h𝔪.isPrime⟩
    apply hg (hle (Ideal.subset_span hPg))
  have h1 : (1 : S) ∈ Ideal.span {g : S | P g} := by
    rw [htop]
    trivial
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  obtain ⟨k, e⟩ : ∃ k : ℕ, Nonempty (Fin k ≃ ↥T) := ⟨T.card, ⟨(Finset.equivFin T).symm⟩⟩
  obtain ⟨e⟩ := e
  have hrange : Set.range (fun i : Fin k => ((e i : ↥T) : S)) = (T : Set S) := by
    ext x
    constructor
    ·
      rintro ⟨i, rfl⟩
      apply (e i).2
    ·
      intro hx
      refine ⟨e.symm ⟨x, hx⟩, by simp⟩
  refine ⟨k, fun i => (e i : S), ?_, fun i => hT (e i).2⟩
  rw [Ideal.eq_top_iff_one, hrange]
  apply h1T


-- created on 2026-10-20
