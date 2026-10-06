import Mathlib
import sympy.Basic


/--
[Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem.lean)
-/
@[main]
private lemma main
  [CommRing B]
-- given
  (P : B → Prop)
  (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ s : B, s ∉ 𝔪 ∧ P s) :
-- imply
  ∃ (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n, P (g i) := by
-- proof
  classical

  have htop : Ideal.span {s : B | P s} = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hs, hPs⟩ := h 𝔪 h𝔪
    exact hs (hle (Ideal.subset_span hPs))

  have h1 : (1 : B) ∈ Ideal.span {s : B | P s} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1

  let e := T.equivFin
  refine ⟨T.card, fun i => (e.symm i).1, ?_, fun i => hT (e.symm i).2⟩
  rw [Ideal.eq_top_iff_one]
  refine Submodule.span_mono ?_ h1T
  intro s hs
  exact ⟨e ⟨s, hs⟩, by simp⟩


-- created on 2026-10-05
