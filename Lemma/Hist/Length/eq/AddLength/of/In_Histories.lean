import sympy.stats.mdp_history
import sympy.Basic


@[main]
private lemma main
  {S : Type*} {A : Type*} [Fintype S] [Fintype A]
  {h h' : Hist S A}
  {t : ℕ}
-- given
  (h₀ : h' ∈ h.histories t) :
-- imply
  h'.length = h.length + t := by
-- proof
  induction t generalizing h' with
  | zero =>
    rw [Hist.histories, Finset.mem_singleton] at h₀
    rw [h₀, add_zero]
  | succ t ih =>
    rw [Hist.histories, Finset.mem_map] at h₀
    obtain ⟨⟨h'', a, s⟩, hm, rfl⟩ := h₀
    rw [Hist.follEmbedding_apply, Hist.length, ih (Finset.mem_product.mp hm).1, add_assoc]


-- created on 2026-09-26
