import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {Φ : ContinuousSemiflow (PhasePoint d m S)}
  {K : Set (PhasePoint d m S)}
  {B : Set (PhasePoint d m S)}
-- given
  (h₀ : Φ.Absorbs data K)
  (h₁ : PhaseBounded data B) :
-- imply
  Φ.Attracts B K := by
-- proof
  intro U _ hKU
  obtain ⟨T, hT, h⟩ := h₀ B h₁
  exact ⟨T, hT, fun t ht x hx => hKU (h t ht x hx)⟩


-- created on 2026-09-26
