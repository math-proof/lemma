import sympy.stats.mdp_history
import sympy.Basic


@[main]
private lemma main
  {S : Type*} {A : Type*} [Fintype S] [Fintype A]
  {h : Hist S A}
  {t : ℕ} :
-- imply
  h ∈ Hist.historiesHorizon S A t ↔ h.length = t := by
-- proof
  induction t generalizing h with
  | zero =>
    cases h with
    | init s =>
      simp [Hist.historiesHorizon, Hist.length]
    | foll _ _ _ =>
      simp [Hist.historiesHorizon, Hist.length]
  | succ t ih =>
    cases h with
    | init s =>
      simp [Hist.historiesHorizon, Hist.length]
    | foll h a s =>
      simp [Hist.historiesHorizon, Hist.length, ih]


-- created on 2026-09-26
