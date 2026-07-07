import Lemma.Hyperreal.IsSt_St.of.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Bool.NotAnd.is.OrNotS
open Bool Hyperreal


@[main, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  stdPart x ≠ 0 ↔ ¬x → ∞ ∧ ¬x → 0  := by
-- proof
  constructor <;>
    intro h
  .
    by_contra h'
    have h' := OrNotS.of.NotAnd h'
    obtain h' | h' := h'
    .
      simp at h'
      have := EqSt_0.of.Infinite h'
      contradiction
    .
      simp at h'
      have := EqSt_0.of.Infinitesimal h'
      contradiction
  .
    let ⟨h₀, h₁⟩ := h
    intro h
    apply h₁
    have h_isSt := IsSt_St.of.NotInfinite h₀
    simpa [h] using h_isSt


-- created on 2025-12-18
