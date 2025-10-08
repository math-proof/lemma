import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Set.In_Ioo.of.Gt.Lt
import Lemma.Algebra.Ne.of.Gt
import Lemma.Set.In_Ico.of.Lt.Ge
import Lemma.Nat.Ge.of.Gt
open Set Algebra Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  Ico a b \ {a} = Ioo a b := by
-- proof
  ext x
  constructor <;>
    intro h
  ·
    let ⟨h₀, h₁⟩ := h
    simp at h₁
    let ⟨h₀, h₂⟩ := h₀
    have := Gt.of.Ge.Ne h₀ h₁
    apply In_Ioo.of.Gt.Lt this h₂
  ·
    let ⟨h₀, h₁⟩ := h
    constructor
    ·
      apply In_Ico.of.Lt.Ge h₁
      apply Ge.of.Gt h₀
    ·
      simp
      apply Ne.of.Gt h₀


-- created on 2025-04-04
