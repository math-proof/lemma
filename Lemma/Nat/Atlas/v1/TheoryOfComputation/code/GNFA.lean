import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfComputation.code.GNFA
open List Set Sipser Sipser.GNFA


namespace Sipser.GNFA

/--
[AcceptPath.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean)
-/
@[path]
lemma AcceptPath.trans
  [Fintype Q]
  {G : GNFA Q σ}
-- given
  (h₁ : AcceptPath G q₁ q₂ w₁)
  (h₂ : AcceptPath G q₂ q₃ w₂) :
-- imply
  AcceptPath G q₁ q₃ (w₁ ++ w₂) := by
-- proof
  induction h₂ generalizing q₁ w₁ with
  | nil => simpa using h₁
  | cons _ hmatch ih =>
    rw [← List.append_assoc]
    exact AcceptPath.cons (ih h₁) hmatch

end Sipser.GNFA

namespace Sipser.GNFA

/--
[accepts_of_single_transition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean)
-/
@[path]
lemma accepts_of_single_transition
  [Fintype Q]
  {G : GNFA Q σ}
  {w : List σ}
-- given
  (h : w ∈ (G.δ G.start G.accept).matches') :
-- imply
  G.accepts w := by
-- proof
  show AcceptPath G G.start G.accept w
  have : AcceptPath G G.start G.accept ([] ++ w) :=
    AcceptPath.cons (AcceptPath.nil G.start) h
  simpa using this

end Sipser.GNFA

/--
[mem_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean)
-/
@[path]
private lemma mem_language_eq
  [Fintype Q]
  {G : GNFA Q σ}
  {w : List σ} :
-- imply
  w ∈ G.language ↔ G.accepts w := by
-- proof
  apply Sipser.GNFA.mem_language


-- created on 2026-10-23
-- updated on 2026-10-28
