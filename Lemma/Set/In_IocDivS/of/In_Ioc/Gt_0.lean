import sympy.sets.sets
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b d : α}
-- given
  (h₀ : d > 0)
  (h₁ : x ∈ Ioc a b) :
-- imply
  x / d ∈ Ioc (a / d) (b / d) := by
-- proof
  let ⟨h_Lt, h_Le⟩ := h₁
  constructor
  ·
    apply LtDivS.of.Lt.Gt_0 h_Lt h₀
  ·
    apply LeDivS.of.Le.Gt_0 h_Le h₀


-- created on 2025-05-04
