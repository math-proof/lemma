import sympy.sets.sets
import Lemma.Algebra.LtDivS.of.Lt.Gt_0
import Lemma.Algebra.LeDivS.of.Le.Gt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
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
