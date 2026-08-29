import sympy.sets.sets
import Lemma.Int.EqCeil.is.Lt.Le
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ioc (-1) 0) :
-- imply
  ⌈x⌉ = 0 := by
-- proof
  let ⟨h₀, h₁⟩ := h
  apply EqCeil.of.Lt.Le <;>
  ·
    norm_num
    assumption


-- created on 2018-10-22
-- updated on 2025-08-02
