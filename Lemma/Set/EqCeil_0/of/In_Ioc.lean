import sympy.sets.sets
import Lemma.Rat.EqCeil.is.Lt.Le
open Rat


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


-- created on 2025-03-02
-- updated on 2025-08-02
