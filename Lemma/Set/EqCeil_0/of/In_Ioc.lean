import sympy.sets.sets
import Lemma.Algebra.EqCeil.is.Lt.Le
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
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
