import Mathlib.Data.Vector.MapLemmas
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (l : List.Vector α n)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) :=
-- proof
  List.Vector.map_map l g f


-- created on 2025-09-24
