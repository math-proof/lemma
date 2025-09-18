import Lemma.Algebra.Eq.of.EqValS
import Mathlib.Data.Vector.MapLemmas
open Algebra


@[main]
private lemma main
-- given
  (l : List α)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) :=
-- proof
  List.map_map g f l


@[main]
private lemma vector
-- given
  (l : List.Vector α n)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) :=
-- proof
  List.Vector.map_map l g f


-- created on 2024-07-01
