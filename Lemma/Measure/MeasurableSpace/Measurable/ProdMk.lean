import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- Pairing of measurable maps is measurable. -/
@[main]
private lemma main
  {α β γ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β} {g : α → γ}
-- given
  (hf : Measurable f)
  (hg : Measurable g) :
-- imply
  Measurable fun a : α => (f a, g a) :=
-- proof
  hf.prodMk hg


-- created on 2026-09-23
