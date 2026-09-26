import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic


/-- `Prod.map` of measurable maps is measurable. -/
@[main]
private lemma main
  {α β γ δ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {f : α → β} {g : γ → δ}
-- given
  (hf : Measurable f)
  (hg : Measurable g) :
-- imply
  Measurable (Prod.map f g) :=
-- proof
  hf.prodMap hg


-- created on 2026-09-23
