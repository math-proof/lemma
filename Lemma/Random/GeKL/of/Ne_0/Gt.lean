import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import sympy.Basic
open MeasureTheory InformationTheory


@[path]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {μ ν : Measure α}
  {g : α → β}
-- given
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (h₀ : Measurable g) :
-- imply
  klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν :=
-- proof
  klDiv_map_le μ ν h₀


-- created on 2021-08-02
-- updated on 2026-10-17
