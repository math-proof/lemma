import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Initialize.Tactic.Attr.Basic
open MeasureTheory InformationTheory


@[path]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {μ ν : Measure (α × β)}
-- given
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
-- imply
  klDiv (μ.map Prod.fst) (ν.map Prod.fst) ≤ klDiv μ ν :=
-- proof
  klDiv_map_le μ ν measurable_fst


-- created on 2023-03-25
-- updated on 2026-10-26
