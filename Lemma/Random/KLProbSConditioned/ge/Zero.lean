import Mathlib.InformationTheory.KullbackLeibler.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory InformationTheory


@[path]
private lemma main
  [MeasurableSpace α]
  (μ ν : Measure α) :
-- imply
  0 ≤ klDiv μ ν :=
-- proof
  bot_le (a := klDiv μ ν)


-- created on 2021-07-19
-- updated on 2026-10-26
