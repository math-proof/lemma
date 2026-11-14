import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box
@[path]
private lemma main
  {d:ℕ}
  {x : EuclideanSpace' d}
-- given
  (hd : 0 < d) :
-- imply
  |⟨fun i => BoundedInterval.Icc (x i) (x i)⟩|ᵥ = 0 :=
-- proof
  Box.volume_singleton hd x


-- created on 2026-10-22
