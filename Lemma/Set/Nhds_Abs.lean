import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.vol_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d} :
-- imply
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))))
  (nhds |B|ᵥ) :=
-- proof
  Box.vol_eq B


-- created on 2026-10-22
