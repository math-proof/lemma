import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open Box


/--
[Box.sum_vol_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {T: Finset (Box d)}
-- given
  (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet) :
-- imply
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))))
  (nhds (∑ B ∈ T, |B|ᵥ)) :=
-- proof
  Box.sum_vol_eq hT


-- created on 2026-10-22
