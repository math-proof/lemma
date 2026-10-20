import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.JentzschPowerSeries
open Filter Topology
open scoped ENNReal NNReal
open MathlibExt.Analysis.Complex.JentzschPowerSeriesWanted


/--
[jentzsch_zeros_of_power_series_sections](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/JentzschPowerSeries.lean)
-/
@[path]
private lemma jentzsch_zeros_of_power_series_sections_eq
-- given
  (a : Nat -> Complex)
  (hradius : (FormalMultilinearSeries.ofScalars Complex a).radius = 1) :
-- imply
  ∀ (z : Complex), ‖z‖ = 1 → ∀ (epsilon : Real), 0 < epsilon → ∀ (N : Nat),
    ∃ (n : Nat), N ≤ n ∧ ∃ (w : Complex),
    (PowerSeries.trunc (n + 1) (PowerSeries.mk a)).IsRoot w ∧ dist w z < epsilon := by
-- proof
  apply MathlibExt.Analysis.Complex.JentzschPowerSeriesWanted.jentzsch_zeros_of_power_series_sections a hradius


-- created on 2026-10-20
