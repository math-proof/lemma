import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Geometry.BesicovitchKakeya
open MeasureTheory
open scoped MeasureTheory ENNReal
open scoped MeasureTheory
open MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted


/--
[besicovitch_kakeya_compact_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BesicovitchKakeya.lean)
-/
@[path]
private lemma besicovitch_kakeya_compact_measure_zero_eq
  [MeasurableSpace (EuclideanSpace ℝ (Fin 2))] [BorelSpace (EuclideanSpace ℝ (Fin 2))] :
-- imply
  ∃ (K : Set (EuclideanSpace ℝ (Fin 2))),
    MeasurableSet K ∧ IsCompact K ∧
    ((volume : Measure (EuclideanSpace ℝ (Fin 2))) K = 0) ∧
    ∀ (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
    ∃ (a : EuclideanSpace ℝ (Fin 2)), ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • v ∈ K := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted.besicovitch_kakeya_compact_measure_zero


-- created on 2026-10-20
