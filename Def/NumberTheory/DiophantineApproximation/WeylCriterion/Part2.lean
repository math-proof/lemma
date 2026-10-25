/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Weyl's equidistribution criterion: a real sequence is equidistributed modulo 1
if and only if every nontrivial Fourier mean vanishes.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Theorem.NumberTheory.DiophantineApproximation.WeylCriterion
open scoped BigOperators
open Filter Topology


namespace MetaMathlibExt

/-- The bump transferred to the circle as a bundled continuous map. -/
noncomputable def wcF (a b δ : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hδ : 0 < δ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco 1 0 (fun t => ((wcPhi a b δ t : ℝ) : ℂ)), by
    apply AddCircle.liftIco_zero_continuous
    · change ((wcPhi a b δ 0 : ℝ) : ℂ) = ((wcPhi a b δ 1 : ℝ) : ℂ)
      rw [wcPhi_eq_zero_of_le a b δ 0 hδ ha0,
        wcPhi_eq_zero_of_ge a b δ 1 hδ hb1]
    · exact (Complex.continuous_ofReal.comp (wcPhi_cont a b δ)).continuousOn⟩

end MetaMathlibExt
