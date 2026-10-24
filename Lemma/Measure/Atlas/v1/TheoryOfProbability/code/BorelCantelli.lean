import Mathlib
import sympy.Basic
open MeasureTheory Filter Set
open scoped ENNReal Topology


/--
[first_borel_cantelli](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BorelCantelli.lean)
-/
@[path]
lemma first_borel_cantelli
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  {A : ℕ → Set Ω}
-- given
  (hA : ∑' n, μ (A n) ≠ ⊤) :
-- imply
  μ (limsup A atTop) = 0 :=
-- proof
  measure_limsup_atTop_eq_zero hA


-- created on 2026-10-23
