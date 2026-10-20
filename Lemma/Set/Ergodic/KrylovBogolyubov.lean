import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Ergodic.KrylovBogolyubov
open MeasureTheory
open MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted


/--
[krylov_bogolyubov](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/KrylovBogolyubov.lean)
-/
@[path]
private lemma krylov_bogolyubov_eq
  [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
  {T : X → X}
-- given
  (hT : Continuous T) :
-- imply
  ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Measure.map T μ = μ := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted.krylov_bogolyubov hT


-- created on 2026-10-20
