/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean -/

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


section

namespace MathlibExt.Dynamics.Ergodic.BirkhoffWanted

open MeasureTheory

/-- Maximal divergence set where some Birkhoff sum exceeds `n * q` for a rational `q > c`. -/
noncomputable def DickSet {α : Type*} [MeasurableSpace α]
    (T : α → α) (g : α → ℝ) (c : ℝ) : Set α :=
  ⋃ (q : ℚ) (_ : c < (q : ℝ)), ⋂ (N : ℕ), ⋃ (n : ℕ) (_ : N ≤ n),
    {x | (n : ℝ) * (q : ℝ) < birkhoffSum T g n x}

end MathlibExt.Dynamics.Ergodic.BirkhoffWanted
end
