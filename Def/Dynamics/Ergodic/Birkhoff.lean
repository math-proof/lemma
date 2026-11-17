/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean -/

module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

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
