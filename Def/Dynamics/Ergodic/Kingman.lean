/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Kingman.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.StrongLaw
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Separation.CompletelyRegular
public import Def.Dynamics.Ergodic.Birkhoff
public import Theorem.Set.Ergodic.Birkhoff

@[expose] public section

section

open MeasureTheory Filter Topology

namespace MathlibExt.Dynamics.Ergodic.KingmanWanted

/-- N8: liminf rate function (ENNReal to avoid boundedness side conditions). -/
noncomputable def kingmanLiminf {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (x : α) : ENNReal :=
  Filter.liminf (fun n : ℕ => ENNReal.ofReal (f n x / (n : ℝ))) atTop

/-- N10/N11: bad set where averages exceed `ℓ + ε` on all of `Icc 1 N`. -/
def kingmanBadSet {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) : Set α :=
  {y | ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y}

end MathlibExt.Dynamics.Ergodic.KingmanWanted
end
