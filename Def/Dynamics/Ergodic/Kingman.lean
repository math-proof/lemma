/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Kingman.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Dynamics.Ergodic.Birkhoff
import Lemma.Set.Ergodic.Birkhoff


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
