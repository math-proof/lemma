/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorem.Topology.Homotopy.BorsukUlam.Part5


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

noncomputable def bu_tkG (n m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    SimpleGraph (bu_tkV n m) where
  Adj σ τ := bu_tkAdj m L σ.val τ.val
  symm := ⟨fun _ _ h => bu_tkAdj_symm h⟩
  loopless := ⟨fun _ h => bu_tkAdj_irrefl hm h⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
