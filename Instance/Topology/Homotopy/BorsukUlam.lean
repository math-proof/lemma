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
import Def.Topology.Homotopy.BorsukUlam.Part3


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Cofacet classification -/

/-- Decidability of the chain predicate (for the counter filters). -/
noncomputable instance bu_tkChain_dec {n : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkChain σ) :=
  Classical.dec _

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
