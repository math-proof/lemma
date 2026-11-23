/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Def.Topology.Homotopy.BorsukUlam.Part3
@[expose] public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Cofacet classification -/

/-- Decidability of the chain predicate (for the counter filters). -/
noncomputable instance bu_tkChain_dec {n : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkChain σ) :=
  Classical.dec _

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
