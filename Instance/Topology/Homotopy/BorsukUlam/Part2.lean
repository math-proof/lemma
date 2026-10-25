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
import Def.Topology.Homotopy.BorsukUlam.Part6


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

instance bu_tkVFintype (n m : ℕ) : Fintype (bu_tkV n m) :=
  Finset.fintypeCoeSort _

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
