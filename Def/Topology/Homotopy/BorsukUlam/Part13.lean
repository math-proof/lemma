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
import Theorem.Topology.Homotopy.BorsukUlam.Part9


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Argmax labelling -/

/-- Argmax index of `a : Fin n → ℝ` (any maximizer). -/
noncomputable def buIdx {n : ℕ} [Nonempty (Fin n)] (a : Fin n → ℝ) : Fin n :=
  Classical.choose (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)

/-- Argmax of absolute values. -/
noncomputable def buI {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Fin n :=
  buIdx (fun i => |v i|)

/-- The label: sign and argmax index. -/
noncomputable def buLab {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Bool × Fin n :=
  (decide (0 < v (buI v)), buI v)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
