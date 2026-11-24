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
public import Def.Topology.Homotopy.BorsukUlam.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

noncomputable instance bu_tkGDec {n m : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    DecidableRel (bu_tkG n m L hm).Adj :=
  Classical.decRel _

/-! ## Degree count -/

/-- Decidability of the boundary predicate (for the antipodal counter). -/
noncomputable instance bu_tkBdry_dec {n m : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkBdry m σ) :=
  Classical.dec _

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
