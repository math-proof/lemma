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
public import Theorem.Topology.Homotopy.BorsukUlam.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

noncomputable def bu_tkG (n m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    SimpleGraph (bu_tkV n m) where
  Adj σ τ := bu_tkAdj m L σ.val τ.val
  symm := ⟨fun _ _ h => bu_tkAdj_symm h⟩
  loopless := ⟨fun _ h => bu_tkAdj_irrefl hm h⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
