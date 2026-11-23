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
public import Def.Topology.Homotopy.BorsukUlam.Part4

public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- The sign set of a chain is the sign set of any top element. -/
theorem bu_tkS_of_top {n : ℕ} {τ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    (hτ : bu_tkChain τ) (ht : t ∈ τ) (hall : ∀ z ∈ τ, bu_tkLe z t) :
    bu_tkS τ = bu_tkSgn t := by
  obtain ⟨_, _, t', ht', _, htop', hSeq'⟩ := bu_chain_bot_top hτ
  have h1 : bu_tkSgn t' ⊆ bu_tkSgn t := bu_tkSgn_mono (hall t' ht')
  have h2 : bu_tkSgn t ⊆ bu_tkSgn t' := bu_tkSgn_mono (htop' t ht)
  rw [hSeq', le_antisymm h1 h2]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
