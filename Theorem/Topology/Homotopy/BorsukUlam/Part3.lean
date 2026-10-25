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
import Def.Topology.Homotopy.BorsukUlam.Part4


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
