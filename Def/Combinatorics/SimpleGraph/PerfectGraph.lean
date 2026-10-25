/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PerfectGraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
open scoped Matrix BigOperators


section

namespace MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted

/-!
# Perfect graphs
-/

/-- Finite graph where every induced subgraph has `chromaticNumber = cliqueNum`. -/
def IsPerfect {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (s : Set V), (G.induce s).chromaticNumber = ((G.induce s).cliqueNum : ℕ∞)

/-- Gasparian's condition (P): every finset satisfies `card s ≤ alpha * omega`. -/
def PerfIneq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.card ≤ (G.induce (↑s : Set V)).indepNum * (G.induce (↑s : Set V)).cliqueNum

/-- Map a finset of the subtype back to `V`. -/
noncomputable def subMap {V : Type*} (u : Finset V)
    (s : Finset (↥(↑u : Set V))) : Finset V :=
  open scoped Classical in s.map ⟨Subtype.val, Subtype.val_injective⟩

end MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted
end
