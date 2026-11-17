/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PerfectGraph.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith

@[expose] public section

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
