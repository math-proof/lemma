/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dichromatic.lean -/

/-
# Dichromatic number

Orientation and dichromatic-colouring infrastructure for simple graphs.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.Basic


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An orientation of `G`: a choice of exactly one direction for each edge. -/
def IsOrientation (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧
  ∀ u v, G.Adj u v → (D u v ∧ ¬ D v u) ∨ (D v u ∧ ¬ D u v)

/-- A closed directed walk of positive length in the digraph `D`. -/
def IsDirectedCycle (D : V → V → Prop) (n : ℕ)
    (f : Fin (n + 2) → V) : Prop :=
  f 0 = f (Fin.last (n + 1)) ∧ ∀ i : Fin (n + 1), D (f i.castSucc) (f i.succ)

/-- `G` is dichromatically `k`-colourable if every orientation admits a
`k`-colouring with no monochromatic directed cycle. -/
def DichromaticColorable (k : ℕ) : Prop :=
  ∀ D : V → V → Prop, G.IsOrientation D →
    ∃ c : V → Fin k, ∀ (n : ℕ) (f : Fin (n + 2) → V),
      IsDirectedCycle D n f → ¬ ∃ col, ∀ i, c (f i) = col

/-- The dichromatic number of `G`: the least `k` such that `G` is
dichromatically `k`-colourable (`⊤` if there is none). -/
noncomputable def dichromaticNumber : ℕ∞ :=
  ⨅ n ∈ Set.ofPred (G.DichromaticColorable), (n : ℕ∞)

end SimpleGraph
