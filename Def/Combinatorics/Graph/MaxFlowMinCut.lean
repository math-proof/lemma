/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section

namespace MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-! # Max-flow min-cut theorem

Proves the finite directed max-flow min-cut theorem with explicit definitions of
feasible flow, conservation, flow value, and cut capacity.
-/

/-- A feasible flow respects  `0 ≤ f ≤ cap` and conserves flow at interior vertices. -/
def IsFeasibleFlow {V : Type*} [Fintype V] [DecidableEq V]
    (cap : V → V → ℝ) (s t : V) (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧
  (∀ u v, f u v ≤ cap u v) ∧
  (∀ v, v ≠ s → v ≠ t → ∑ u : V, f u v = ∑ w : V, f v w)

/-- Net outflow from the source `s`; the flow value. -/
def flowValue {V : Type*} [Fintype V] [DecidableEq V]
    (s : V) (f : V → V → ℝ) : ℝ :=
  (∑ v : V, f s v) - ∑ u : V, f u s

/-- An `s-t` cut is a vertex set `S` with `s ∈ S`, `t ∉ S`. -/
def IsSTCut {V : Type*} [Fintype V] [DecidableEq V]
    (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S

/-- Capacity of cut `S`: sum of capacities of arcs leaving `S`. -/
def cutCapacity {V : Type*} [Fintype V] [DecidableEq V]
    (cap : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ (Finset.univ : Finset V) \ S, cap u v

/-- Vertices reachable from `s` along residual edges (the future min cut). -/
def ReachableFrom {V : Type*} [Fintype V] [DecidableEq V]
    (cap : V → V → ℝ) (s : V) (f : V → V → ℝ) (a : V) : Prop :=
  ∃ (k : ℕ) (w : ℕ → V), w 0 = s ∧
    (∀ i, i < k → f (w i) (w (i + 1)) < cap (w i) (w (i + 1)) ∨ 0 < f (w (i + 1)) (w i)) ∧
    w k = a

end MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted
end
