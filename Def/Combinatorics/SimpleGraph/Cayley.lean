/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Cayley.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Def.Combinatorics.SimpleGraph.MatrixTree.Part2
import Lemma.Finset.SimpleGraph.MatrixTree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Ring


section

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-!
# Cayley's formula

The complete graph on `n` vertices has `n^(n-2)` spanning trees.
-/

/-! ## Helpers -/

/-- Rooted forests on `U` with root set `R`, as parent maps `f : α → α`.
(a) `f` fixes everything outside `U \ R`; (b) `f` maps `U \ R` into `U`;
(c) a rank function strictly decreases along `f` on `U \ R` (acyclicity). -/
noncomputable def acyclicMaps {α : Type*} [Fintype α] [DecidableEq α]
    (U R : Finset α) : Finset (α → α) := by
  classical
  exact Finset.univ.filter fun f : α → α =>
    ((∀ x : α, x ∉ U \ R → f x = x) ∧
     (∀ x : α, x ∈ U \ R → f x ∈ U) ∧
     (∃ h : α → ℕ, ∀ x : α, x ∈ U \ R → h (f x) < h x))

def fwd {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) (U R : Finset α) (f : α → α) : α → α :=
  fun x => if x ∈ (U \ R).filter (fun y => f y = r) then x else f x

def bwd {α : Type*} [DecidableEq α] (r : α) (S : Finset α) (g : α → α) : α → α :=
  fun x => if x ∈ S then r else g x

open scoped Classical in
/-- Parent map of a graph toward a root, via distance-descent choice. -/
noncomputable def treeParent {V : Type*}
    (T : _root_.SimpleGraph V) (r : V) : V → V :=
  fun v => if _hv : v = r then r
    else if _Hex : ∃ u, T.Adj v u ∧ T.dist u r < T.dist v r then
      Classical.choose _Hex
    else v

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
