/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/NashWilliams.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.CompletePartialOrder


section

namespace MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted

/-!
# Nash–Williams arboricity
-/

/-- Edge-coloring whose color classes are forests (acyclic). -/
def IsArboricityColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (C : G.EdgeLabeling (Fin k)) : Prop :=
  ∀ i : Fin k, (C.labelGraph i).IsAcyclic

/-- `nwForest S R c x i`: color class `i` of the near-coloring `(S, x, c)`
restricted to `R`: the graph on edges of `S ∩ R` labeled `i`, minus `x`. -/
def nwForest {V : Type*} {k : ℕ} (S : Finset (Sym2 V)) (R : Set (Sym2 V))
    (c : Sym2 V → Fin k) (x : Sym2 V) (i : Fin k) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ S ∧ e ∈ R ∧ e ≠ x ∧ c e = i}

/-- `nwNear S c x`: `x ∈ S` and every class of `(S, x, c)` is a forest. -/
def nwNear {V : Type*} {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k)
    (x : Sym2 V) : Prop :=
  x ∈ S ∧ ∀ i : Fin k, (nwForest S Set.univ c x i).IsAcyclic

/-- `nwFull k S`: `S` admits a full forest coloring. -/
def nwFull {V : Type*} (k : ℕ) (S : Finset (Sym2 V)) : Prop :=
  ∃ c : Sym2 V → Fin k, ∀ i : Fin k,
    (SimpleGraph.fromEdgeSet {e | e ∈ S ∧ c e = i}).IsAcyclic

/-- `nwMove S`: one exchange step. From uncovered `x` (with `x = s(u,v)`),
relabel `x` with `y`'s color, making `y` uncovered; allowed when `u, v`
are disconnected in class `c y` with `y` removed. -/
def nwMove {V : Type*} {k : ℕ} [DecidableEq V] (S : Finset (Sym2 V)) :
    (Sym2 V × (Sym2 V → Fin k)) → (Sym2 V × (Sym2 V → Fin k)) → Prop
  | (x, c), (y, c') => ∃ u v : V, x = s(u, v) ∧ y ∈ S ∧ y ≠ x ∧
      c' = Function.update c x (c y) ∧
      ¬ ((nwForest S Set.univ c x (c y)).deleteEdges {y}).Reachable u v

/-- `nwReached S s0`: edges uncovered in some state reachable from `s0`. -/
def nwReached {V : Type*} {k : ℕ} [DecidableEq V] (S : Finset (Sym2 V))
    (s0 : Sym2 V × (Sym2 V → Fin k)) : Set (Sym2 V) :=
  {y | ∃ t, Relation.ReflTransGen (nwMove S) s0 t ∧ t.1 = y}

end MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted
end
