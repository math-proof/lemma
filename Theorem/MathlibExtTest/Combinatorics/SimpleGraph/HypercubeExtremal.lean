/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/HypercubeExtremal.lean -/


import Def.Combinatorics.SimpleGraph.HypercubeExtremal
import Lemma.SimpleGraph.HypercubeExtremal


namespace SimpleGraph

/-- `Q_0`: no adjacency. -/
example (x y : Fin 0 → Bool) : ¬ (hypercubeGraph 0).Adj x y :=
  hypercubeGraph_zero_not_adj x y

/-- `Q_1`: the constant-`true` and constant-`false` vertices are adjacent. -/
example : (hypercubeGraph 1).Adj (fun _ => true) (fun _ => false) :=
  hypercubeGraph_one_adj

/-- Adjacency characterization unfolds to unique differing coordinate. -/
example (n : ℕ) (x y : Fin n → Bool) :
    (hypercubeGraph n).Adj x y ↔ ∃! i, x i ≠ y i :=
  hypercubeGraph_adj n x y

/-- No vertex is adjacent to itself. -/
example (n : ℕ) (x : Fin n → Bool) : ¬ (hypercubeGraph n).Adj x x := by
  simp

/-- `Q_0` has an empty edge set. -/
example : (hypercubeGraph 0).edgeSet = ∅ :=
  hypercubeGraph_zero_edgeSet

/-- Subgraphs of `Q_n` satisfy the ambient edge-count bound. -/
example (n : ℕ) (S : Subgraph (hypercubeGraph n)) :
    S.edgeSet.ncard ≤ (hypercubeGraph n).edgeSet.ncard :=
  hypercubeGraph_subgraph_edgeSet_ncard_le n S

/-- Boundary value: extremal number over `Q_0` vanishes. -/
example {W : Type*} (H : SimpleGraph W) : hypercubeTuranNumber 0 H = 0 :=
  hypercubeTuranNumber_zero H

/-- General bound: the extremal number never exceeds the edges of `Q_n`. -/
example (n : ℕ) {W : Type*} (H : SimpleGraph W) :
    hypercubeTuranNumber n H ≤ (hypercubeGraph n).edgeSet.ncard :=
  hypercubeTuranNumber_le_edgeSet_ncard n H

/-- Lower bound at a concrete bottom subgraph. -/
example (n : ℕ) :
    (⊥ : Subgraph (hypercubeGraph n)).edgeSet.ncard ≤
      hypercubeTuranNumber n (completeGraph (Fin 2)) :=
  le_hypercubeTuranNumber n (⊥ : Subgraph (hypercubeGraph n))
    (by exact free_bot (by simp))

/-- Lower bound over `Q_0`: every eligible subgraph counts into the maximum. -/
example {W : Type*} {H : SimpleGraph W} (S : Subgraph (hypercubeGraph 0))
    (hfree : H.Free S.coe) : S.edgeSet.ncard ≤ hypercubeTuranNumber 0 H :=
  le_hypercubeTuranNumber 0 S hfree

/-- Attainment at `n = 1` for the concrete forbidden graph. -/
example :
    ∃ S : Subgraph (hypercubeGraph 1),
      (completeGraph (Fin 2)).Free S.coe ∧
        S.edgeSet.ncard = hypercubeTuranNumber 1 (completeGraph (Fin 2)) :=
  exists_attains_hypercubeTuranNumber 1
    ⟨(⊥ : Subgraph (hypercubeGraph 1)), by exact free_bot (by simp)⟩

end SimpleGraph
