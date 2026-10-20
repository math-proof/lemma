/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/LinearPartition.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic

namespace MetaMathlibExt

/-- An unordered `k`-linear partition of a simple graph in the sense of Gonzales,
JIS VOL25: nonempty ordered blocks partition the vertices, and consecutive vertices
within each block are nonadjacent. Concept `jis_term_096dd7cbe3f83bcfea2406a6`,
source `https://cs.uwaterloo.ca/journals/JIS/VOL25/Gonzales/gonzales2.tex`. -/
structure LinearPartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) where
  blocks : Finset (List V)
  card_eq : blocks.card = k
  nonempty : ∀ L ∈ blocks, L ≠ []
  nodup : ∀ L ∈ blocks, L.Nodup
  covers : ∀ v : V, ∃! L, L ∈ blocks ∧ v ∈ L
  consecutive : ∀ L ∈ blocks, List.IsChain (fun a b => ¬G.Adj a b) L

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

@[ext]
theorem LinearPartition.ext {P Q : LinearPartition G k}
    (h : P.blocks = Q.blocks) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem LinearPartition.existsUniqueBlock (P : LinearPartition G k) (v : V) :
    ∃! L, L ∈ P.blocks ∧ v ∈ L :=
  P.covers v

theorem LinearPartition.consecutive_mem (P : LinearPartition G k) {L : List V}
    (hL : L ∈ P.blocks) : List.IsChain (fun a b => ¬G.Adj a b) L :=
  P.consecutive L hL

end MetaMathlibExt
