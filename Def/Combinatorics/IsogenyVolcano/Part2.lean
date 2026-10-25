/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Instance.Combinatorics.IsogenyVolcano
set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/


namespace IsogenyVolcano

variable {ℓ : ℕ} {C : IsogenyVolcano ℓ}

/-- Surface vertices. -/
def isSurface (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = 0

/-- Floor vertices. -/
def isFloor (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = Fin.last C.depth

/-- Depth of the volcano. -/
def volcanoDepth (C : IsogenyVolcano ℓ) : ℕ :=
  C.depth

/-- Horizontal edge on the surface. -/
def IsHorizontalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) = 0 ∧ (C.level w : ℕ) = 0

/-- Descending edge from `v` down to `w`. -/
def IsDescendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) + 1 = (C.level w : ℕ)

/-- An ascending edge from `v` to `w`, where `w` lies one level above `v`. -/
def IsAscendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level w : ℕ) + 1 = (C.level v : ℕ)

/-- Vertical edge in either direction. -/
def IsVerticalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.IsDescendingEdge v w ∨ C.IsAscendingEdge v w

end IsogenyVolcano
