/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/


/-- A multigraph described by a symmetric edge-multiplicity function. Loops are permitted. -/
structure Multigraph (V : Type*) where
  /-- The multiplicity of edges between two vertices. -/
  edgeMult : V → V → ℕ
  /-- Edge multiplicity is symmetric. -/
  symm : ∀ v w, edgeMult v w = edgeMult w v

