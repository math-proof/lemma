/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Def.Combinatorics.SimpleGraph.Contraction
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

/-- A vertex in `D` survives contraction as its subtype copy. -/
@[simp]
theorem collapseOutside_of_mem {V : Type*} (D : Set V) {v : V} (hv : v ∈ D) :
    collapseOutside D v = some ⟨v, hv⟩ := by
  classical
  simp [collapseOutside, hv]

/-- A vertex outside `D` is sent to the contraction vertex. -/
@[simp]
theorem collapseOutside_of_notMem {V : Type*} (D : Set V) {v : V} (hv : v ∉ D) :
    collapseOutside D v = none := by
  classical
  simp [collapseOutside, hv]

/-- Characterization of the vertices that map to a surviving subtype vertex. -/
@[simp]
theorem collapseOutside_eq_some_iff {V : Type*} (D : Set V) (v : V) (a : D) :
    collapseOutside D v = some a ↔ v = a := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp only [Option.some.injEq]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  · rw [collapseOutside_of_notMem D hv]
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      apply hv
      rw [h]
      exact a.property

end SimpleGraph
