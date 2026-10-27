import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.IrreducibleComponentDef
open TopologicalSpace


/--
[isIrreducibleComponentOf_iff_maximal_closed_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean)
-/
@[path]
lemma isIrreducibleComponentOf_iff_maximal_closed_irreducible
  [TopologicalSpace X]
  {s : Set X} :
-- imply
  IsIrreducibleComponentOf s ↔ Maximal (fun t => IsClosed t ∧ IsIrreducible t) s := by
-- proof
  unfold IsIrreducibleComponentOf
  constructor
  · intro hs
    rwa [irreducibleComponents_eq_maximals_closed] at hs
  · intro hs
    rwa [irreducibleComponents_eq_maximals_closed]

/--
[IsIrreducibleComponentOf.isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean)
-/
@[path]
lemma IsIrreducibleComponentOf.isIrreducible
  [TopologicalSpace X]
  {s : Set X}
-- given
  (hs : IsIrreducibleComponentOf s) :
-- imply
  IsIrreducible s :=
-- proof
  hs.1

/--
[IsIrreducibleComponentOf.isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean)
-/
@[path]
lemma IsIrreducibleComponentOf.isClosed
  [TopologicalSpace X]
  {s : Set X}
-- given
  (hs : IsIrreducibleComponentOf s) :
-- imply
  IsClosed s :=
-- proof
  isClosed_of_mem_irreducibleComponents s hs

/--
[exists_irreducibleComponent_superset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean)
-/
@[path]
lemma exists_irreducibleComponent_superset
  [TopologicalSpace X]
  {s : Set X}
-- given
  (hs : IsIrreducible s) :
-- imply
  ∃ t, IsIrreducibleComponentOf t ∧ s ⊆ t := by
-- proof
  obtain ⟨t, ht, hst⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible s hs
  exact ⟨t, ht, hst⟩

/--
[exists_irreducibleComponent_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean)
-/
@[path]
lemma exists_irreducibleComponent_of_mem
  [TopologicalSpace X]
  {x : X} :
-- imply
  ∃ s, IsIrreducibleComponentOf s ∧ x ∈ s :=
-- proof
  ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩


-- created on 2026-10-23
