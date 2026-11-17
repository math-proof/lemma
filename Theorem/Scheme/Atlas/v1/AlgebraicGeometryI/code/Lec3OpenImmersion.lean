module

public import Mathlib
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec3OpenImmersion

public section

open TopologicalSpace Set


/--
[isIrreducibleComponent_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean)
-/
public theorem isIrreducibleComponent_iff_mem
  [TopologicalSpace X]
  {s : Set X} :
-- imply
  IsIrreducibleComponent s ↔ s ∈ irreducibleComponents X := by
-- proof
  rw [irreducibleComponents_eq_maximals_closed]
  simp only [Maximal, Set.mem_setOf_eq]
  constructor
  · intro ⟨hc, hi, hmax⟩
    exact ⟨⟨hc, hi⟩, fun t ⟨htc, hti⟩ hst => (hmax t htc hti hst).le⟩
  · intro ⟨⟨hc, hi⟩, hmax⟩
    exact ⟨hc, hi, fun t htc hti hst => le_antisymm (hmax ⟨htc, hti⟩ hst) hst⟩

/--
[IsIrreducibleComponent.isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean)
-/
public theorem IsIrreducibleComponent.isClosed
  [TopologicalSpace X]
  {s : Set X}
-- given
  (h : IsIrreducibleComponent s) :
-- imply
  IsClosed s :=
-- proof
  h.1

/--
[IsIrreducibleComponent.isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean)
-/
public theorem IsIrreducibleComponent.isIrreducible
  [TopologicalSpace X]
  {s : Set X}
-- given
  (h : IsIrreducibleComponent s) :
-- imply
  IsIrreducible s :=
-- proof
  h.2.1

/--
[IsIrreducibleComponent.eq_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean)
-/
public theorem IsIrreducibleComponent.eq_of_subset
  [TopologicalSpace X]
  {s t : Set X}
-- given
  (h : IsIrreducibleComponent s)
  (htc : IsClosed t)
  (hti : IsIrreducible t)
  (hst : s ⊆ t) :
-- imply
  t = s :=
-- proof
  h.2.2 t htc hti hst

/--
[exists_isIrreducibleComponent_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean)
-/
public theorem exists_isIrreducibleComponent_of_mem
  [TopologicalSpace X]
  {x : X} :
-- imply
  ∃ s : Set X, IsIrreducibleComponent s ∧ x ∈ s :=
-- proof
  ⟨irreducibleComponent x,
    (isIrreducibleComponent_iff_mem _).mpr (irreducibleComponent_mem_irreducibleComponents x),
    mem_irreducibleComponent⟩


-- created on 2026-10-23
