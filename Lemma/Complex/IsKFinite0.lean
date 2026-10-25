import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
open ContinuousRep


/--
[isKFinite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean)
-/
@[path]
private lemma isKFinite_zero_eq
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep G V}
  {K : Subgroup G} :
-- imply
  IsKFinite π K (0 : V) := by
-- proof
  apply ContinuousRep.isKFinite_zero π K

/--
[isKFinite_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean)
-/
@[path]
private lemma isKFinite_add_eq
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep G V}
  {K : Subgroup G}
  {v w : V}
-- given
  (hv : IsKFinite π K v)
  (hw : IsKFinite π K w) :
-- imply
  IsKFinite π K (v + w) := by
-- proof
  apply ContinuousRep.isKFinite_add π K v w hv hw

/--
[isKFinite_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean)
-/
@[path]
private lemma isKFinite_smul_eq
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep G V}
  {K : Subgroup G}
  {c : ℂ}
  {v : V}
-- given
  (hv : IsKFinite π K v) :
-- imply
  IsKFinite π K (c • v) := by
-- proof
  apply ContinuousRep.isKFinite_smul π K c v hv

/--
[mem_kFiniteSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean)
-/
@[path]
private lemma mem_kFiniteSubspace_eq
  [Group G]
  [TopologicalSpace G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep G V}
  {K : Subgroup G}
  {v : V} :
-- imply
  v ∈ kFiniteSubspace π K ↔ IsKFinite π K v := by
-- proof
  apply ContinuousRep.mem_kFiniteSubspace π K v


-- created on 2026-10-23
-- updated on 2026-10-24
