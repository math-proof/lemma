import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter
open Finset StatMech StatMech.Walls


/--
[rc2_slabImg_top_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_slabImg_top_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B poc_topKey = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
-- proof
  apply StatMech.Walls.rc2_slabImg_top_eq_inter A B

/--
[rc2_mem_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_mem_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc2_slab k ↔ orbitKey (ω, poc_keyFlip k ω) = k := by
-- proof
  apply StatMech.Walls.rc2_mem_slab k ω

/--
[rc2_mem_keyReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_mem_keyReflect_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc2_keyReflect k B ↔ poc_keyFlip k ω ∈ B := by
-- proof
  apply StatMech.Walls.rc2_mem_keyReflect k B ω

/--
[rc2_keyReflect_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_keyReflect_top_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  rc2_keyReflect poc_topKey B = rmr_reflect B := by
-- proof
  apply StatMech.Walls.rc2_keyReflect_top B

/--
[rc2_slabImg_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_slabImg_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  poc_slabImg A B k = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc2_slabImg_eq_inter A B k

/--
[rc2_keyFlip_involutive_on_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_keyFlip_involutive_on_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip k (poc_keyFlip k ω) = ω := by
-- proof
  apply StatMech.Walls.rc2_keyFlip_involutive_on_slab k ω

/--
[rc2_slabImg_eq_inter_top_recovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_slabImg_eq_inter_top_recovers_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B poc_topKey = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
-- proof
  apply StatMech.Walls.rc2_slabImg_eq_inter_top_recovers A B

/--
[rc2_slabCard_top_iff_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_slabCard_top_iff_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc2_slabCard_top_iff_inter A B

/--
[rc2_reimerCardForm_iff_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean)
-/
@[path]
private lemma rc2_reimerCardForm_iff_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc2_reimerCardForm_iff_inter A B


-- created on 2026-10-23
