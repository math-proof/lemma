import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc3_slabimgeqinter
open Finset StatMech StatMech.Walls


/--
[rc3_mem_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_mem_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc3_slab k ↔ orbitKey (ω, poc_keyFlip k ω) = k := by
-- proof
  apply StatMech.Walls.rc3_mem_slab k ω

/--
[rc3_mem_keyReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_mem_keyReflect_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {B : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc3_keyReflect k B ↔ poc_keyFlip k ω ∈ B := by
-- proof
  apply StatMech.Walls.rc3_mem_keyReflect k B ω

/--
[rc3_keyReflect_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_keyReflect_top_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  rc3_keyReflect poc_topKey B = rmr_reflect B := by
-- proof
  apply StatMech.Walls.rc3_keyReflect_top B

/--
[rc3_slabImg_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_slabImg_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  poc_slabImg A B k = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rc3_keyReflect k B ∧ ω ∈ rc3_slab k) := by
-- proof
  apply StatMech.Walls.rc3_slabImg_eq_inter A B k

/--
[rc3_sie_keyFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_sie_keyFlip_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip k (poc_keyFlip k ω) = ω := by
-- proof
  apply StatMech.Walls.rc3_sie_keyFlip_involutive k ω

/--
[rc3_slabImg_top_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_slabImg_top_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B poc_topKey = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
-- proof
  apply StatMech.Walls.rc3_slabImg_top_eq_inter A B

/--
[rc3_slabImg_eq_inter_top_recovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_slabImg_eq_inter_top_recovers_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B poc_topKey = Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
-- proof
  apply StatMech.Walls.rc3_slabImg_eq_inter_top_recovers A B

/--
[rc3_slabCard_top_iff_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_slabCard_top_iff_interCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_slabCard_top_iff_interCard A B

/--
[rc3_reimerCardForm_iff_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_reimerCardForm_iff_interCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_reimerCardForm_iff_interCard A B

/--
[rc3_interCard_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_interCard_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_interCard_of_slabCard h

/--
[rc3_interCard_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_interCard_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : PerOrbitCard A B) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_interCard_of_perOrbitCard h

/--
[rc3_interCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_interCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc2_boxCard rbi_A rbi_B ≤ rc2_interCard rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc3_interCard_rbi

/--
[rc3_interCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_interCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_interCard_of_disjoint_support hA hB hST

/--
[rc3_interCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean)
-/
@[path]
private lemma rc3_interCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  rc2_boxCard A B ≤ rc2_interCard A B := by
-- proof
  apply StatMech.Walls.rc3_interCard_of_box_empty hbox


-- created on 2026-10-23
