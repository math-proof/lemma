import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_keyflipiscompl
open Finset StatMech StatMech.Walls


/--
[rc4_restrict_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_restrict_apply_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {b : rc4_differ k} :
-- imply
  rc4_restrict k ω b = ω b.val := by
-- proof
  apply StatMech.Walls.rc4_restrict_apply k ω b

/--
[rc4_keyFlip_eq_on_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_on_differ_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (ha : k.1 a ≠ k.2 a) :
-- imply
  poc_keyFlip k ω a = !(ω a) := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_on_differ k ω a ha

/--
[rc4_keyFlip_eq_off_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_off_differ_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (ha : k.1 a = k.2 a) :
-- imply
  poc_keyFlip k ω a = ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_off_differ k ω a ha

/--
[rc4_restrict_keyFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_restrict_keyFlip_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  rc4_restrict k (poc_keyFlip k ω) = rmr_compl (rc4_restrict k ω) := by
-- proof
  apply StatMech.Walls.rc4_restrict_keyFlip k ω

/--
[rc4_restrict_keyFlip_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_restrict_keyFlip_apply_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {b : rc4_differ k} :
-- imply
  rc4_restrict k (poc_keyFlip k ω) b = !(rc4_restrict k ω b) := by
-- proof
  apply StatMech.Walls.rc4_restrict_keyFlip_apply k ω b

/--
[rc4_restrict_keyFlip_keyFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_restrict_keyFlip_keyFlip_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  rc4_restrict k (poc_keyFlip k (poc_keyFlip k ω)) = rc4_restrict k ω := by
-- proof
  apply StatMech.Walls.rc4_restrict_keyFlip_keyFlip k ω

/--
[rc4_keyReflect_mem_via_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_keyReflect_mem_via_compl_eq
  {k : ConfigSpace α × ConfigSpace α}
  {B : Set (ConfigSpace α)}
  {P : ConfigSpace (rc4_differ k) → Prop}
  {ω : ConfigSpace α}
-- given
  (hP : ∀ ω, poc_keyFlip k ω ∈ B ↔ P (rc4_restrict k (poc_keyFlip k ω))) :
-- imply
  poc_keyFlip k ω ∈ B ↔ P (rmr_compl (rc4_restrict k ω)) := by
-- proof
  apply StatMech.Walls.rc4_keyReflect_mem_via_compl k hP ω

/--
[rc4_slab_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_slab_frozen_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hk : ω ∈ rc2_slab k)
  (hne : k.1 a = k.2 a) :
-- imply
  ω a = k.1 a := by
-- proof
  apply StatMech.Walls.rc4_slab_frozen hk a hne

/--
[rc4_slab_differ_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_slab_differ_key_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hk : ω ∈ rc2_slab k)
  (hne : k.1 a ≠ k.2 a) :
-- imply
  k.1 a = true ∧ k.2 a = false := by
-- proof
  apply StatMech.Walls.rc4_slab_differ_key hk a hne

/--
[rc4_topKey_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_topKey_differ_eq
  {a : α} :
-- imply
  (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠ (poc_topKey : ConfigSpace α × ConfigSpace α).2 a := by
-- proof
  apply StatMech.Walls.rc4_topKey_differ a

/--
[rc4_keyFlip_top_eq_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean)
-/
@[path]
private lemma rc4_keyFlip_top_eq_compl_eq
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = rmr_compl ω := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_top_eq_compl ω


-- created on 2026-10-23
