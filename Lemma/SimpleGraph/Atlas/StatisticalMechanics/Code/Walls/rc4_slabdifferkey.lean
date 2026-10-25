import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_slabdifferkey
open Finset StatMech StatMech.Walls


/--
[rc4_slab_differ_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
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
[rc4_keyFlip_eq_not_on_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_not_on_differ_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hne : k.1 a ≠ k.2 a) :
-- imply
  poc_keyFlip k ω a = !ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_not_on_differ k ω a hne

/--
[rc4_keyFlip_eq_id_off_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_id_off_differ_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (heq : k.1 a = k.2 a) :
-- imply
  poc_keyFlip k ω a = ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_id_off_differ k ω a heq

/--
[rc4_keyFlip_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_keyFlip_apply_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
  [Decidable (k.1 a ≠ k.2 a)] :
-- imply
  poc_keyFlip k ω a = if k.1 a ≠ k.2 a then !ω a else ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_apply k ω a

/--
[rc4_topKey_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_topKey_differ_eq
  {a : α} :
-- imply
  (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠ (poc_topKey : ConfigSpace α × ConfigSpace α).2 a := by
-- proof
  apply StatMech.Walls.rc4_topKey_differ a

/--
[rc4_slab_differ_key_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_slab_differ_key_top_eq
  {ω : ConfigSpace α}
  {a : α}
-- given
  (hk : ω ∈ rc2_slab (poc_topKey : ConfigSpace α × ConfigSpace α)) :
-- imply
  (poc_topKey : ConfigSpace α × ConfigSpace α).1 a = true ∧ (poc_topKey : ConfigSpace α × ConfigSpace α).2 a = false := by
-- proof
  apply StatMech.Walls.rc4_slab_differ_key_top hk a

/--
[rc4_keyFlip_top_eq_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_slabdifferkey.lean)
-/
@[path]
private lemma rc4_keyFlip_top_eq_not_eq
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω a = !ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_top_eq_not ω a


-- created on 2026-10-23
