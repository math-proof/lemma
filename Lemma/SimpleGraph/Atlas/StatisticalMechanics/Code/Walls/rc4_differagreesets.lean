import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc4_differagreesets
open Finset StatMech StatMech.Walls


/--
[rc4_mem_differSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_mem_differSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {a : α} :
-- imply
  a ∈ rc4_differSet k ↔ k.1 a ≠ k.2 a := by
-- proof
  apply StatMech.Walls.rc4_mem_differSet k a

/--
[rc4_mem_agreeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_mem_agreeSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {a : α} :
-- imply
  a ∈ rc4_agreeSet k ↔ k.1 a = k.2 a := by
-- proof
  apply StatMech.Walls.rc4_mem_agreeSet k a

/--
[rc4_differSet_disjoint_agreeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_differSet_disjoint_agreeSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Disjoint (rc4_differSet k) (rc4_agreeSet k) := by
-- proof
  apply StatMech.Walls.rc4_differSet_disjoint_agreeSet k

/--
[rc4_agreeSet_eq_compl_differSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_agreeSet_eq_compl_differSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  rc4_agreeSet k = (rc4_differSet k)ᶜ := by
-- proof
  apply StatMech.Walls.rc4_agreeSet_eq_compl_differSet k

/--
[rc4_differSet_eq_compl_agreeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_differSet_eq_compl_agreeSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  rc4_differSet k = (rc4_agreeSet k)ᶜ := by
-- proof
  apply StatMech.Walls.rc4_differSet_eq_compl_agreeSet k

/--
[rc4_differSet_union_agreeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_differSet_union_agreeSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  rc4_differSet k ∪ rc4_agreeSet k = Finset.univ := by
-- proof
  apply StatMech.Walls.rc4_differSet_union_agreeSet k

/--
[rc4_card_differSet_add_card_agreeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_card_differSet_add_card_agreeSet_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  (rc4_differSet k).card + (rc4_agreeSet k).card = Fintype.card α := by
-- proof
  apply StatMech.Walls.rc4_card_differSet_add_card_agreeSet k

/--
[rc4_orbitKey_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_orbitKey_valid_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {a : α}
-- given
  (ha : a ∈ rc4_differSet (orbitKey p)) :
-- imply
  (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false := by
-- proof
  apply StatMech.Walls.rc4_orbitKey_valid p a ha

/--
[rc4_orbitKey_agree_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_orbitKey_agree_value_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {a : α}
-- given
  (ha : a ∈ rc4_agreeSet k) :
-- imply
  k.1 a = k.2 a := by
-- proof
  apply StatMech.Walls.rc4_orbitKey_agree_value k a ha

/--
[rc4_orbitKey_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_orbitKey_value_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {a : α} :
-- imply
  (a ∈ rc4_differSet (orbitKey p) ∧ (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false) ∨ (a ∈ rc4_agreeSet (orbitKey p) ∧ (orbitKey p).1 a = (orbitKey p).2 a) := by
-- proof
  apply StatMech.Walls.rc4_orbitKey_value p a

/--
[rc4_keyFlip_eq_compl_on_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_compl_on_differ_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (ha : a ∈ rc4_differSet k) :
-- imply
  poc_keyFlip k ω a = !ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_compl_on_differ k ω a ha

/--
[rc4_keyFlip_eq_self_on_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_keyFlip_eq_self_on_agree_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
  {a : α}
-- given
  (ha : a ∈ rc4_agreeSet k) :
-- imply
  poc_keyFlip k ω a = ω a := by
-- proof
  apply StatMech.Walls.rc4_keyFlip_eq_self_on_agree k ω a ha

/--
[rc4_snd_recovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_snd_recovered_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  p.2 = poc_keyFlip k p.1 := by
-- proof
  apply StatMech.Walls.rc4_snd_recovered p k hk

/--
[rc4_snd_recovered_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean)
-/
@[path]
private lemma rc4_snd_recovered_pointwise_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
  {a : α}
-- given
  (hk : orbitKey p = k) :
-- imply
  (a ∈ rc4_differSet k → p.2 a = !p.1 a) ∧ (a ∈ rc4_agreeSet k → p.2 a = p.1 a) := by
-- proof
  apply StatMech.Walls.rc4_snd_recovered_pointwise p k hk a


-- created on 2026-10-23
