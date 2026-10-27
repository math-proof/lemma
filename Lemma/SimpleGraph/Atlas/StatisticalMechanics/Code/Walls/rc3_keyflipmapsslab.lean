import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipmapsslab
open Finset StatMech StatMech.Walls


/--
[rc3_kfms_keyFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_kfms_keyFlip_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Function.Involutive (poc_keyFlip k) := by
-- proof
  apply StatMech.Walls.rc3_kfms_keyFlip_involutive k

/--
[rc3_kfms_orbitKey_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_kfms_orbitKey_symm_eq
  [Fintype α]
  [DecidableEq α]
  {a b : ConfigSpace α} :
-- imply
  orbitKey (a, b) = orbitKey (b, a) := by
-- proof
  apply StatMech.Walls.rc3_kfms_orbitKey_symm a b

/--
[rc3_keyFlip_maps_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_keyFlip_maps_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ rc2_slab k) :
-- imply
  poc_keyFlip k ω ∈ rc2_slab k := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_maps_slab k hω

/--
[rc3_keyFlip_mapsTo_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_keyFlip_mapsTo_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Set.MapsTo (poc_keyFlip k) (rc2_slab k) (rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_mapsTo_slab k

/--
[rc3_keyFlip_invOn_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_keyFlip_invOn_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Set.InvOn (poc_keyFlip k) (poc_keyFlip k) (rc2_slab k) (rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_invOn_slab k

/--
[rc3_keyFlip_injOn_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_keyFlip_injOn_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Set.InjOn (poc_keyFlip k) (rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_injOn_slab k

/--
[rc3_keyFlip_bijOn_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_keyFlip_bijOn_slab_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Set.BijOn (poc_keyFlip k) (rc2_slab k) (rc2_slab k) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_bijOn_slab k

/--
[rc3_mem_slab_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipmapsslab.lean)
-/
@[path]
private lemma rc3_mem_slab_top_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc2_slab (poc_topKey : ConfigSpace α × ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc3_mem_slab_top ω


-- created on 2026-10-23
