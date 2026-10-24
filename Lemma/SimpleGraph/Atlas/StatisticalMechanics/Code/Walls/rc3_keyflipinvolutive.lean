import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
open Finset StatMech StatMech.Walls


/--
[rc3_flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_flip_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {d : α → Bool} :
-- imply
  Function.Involutive (StatMech.poc_flip d : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc3_flip_involutive d

/--
[rc3_flip_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_flip_flip_eq
  [Fintype α]
  [DecidableEq α]
  {d : α → Bool}
  {ω : ConfigSpace α} :
-- imply
  StatMech.poc_flip d (StatMech.poc_flip d ω) = ω := by
-- proof
  apply StatMech.Walls.rc3_flip_flip d ω

/--
[rc3_keyFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_keyFlip_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Function.Involutive (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_involutive k

/--
[rc3_keyFlip_keyFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_keyFlip_keyFlip_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  StatMech.poc_keyFlip k (StatMech.poc_keyFlip k ω) = ω := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_keyFlip k ω

/--
[rc3_keyFlip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_keyFlip_injective_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Function.Injective (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_injective k

/--
[rc3_keyFlip_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_keyFlip_bijective_eq
  [Fintype α]
  [DecidableEq α]
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  Function.Bijective (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_bijective k

/--
[rc3_keyFlip_top_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_keyflipinvolutive.lean)
-/
@[path]
private lemma rc3_keyFlip_top_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α) (StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α) ω) = ω := by
-- proof
  apply StatMech.Walls.rc3_keyFlip_top_involutive ω


-- created on 2026-10-23
