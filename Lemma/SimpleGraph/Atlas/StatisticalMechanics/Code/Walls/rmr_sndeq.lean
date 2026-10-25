import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmr_sndeq
open Finset StatMech StatMech.Walls


/--
[rmr_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_sndeq.lean)
-/
@[path]
private lemma rmr_snd_eq_eq
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  p.2 = rmr_keyFlip k p.1 := by
-- proof
  apply StatMech.Walls.rmr_snd_eq p k hk

/--
[rmr_keyFlip_eq_poc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_sndeq.lean)
-/
@[path]
private lemma rmr_keyFlip_eq_poc_eq
  {k : ConfigSpace α × ConfigSpace α}
  {ω : ConfigSpace α} :
-- imply
  rmr_keyFlip k ω = poc_keyFlip k ω := by
-- proof
  apply StatMech.Walls.rmr_keyFlip_eq_poc k ω

/--
[rmr_keyFlip_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_sndeq.lean)
-/
@[path]
private lemma rmr_keyFlip_fst_eq
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  p.1 = rmr_keyFlip k p.2 := by
-- proof
  apply StatMech.Walls.rmr_keyFlip_fst p k hk

/--
[rmr_keyFlip_keyFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_sndeq.lean)
-/
@[path]
private lemma rmr_keyFlip_keyFlip_eq
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  rmr_keyFlip k (rmr_keyFlip k p.1) = p.1 := by
-- proof
  apply StatMech.Walls.rmr_keyFlip_keyFlip p k hk


-- created on 2026-10-23
