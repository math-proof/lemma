import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kwd_flipfiber
open Finset StatMech StatMech.Walls


/--
[flipConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma flipConfig_apply_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {v : V} :
-- imply
  flipConfig s v = ! s v := by
-- proof
  apply StatMech.Walls.flipConfig_apply s v

/--
[flipConfig_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma flipConfig_flipConfig_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  flipConfig (flipConfig s) = s := by
-- proof
  apply StatMech.Walls.flipConfig_flipConfig s

/--
[cutEdges_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma cutEdges_flipConfig_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  cutEdges Gp (flipConfig s) = cutEdges Gp s := by
-- proof
  apply StatMech.Walls.cutEdges_flipConfig s

/--
[flipConfig_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma flipConfig_ne_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {s : ConfigSpace V} :
-- imply
  flipConfig s ≠ s := by
-- proof
  apply StatMech.Walls.flipConfig_ne s

/--
[cutMap_fiber_eq_flip_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma cutMap_fiber_eq_flip_orbit_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {s : ConfigSpace V}
-- given
  (hG : Gp.Preconnected) :
-- imply
  (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = cutEdges Gp s)) = {s, flipConfig s} := by
-- proof
  apply StatMech.Walls.cutMap_fiber_eq_flip_orbit hG s

/--
[cutMap_fiber_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma cutMap_fiber_card_eq_two_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {s : ConfigSpace V}
-- given
  (hG : Gp.Preconnected) :
-- imply
  (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = cutEdges Gp s)).card = 2 := by
-- proof
  apply StatMech.Walls.cutMap_fiber_card_eq_two hG s

/--
[cutMap_fiber_eq_flip_orbit_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_flipfiber.lean)
-/
@[path]
private lemma cutMap_fiber_eq_flip_orbit_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {δ : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hG : Gp.Preconnected)
  (hs : cutEdges Gp s = δ) :
-- imply
  (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = δ)) = {s, flipConfig s} := by
-- proof
  apply StatMech.Walls.cutMap_fiber_eq_flip_orbit_of_mem hG hs


-- created on 2026-10-23
