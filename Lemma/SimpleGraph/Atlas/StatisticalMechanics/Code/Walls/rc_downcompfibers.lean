import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc_downcompfibers.Part3
open Finset StatMech StatMech.Walls


/--
[memberFiber_to_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma memberFiber_to_inter_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (Finset E)}
  {s : Finset E}
-- given
  (hi : i ∉ s) :
-- imply
  insert i s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∧ (s ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.memberFiber_to_inter i 𝒜 hi

/--
[nonMemberFiber_to_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma nonMemberFiber_to_union_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (Finset E)}
  {s : Finset E}
-- given
  (hi : i ∉ s) :
-- imply
  s ∈ Down.compression i 𝒜 ↔ (insert i s ∈ 𝒜) ∨ (s ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.nonMemberFiber_to_union i 𝒜 hi

/--
[raiseCoord_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma raiseCoord_self_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E} :
-- imply
  raiseCoord i ω i = true := by
-- proof
  apply StatMech.Walls.raiseCoord_self i ω

/--
[raiseCoord_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma raiseCoord_of_ne_eq
  [Fintype E]
  [DecidableEq E]
  {i j : E}
  {ω : ConfigSpace E}
-- given
  (h : j ≠ i) :
-- imply
  raiseCoord i ω j = ω j := by
-- proof
  apply StatMech.Walls.raiseCoord_of_ne h ω

/--
[cfgSupport_raiseCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma cfgSupport_raiseCoord_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E} :
-- imply
  cfgSupport (raiseCoord i ω) = insert i (cfgSupport ω) := by
-- proof
  apply StatMech.Walls.cfgSupport_raiseCoord i ω

/--
[mem_image_cfgSupport_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma mem_image_cfgSupport_iff_eq
  [Fintype E]
  [DecidableEq E]
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  cfgSupport ω ∈ 𝒜.image cfgSupport ↔ ω ∈ 𝒜 := by
-- proof
  apply StatMech.Walls.mem_image_cfgSupport_iff 𝒜 ω

/--
[rc_memberFiber_to_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_memberFiber_to_inter_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.rc_memberFiber_to_inter i 𝒜 hω

/--
[rc_nonMemberFiber_to_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_nonMemberFiber_to_union_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.rc_nonMemberFiber_to_union i 𝒜 hω

/--
[rc_downCompress_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_downCompress_fibers_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜)) ∧ (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜)) := by
-- proof
  apply StatMech.Walls.rc_downCompress_fibers i 𝒜 hω

/--
[rc_downCompress_fiber_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_downCompress_fiber_count_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  ind (raiseCoord i ω ∈ downCompress i 𝒜) + ind (ω ∈ downCompress i 𝒜) = ind (raiseCoord i ω ∈ 𝒜) + ind (ω ∈ 𝒜) := by
-- proof
  apply StatMech.Walls.rc_downCompress_fiber_count i 𝒜 hω

/--
[rc_fiber_univ_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_fiber_univ_high_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  raiseCoord i ω ∈ downCompress i (Finset.univ : Finset (ConfigSpace E)) := by
-- proof
  apply StatMech.Walls.rc_fiber_univ_high i hω

/--
[rc_fiber_empty_low](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_fiber_empty_low_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  ω ∉ downCompress i (∅ : Finset (ConfigSpace E)) := by
-- proof
  apply StatMech.Walls.rc_fiber_empty_low i hω

/--
[rc_fiber_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean)
-/
@[path]
private lemma rc_fiber_cases_eq
  [Fintype E]
  [DecidableEq E]
  {i : E}
  {𝒜 : Finset (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hω : ω i = false) :
-- imply
  (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∧ ω ∈ 𝒜)) ∧ (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∨ ω ∈ 𝒜)) := by
-- proof
  apply StatMech.Walls.rc_fiber_cases i 𝒜 hω


-- created on 2026-10-23
