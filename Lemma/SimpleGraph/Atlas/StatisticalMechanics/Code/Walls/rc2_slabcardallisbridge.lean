import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
open Finset StatMech StatMech.Walls


/--
[rc2_countBoxBridge_iff_slabCardAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_countBoxBridge_iff_slabCardAll_eq :
-- imply
  rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll := by
-- proof
  apply StatMech.Walls.rc2_countBoxBridge_iff_slabCardAll

/--
[rc2_countBoxBridge_iff_forall_slab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_countBoxBridge_iff_forall_slab_eq :
-- imply
  rc_core_CountBoxBridge ↔ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))) (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)), #(StatMech.poc_slabBox A B k) ≤ #(StatMech.poc_slabImg A B k) := by
-- proof
  apply StatMech.Walls.rc2_countBoxBridge_iff_forall_slab

/--
[rc2_reimerWprobCore_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_reimerWprobCore_of_bridge_eq
-- given
  (h : rc_core_CountBoxBridge) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc2_reimerWprobCore_of_bridge h

/--
[rc2_reimerWprobCore_of_slabCardAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_reimerWprobCore_of_slabCardAll_eq
-- given
  (h : StatMech.poc_SlabCardAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc2_reimerWprobCore_of_slabCardAll h

/--
[rc2_reimer_inequality_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_reimer_inequality_of_bridge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc_core_CountBoxBridge)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc2_reimer_inequality_of_bridge h hp A B

/--
[rc2_slabCardAll_is_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabcardallisbridge.lean)
-/
@[path]
private lemma rc2_slabCardAll_is_bridge_eq :
-- imply
  (rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll) ∧ (rc_core_CountBoxBridge → ReimerWprobCore) ∧ (rc_core_CountBoxBridge → ∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc2_slabCardAll_is_bridge


-- created on 2026-10-23
