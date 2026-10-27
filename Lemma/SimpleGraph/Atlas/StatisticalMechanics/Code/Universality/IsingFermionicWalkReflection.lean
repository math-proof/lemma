import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
open StatMech StatMech.Universality StatMech.Universality.IsingDiagonalWalkHitSplit


/--
[firstHitSplit_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma firstHitSplit_steps_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
-- imply
  w.steps = path := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.firstHitSplit_steps h

/--
[firstHitSplit_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma firstHitSplit_firstHit_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
-- imply
  w.FirstHit := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.firstHitSplit_firstHit h

/--
[firstHitSplit_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma firstHitSplit_eq_some_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (hw : w.FirstHit) :
-- imply
  isingDiagonalWalkFirstHitSplit? start level w.steps = some w := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.firstHitSplit_eq_some w hw

/--
[reflect_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_before_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.before = w.before := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_before w

/--
[reflect_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_after_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.after = w.after.map reflectIncrement := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_after w

/--
[reflect_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_reflect_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.reflect = w := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_reflect w

/--
[reflect_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_length_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.steps.length = w.steps.length := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_length w

/--
[reflect_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_valid_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (hw : w.Valid) :
-- imply
  w.reflect.Valid := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_valid w hw

/--
[reflect_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_firstHit_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (hw : w.FirstHit) :
-- imply
  w.reflect.FirstHit := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_firstHit w hw

/--
[reflect_endpoint_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_endpoint_fst_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.endpoint.1 = 2 * level - w.endpoint.1 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_endpoint_fst w

/--
[reflect_endpoint_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflect_endpoint_snd_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflect.endpoint.2 = w.endpoint.2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflect_endpoint_snd w

/--
[reflectedEndpoint_reflectedEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectedEndpoint_reflectedEndpoint_eq
  {start : Int × Int}
  {level : Int}
  {level : Int}
  {target : Int × Int} :
-- imply
  reflectedEndpoint level (reflectedEndpoint level target) = target := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectedEndpoint_reflectedEndpoint level target

/--
[natCard_firstHitFamily_eq_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma natCard_firstHitFamily_eq_reflected_eq
  {start : Int × Int}
  {level : Int}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  Nat.card (FirstHitFamily start level walkLength target) = Nat.card (FirstHitFamily start level walkLength (reflectedEndpoint level target)) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.natCard_firstHitFamily_eq_reflected start level walkLength target

/--
[firstHitFamilyWeight_eq_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma firstHitFamilyWeight_eq_reflected_eq
  {start : Int × Int}
  {level : Int}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  firstHitFamilyWeight start level walkLength target = firstHitFamilyWeight start level walkLength (reflectedEndpoint level target) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.firstHitFamilyWeight_eq_reflected start level walkLength target

/--
[firstHitSplit_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma firstHitSplit_reflect_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
-- imply
  isingDiagonalWalkFirstHitSplit? start level w.reflect.steps = some w.reflect := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.firstHitSplit_reflect h

/--
[isingLeapfrogKilledKernel_eq_pathCount_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_eq_pathCount_div_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t p q = isingLeapfrogKilledPathCount R t p q / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_eq_pathCount_div R t p q

/--
[isingLeapfrogStoppedKernel_one_eq_pathCount_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_one_eq_pathCount_div_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R 1 p q = isingLeapfrogStoppedOneStepCount R p q / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_one_eq_pathCount_div R p q

/--
[isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div_eq
  {R t : Nat}
  {p r q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t p r * isingLeapfrogStoppedKernel R 1 r q = (isingLeapfrogKilledPathCount R t p r * isingLeapfrogStoppedOneStepCount R r q : Nat) / (4 : Real) ^ (t + 1) := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div R t p r q

/--
[isingLeapfrogBoxReflectX_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogBoxReflectX_involutive_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxReflectX R (isingLeapfrogBoxReflectX R p) = p := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxReflectX_involutive R p

/--
[isingLeapfrogBoxReflectX_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogBoxReflectX_eq_iff_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxReflectX R p = isingLeapfrogBoxReflectX R q ↔ p = q := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxReflectX_eq_iff R p q

/--
[isingLeapfrogBoxBoundary_reflectX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogBoxBoundary_reflectX_iff_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxBoundary R (isingLeapfrogBoxReflectX R p) ↔ isingLeapfrogBoxBoundary R p := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxBoundary_reflectX_iff R p

/--
[isingLeapfrogKilledPathCount_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogKilledPathCount_reflectX_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R q) = isingLeapfrogKilledPathCount R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledPathCount_reflectX R t p q

/--
[isingLeapfrogStoppedOneStepCount_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogStoppedOneStepCount_reflectX_eq
  {R : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R q) = isingLeapfrogStoppedOneStepCount R p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedOneStepCount_reflectX R p q

/--
[isingLeapfrogFirstHitFluxNumerator_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogFirstHitFluxNumerator_reflectX_eq
  {R t : Nat}
  {p r q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R r) * isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R r) (isingLeapfrogBoxReflectX R q) = isingLeapfrogKilledPathCount R t p r * isingLeapfrogStoppedOneStepCount R r q := by
-- proof
  apply StatMech.Universality.isingLeapfrogFirstHitFluxNumerator_reflectX R t p r q

/--
[isingLeapfrogFirstHitFluxSummand_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogFirstHitFluxSummand_reflectX_eq
  {R t : Nat}
  {p r q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R r) * isingLeapfrogStoppedKernel R 1 (isingLeapfrogBoxReflectX R r) (isingLeapfrogBoxReflectX R q) = isingLeapfrogKilledKernel R t p r * isingLeapfrogStoppedKernel R 1 r q := by
-- proof
  apply StatMech.Universality.isingLeapfrogFirstHitFluxSummand_reflectX R t p r q

/--
[isingLeapfrogStoppedKernel_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectX_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R t (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R q) = isingLeapfrogStoppedKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectX R t p q

/--
[isingLeapfrogExitKernel_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_reflectX_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogExitKernel R t (isingLeapfrogBoxReflectX R p) (isingLeapfrogBoxReflectX R q) = isingLeapfrogExitKernel R t p q := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_reflectX R t p q

/--
[isingLeapfrogDiagonalAdjacent_eq_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogDiagonalAdjacent_eq_neighbor_eq
  {R : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hp' : ¬ isingLeapfrogBoxBoundary R p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  p = isingLeapfrogSW R p' ∨ p = isingLeapfrogSE R p' hp' ∨ p = isingLeapfrogNW R p' hp' ∨ p = isingLeapfrogNE R p' hp' := by
-- proof
  apply StatMech.Universality.isingLeapfrogDiagonalAdjacent_eq_neighbor p p' hp' hpp'

/--
[isingLeapfrogExitKernel_neighbor_timeOffset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_neighbor_timeOffset_eq_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hp' : ¬ isingLeapfrogBoxBoundary R p') :
-- imply
  isingLeapfrogExitKernel R (t + 1) p' q - isingLeapfrogExitKernel R t p q = ((isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q - isingLeapfrogExitKernel R t p q) + (isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q - isingLeapfrogExitKernel R t p q) + (isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q - isingLeapfrogExitKernel R t p q) + (isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q - isingLeapfrogExitKernel R t p q)) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_neighbor_timeOffset_eq R t p p' q hp'

/--
[isingLeapfrogExitKernel_neighbor_timeOffset_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogExitKernel_neighbor_timeOffset_abs_le_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hp' : ¬ isingLeapfrogBoxBoundary R p') :
-- imply
  |isingLeapfrogExitKernel R (t + 1) p' q - isingLeapfrogExitKernel R t p q| ≤ (|isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q - isingLeapfrogExitKernel R t p q| + |isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q - isingLeapfrogExitKernel R t p q| + |isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q - isingLeapfrogExitKernel R t p q| + |isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q - isingLeapfrogExitKernel R t p q|) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogExitKernel_neighbor_timeOffset_abs_le R t p p' q hp'

/--
[isingLeapfrogStoppedKernel_neighbor_timeOffset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_neighbor_timeOffset_eq_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hp' : ¬ isingLeapfrogBoxBoundary R p') :
-- imply
  isingLeapfrogStoppedKernel R (t + 1) p' q - isingLeapfrogStoppedKernel R t p q = ((isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q - isingLeapfrogStoppedKernel R t p q) + (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q - isingLeapfrogStoppedKernel R t p q) + (isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q - isingLeapfrogStoppedKernel R t p q) + (isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q - isingLeapfrogStoppedKernel R t p q)) / 4 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_neighbor_timeOffset_eq R t p p' q hp'

/--
[reflectPrefix_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_before_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.before = w.before.map reflectIncrement := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_before w

/--
[reflectPrefix_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_after_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.after = w.after := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_after w

/--
[reflectPrefix_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_length_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.steps.length = w.steps.length := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_length w

/--
[reflectPrefix_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_valid_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (hw : w.Valid) :
-- imply
  w.reflectPrefix.Valid := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_valid w hw

/--
[reflectPrefix_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_firstHit_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
-- given
  (hw : w.FirstHit) :
-- imply
  w.reflectPrefix.FirstHit := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_firstHit w hw

/--
[reflectPrefix_endpoint_take_fst_of_le_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_endpoint_take_fst_of_le_before_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
  {k : Nat}
-- given
  (hk : k ≤ w.before.length) :
-- imply
  (isingDiagonalWalkEndpoint (reflectedEndpoint level start) (w.reflectPrefix.steps.take k)).1 = 2 * level - (isingDiagonalWalkEndpoint start (w.steps.take k)).1 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_endpoint_take_fst_of_le_before w k hk

/--
[reflectPrefix_endpoint_take_snd_of_le_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_endpoint_take_snd_of_le_before_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
  {k : Nat}
-- given
  (hk : k ≤ w.before.length) :
-- imply
  (isingDiagonalWalkEndpoint (reflectedEndpoint level start) (w.reflectPrefix.steps.take k)).2 = (isingDiagonalWalkEndpoint start (w.steps.take k)).2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_endpoint_take_snd_of_le_before w k hk

/--
[reflectPrefix_endpoint_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_endpoint_fst_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.endpoint.1 = w.endpoint.1 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_endpoint_fst w

/--
[reflectPrefix_endpoint_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_endpoint_snd_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.endpoint.2 = w.endpoint.2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_endpoint_snd w

/--
[reflectPrefix_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_endpoint_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  w.reflectPrefix.endpoint = w.endpoint := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_endpoint w

/--
[unreflectPrefix_reflectPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma unreflectPrefix_reflectPrefix_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level} :
-- imply
  unreflectPrefix w.reflectPrefix = w := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.unreflectPrefix_reflectPrefix w

/--
[reflectPrefix_unreflectPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma reflectPrefix_unreflectPrefix_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level} :
-- imply
  (unreflectPrefix w).reflectPrefix = w := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.reflectPrefix_unreflectPrefix w

/--
[natCard_firstHitFamily_eq_mirroredStart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma natCard_firstHitFamily_eq_mirroredStart_eq
  {start : Int × Int}
  {level : Int}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  Nat.card (FirstHitFamily start level walkLength target) = Nat.card (FirstHitFamily (reflectedEndpoint level start) level walkLength target) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.natCard_firstHitFamily_eq_mirroredStart start level walkLength target

/--
[survivalException_before_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma survivalException_before_firstHit_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
  {R : Nat}
-- given
  (hs : StaysInOpenBox R start w.steps)
  (hr : ¬ StaysInOpenBox R (reflectedEndpoint level start) w.reflectPrefix.steps) :
-- imply
  ∃ k, k < w.before.length ∧ k ≤ w.reflectPrefix.steps.length ∧ ¬ InOpenBox R (isingDiagonalWalkEndpoint (reflectedEndpoint level start) (w.reflectPrefix.steps.take k)) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalException_before_firstHit w hs hr

/--
[exists_prefix_fst_eq_of_lt_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma exists_prefix_fst_eq_of_lt_of_le_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
  {start : Int × Int}
  {level : Int}
-- given
  (hvalid : IsingDiagonalWalkStepsValid path)
  (hstart : start.1 < level)
  (hend : level ≤ (isingDiagonalWalkEndpoint start path).1) :
-- imply
  ∃ k, k ≤ path.length ∧ (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.exists_prefix_fst_eq_of_lt_of_le path start level hvalid hstart hend

/--
[exists_prefix_fst_eq_of_ge_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma exists_prefix_fst_eq_of_ge_of_gt_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
  {start : Int × Int}
  {level : Int}
-- given
  (hvalid : IsingDiagonalWalkStepsValid path)
  (hstart : level < start.1)
  (hend : (isingDiagonalWalkEndpoint start path).1 ≤ level) :
-- imply
  ∃ k, k ≤ path.length ∧ (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.exists_prefix_fst_eq_of_ge_of_gt path start level hvalid hstart hend

/--
[FirstHit.endpoint_take_fst_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma endpoint_take_fst_lt_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
  {k : Nat}
-- given
  (hfirst : w.FirstHit)
  (hvalid : w.Valid)
  (hstart : start.1 < level)
  (hk : k < w.before.length) :
-- imply
  (isingDiagonalWalkEndpoint start (w.before.take k)).1 < level := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.FirstHit.endpoint_take_fst_lt w hfirst hvalid hstart k hk

/--
[FirstHit.endpoint_take_fst_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma endpoint_take_fst_gt_eq
  {start : Int × Int}
  {level : Int}
  {w : IsingDiagonalWalkHitSplit start level}
  {k : Nat}
-- given
  (hfirst : w.FirstHit)
  (hvalid : w.Valid)
  (hstart : level < start.1)
  (hk : k < w.before.length) :
-- imply
  level < (isingDiagonalWalkEndpoint start (w.before.take k)).1 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.FirstHit.endpoint_take_fst_gt w hfirst hvalid hstart k hk

/--
[natCard_survivalMatchedFirstHitFamily_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean)
-/
@[path]
private lemma natCard_survivalMatchedFirstHitFamily_eq_eq
  {start : Int × Int}
  {level : Int}
  {R : Nat}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  Nat.card (SurvivalMatchedFirstHitFamily R start level walkLength target) = Nat.card (SurvivalMatchedMirrorFamily R start level walkLength target) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.natCard_survivalMatchedFirstHitFamily_eq R start level walkLength target


-- created on 2026-10-23
