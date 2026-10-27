import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.setConnectionWithin_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma setConnectionWithin_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A S T : Set V} :
-- imply
  P.configTranslate z omega ∈ P.setConnectionWithin (P.shift z '' A) (P.shift z '' S) (P.shift z '' T) ↔ omega ∈ P.setConnectionWithin A S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_configTranslate P z omega A S T

/--
[PeriodicGraph.setConnectionWithin_mono_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma setConnectionWithin_mono_target_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S : Set V}
  {T U : Set V}
-- given
  (hTU : T ⊆ U) :
-- imply
  P.setConnectionWithin A S T ⊆ P.setConnectionWithin A S U := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_mono_target P A S hTU

/--
[verticalShift_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma verticalShift_zero_apply_eq
  [DecidableEq V]
  [Countable V]
  {t : Int} :
-- imply
  verticalShift t 0 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.verticalShift_zero_apply t

/--
[verticalShift_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma verticalShift_one_apply_eq
  [DecidableEq V]
  [Countable V]
  {t : Int} :
-- imply
  verticalShift t 1 = t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.verticalShift_one_apply t

/--
[PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_mem_rightHalfPlaneVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r : Real}
  {x : V} :
-- imply
  P.shift (verticalShift t) x ∈ E.rightHalfPlaneVertices r ↔ x ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneVertices_vertical E t r x

/--
[PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_image_rightHalfPlaneVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r : Real} :
-- imply
  P.shift (verticalShift t) '' E.rightHalfPlaneVertices r = E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices_vertical E t r

/--
[PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneBoundaryVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_mem_rightHalfPlaneBoundaryVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r : Real}
  {x : V} :
-- imply
  P.shift (verticalShift t) x ∈ E.rightHalfPlaneBoundaryVertices r ↔ x ∈ E.rightHalfPlaneBoundaryVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneBoundaryVertices_vertical E t r x

/--
[PeriodicPlaneEmbedding.shift_image_rightHalfPlaneBoundaryVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_image_rightHalfPlaneBoundaryVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r : Real} :
-- imply
  P.shift (verticalShift t) '' E.rightHalfPlaneBoundaryVertices r = E.rightHalfPlaneBoundaryVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rightHalfPlaneBoundaryVertices_vertical E t r

/--
[PeriodicPlaneEmbedding.shift_image_lowerBoundaryRayVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_image_lowerBoundaryRayVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r s : Real} :
-- imply
  P.shift (verticalShift t) '' E.lowerBoundaryRayVertices r s = E.lowerBoundaryRayVertices r (s + t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_lowerBoundaryRayVertices_vertical E t r s

/--
[PeriodicPlaneEmbedding.shift_image_upperBoundaryRayVertices_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_image_upperBoundaryRayVertices_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {t : Int}
  {r s : Real} :
-- imply
  P.shift (verticalShift t) '' E.upperBoundaryRayVertices r s = E.upperBoundaryRayVertices r (s + t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_upperBoundaryRayVertices_vertical E t r s

/--
[PeriodicPlaneEmbedding.lowerBoundaryRay_connection_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma lowerBoundaryRay_connection_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.lowerBoundaryRay_connection_mono E r S

/--
[PeriodicPlaneEmbedding.iUnion_lowerBoundaryRay_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma iUnion_lowerBoundaryRay_connection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n)) = P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_lowerBoundaryRay_connection E r S

/--
[PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma lowerBoundaryRay_connection_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r n))) atTop (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_tendsto E mu r S

/--
[PeriodicPlaneEmbedding.upperBoundaryRay_connection_mono_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma upperBoundaryRay_connection_mono_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  Monotone (fun n : Nat => P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.upperBoundaryRay_connection_mono_neg E r S

/--
[PeriodicPlaneEmbedding.iUnion_upperBoundaryRay_connection_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma iUnion_upperBoundaryRay_connection_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S : Set V} :
-- imply
  (⋃ n : Nat, P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real)))) = P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_upperBoundaryRay_connection_neg E r S

/--
[PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_tendsto_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma upperBoundaryRay_connection_measureReal_tendsto_neg_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r (-(n : Real))))) atTop (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_tendsto_neg E mu r S

/--
[PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma lowerBoundaryRay_connection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S) (E.lowerBoundaryRayVertices r (s + t))) = mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma upperBoundaryRay_connection_measureReal_vertical_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {t : Int}
  {r s : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S) (E.upperBoundaryRayVertices r (s + t))) = mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_vertical E mu hTI t r s S

/--
[PeriodicPlaneEmbedding.shift_down_lowerBoundaryRay_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_down_lowerBoundaryRay_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (-(n : Int))) '' S) (E.lowerBoundaryRayVertices r 0))) atTop (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_down_lowerBoundaryRay_measureReal_tendsto E mu hTI r S

/--
[PeriodicPlaneEmbedding.shift_up_upperBoundaryRay_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean)
-/
@[path]
private lemma shift_up_upperBoundaryRay_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  Tendsto (fun n : Nat => mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (P.shift (verticalShift (n : Int)) '' S) (E.upperBoundaryRayVertices r 0))) atTop (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_up_upperBoundaryRay_measureReal_tendsto E mu hTI r S


-- created on 2026-10-23
