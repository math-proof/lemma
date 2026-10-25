import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCoefficientSemantics.Part2
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[weightedListEval_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_nil_eq
-- given
  (weight : Nat -> Real) :
-- imply
  weightedListEval weight [] = 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_nil weight

/--
[weightedListEval_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_cons_eq
  {coefficient : Int}
  {coefficients : List Int}
-- given
  (weight : Nat -> Real) :
-- imply
  weightedListEval weight (coefficient :: coefficients) = (coefficient : Real) * weight 0 + weightedListEval (fun i => weight (i + 1)) coefficients := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_cons weight coefficient coefficients

/--
[updateCoefficient_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma updateCoefficient_length_eq
  {coefficients : List Int}
  {i : Nat}
-- given
  (f : Int -> Int) :
-- imply
  (updateCoefficient coefficients i f).length = coefficients.length := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.updateCoefficient_length coefficients i f

/--
[weightedListEval_update_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_update_add_eq
  {coefficients : List Int}
  {i : Nat}
  {delta : Int}
-- given
  (weight : Nat -> Real)
  (hi : i < coefficients.length) :
-- imply
  weightedListEval weight (updateCoefficient coefficients i (fun c => c + delta)) = weightedListEval weight coefficients + (delta : Real) * weight i := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_update_add weight coefficients i delta hi

/--
[weightedListEval_foldl_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_foldl_update_eq
  {xs : List alpha}
  {coefficients : List Int}
-- given
  (weight : Nat -> Real)
  (index : alpha -> Nat)
  (delta : alpha -> Int)
  (hindex : ∀ x ∈ xs, index x < coefficients.length) :
-- imply
  weightedListEval weight (xs.foldl (fun out x => updateCoefficient out (index x) (fun c => c + delta x)) coefficients) = weightedListEval weight coefficients + (xs.map fun x => (delta x : Real) * weight (index x)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_foldl_update weight xs coefficients index delta hindex

/--
[weightedListEval_replicate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_replicate_zero_eq
  {n : Nat}
-- given
  (weight : Nat -> Real) :
-- imply
  weightedListEval weight (List.replicate n 0) = 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_replicate_zero weight n

/--
[weightedListEval_eq_sum_getD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_eq_sum_getD_eq
  {coefficients : List Int}
-- given
  (weight : Nat -> Real) :
-- imply
  weightedListEval weight coefficients = ∑ i ∈ Finset.range coefficients.length, (coefficients.getD i 0 : Real) * weight i := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_eq_sum_getD weight coefficients

/--
[foldl_length_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma foldl_length_of_step_eq
  {xs : List alpha}
  {coefficients : List Int}
-- given
  (step : List Int -> alpha -> List Int)
  (hstep : ∀ out x, (step out x).length = out.length) :
-- imply
  (xs.foldl step coefficients).length = coefficients.length := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.foldl_length_of_step xs step coefficients hstep

/--
[foldl_length_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma foldl_length_of_invariant_eq
  {xs : List alpha}
  {coefficients : List Int}
  {n : Nat}
-- given
  (step : List Int -> alpha -> List Int)
  (hlength : coefficients.length = n)
  (hstep : ∀ out x, out.length = n -> (step out x).length = n) :
-- imply
  (xs.foldl step coefficients).length = n := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.foldl_length_of_invariant xs step coefficients n hlength hstep

/--
[weightedListEval_foldl_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_foldl_additive_eq
  {xs : List alpha}
  {coefficients : List Int}
-- given
  (weight : Nat -> Real)
  (step : List Int -> alpha -> List Int)
  (contribution : alpha -> Real)
  (hstep : ∀ out x, weightedListEval weight (step out x) = weightedListEval weight out + contribution x) :
-- imply
  weightedListEval weight (xs.foldl step coefficients) = weightedListEval weight coefficients + (xs.map contribution).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_foldl_additive weight xs step contribution coefficients hstep

/--
[weightedListEval_foldl_additive_of_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_foldl_additive_of_length_eq
  {xs : List alpha}
  {coefficients : List Int}
  {n : Nat}
-- given
  (weight : Nat -> Real)
  (step : List Int -> alpha -> List Int)
  (contribution : alpha -> Real)
  (valid : alpha -> Prop)
  (hlength : coefficients.length = n)
  (hvalid : ∀ x ∈ xs, valid x)
  (hstepLength : ∀ out x, out.length = n -> (step out x).length = n)
  (hstepEval : ∀ out x, valid x -> out.length = n -> weightedListEval weight (step out x) = weightedListEval weight out + contribution x) :
-- imply
  weightedListEval weight (xs.foldl step coefficients) = weightedListEval weight coefficients + (xs.map contribution).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_foldl_additive_of_length weight xs step contribution valid coefficients n hlength hvalid hstepLength hstepEval

/--
[weightedListEval_eq_list_sum_getD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_eq_list_sum_getD_eq
  {coefficients : List Int}
-- given
  (weight : Nat -> Real) :
-- imply
  weightedListEval weight coefficients = ((List.range coefficients.length).map fun i => (coefficients.getD i 0 : Real) * weight i).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_eq_list_sum_getD weight coefficients

/--
[weightedListEval_addCoefficientLists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_addCoefficientLists_eq
  {left right : List Int}
-- given
  (weight : Nat -> Real)
  (hlength : left.length = right.length) :
-- imply
  weightedListEval weight (addCoefficientLists left right) = weightedListEval weight left + weightedListEval weight right := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_addCoefficientLists weight left right hlength

/--
[addCoefficientLists_length_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma addCoefficientLists_length_of_eq_eq
  {left right : List Int}
-- given
  (hlength : left.length = right.length) :
-- imply
  (addCoefficientLists left right).length = left.length := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.addCoefficientLists_length_of_eq left right hlength

/--
[rawMomentStateCoefficientList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentStateCoefficientList_length_eq
  {s : Nat} :
-- imply
  (rawMomentStateCoefficientList s).length = 800 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentStateCoefficientList_length s

/--
[rawMomentVIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentVIndex_lt_eq
  {s v : Nat} :
-- imply
  Int.toNat (halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) < 35 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentVIndex_lt s v

/--
[rawMomentQEndpointIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentQEndpointIndex_lt_eq
  {q : Nat} :
-- imply
  Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) < 26 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentQEndpointIndex_lt q

/--
[rawMomentQInteractionIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentQInteractionIndex_lt_eq
  {s q : Nat} :
-- imply
  Int.toNat (halfShift (layerDotInt s q) 9) < 10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentQInteractionIndex_lt s q

/--
[rawMomentQIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentQIndex_lt_eq
  {s q : Nat} :
-- imply
  10 * Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) + Int.toNat (halfShift (layerDotInt s q) 9) < 260 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentQIndex_lt s q

/--
[rawMomentStateIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentStateIndex_lt_eq
  {s ev eq iq : Nat}
-- given
  (hev : ev < 35)
  (heq : eq < 26)
  (hiq : iq < 10) :
-- imply
  10 * (Int.toNat (halfShift (layerLateralInt s) 16) + ev + eq) + iq < 800 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentStateIndex_lt s ev eq iq hev heq hiq

/--
[rawMomentStateExponentIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentStateExponentIndex_lt_eq
  {s : Nat} :
-- imply
  Int.toNat (halfShift (layerLateralInt s) 16) < 21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentStateExponentIndex_lt s

/--
[rawMomentVCounts_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentVCounts_length_eq
  {s : Nat} :
-- imply
  (rawMomentVCounts s).length = 35 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentVCounts_length s

/--
[rawMomentQCounts_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentQCounts_length_eq
  {s : Nat} :
-- imply
  (rawMomentQCounts s).length = 260 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentQCounts_length s

/--
[weightedListEval_rawMomentVCounts_eq_getD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentVCounts_eq_getD_eq
  {X : Real}
  {s : Nat} :
-- imply
  weightedListEval (fun ev => X ^ (ev : Int)) (rawMomentVCounts s) = ((List.range 35).map fun ev => (rawMomentVCounts s |>.getD ev 0 : Real) * X ^ (ev : Int)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentVCounts_eq_getD X s

/--
[weightedListEval_rawMomentQCounts_eq_getD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentQCounts_eq_getD_eq
  {X Y : Real}
  {s : Nat} :
-- imply
  weightedListEval (denseMomentWeight X Y) (rawMomentQCounts s) = ((List.range 26).map fun eq => ((List.range 10).map fun iq => (rawMomentQCounts s |>.getD (10 * eq + iq) 0 : Real) * X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentQCounts_eq_getD X Y s

/--
[weightedListEval_addRawMomentState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_addRawMomentState_eq
  {X Y : Real}
  {out : List Int}
  {s : Nat}
-- given
  (hX : X ≠ 0)
  (hlength : out.length = 800) :
-- imply
  weightedListEval (denseMomentWeight X Y) (addRawMomentState out s) = weightedListEval (denseMomentWeight X Y) out + X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) * weightedListEval (fun ev => X ^ (ev : Int)) (rawMomentVCounts s) * weightedListEval (denseMomentWeight X Y) (rawMomentQCounts s) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_addRawMomentState X Y hX out s hlength

/--
[weightedListEval_rawMomentVCounts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentVCounts_eq
  {X : Real}
  {s : Nat} :
-- imply
  weightedListEval (fun ev => X ^ (ev : Int)) (rawMomentVCounts s) = ((List.range 512).map fun v => X ^ (Int.toNat (halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) : Int)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentVCounts X s

/--
[weightedListEval_rawMomentQCounts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentQCounts_eq
  {X Y : Real}
  {s : Nat} :
-- imply
  weightedListEval (fun index => X ^ ((index / 10 : Nat) : Int) * Y ^ ((index % 10 : Nat) : Int)) (rawMomentQCounts s) = ((List.range 512).map fun q => X ^ (Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) * Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentQCounts X Y s

/--
[weightedListEval_rawMomentStateCoefficientList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentStateCoefficientList_eq
  {X Y : Real}
  {s : Nat}
-- given
  (hX : X ≠ 0) :
-- imply
  weightedListEval (denseMomentWeight X Y) (rawMomentStateCoefficientList s) = X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) * ((List.range 512).map fun v => X ^ (Int.toNat (halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) : Int)).sum * ((List.range 512).map fun q => X ^ (Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) * Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentStateCoefficientList X Y hX s

/--
[rawMomentCoefficientSmallList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentCoefficientSmallList_length_eq
  {start count : Nat} :
-- imply
  (rawMomentCoefficientSmallList start count).length = 800 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentCoefficientSmallList_length start count

/--
[weightedListEval_rawMomentCoefficientSmallList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentCoefficientSmallList_eq
  {X Y : Real}
  {start count : Nat} :
-- imply
  weightedListEval (denseMomentWeight X Y) (rawMomentCoefficientSmallList start count) = ((List.range count).map fun offset => weightedListEval (denseMomentWeight X Y) (rawMomentStateCoefficientList (start + offset))).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentCoefficientSmallList X Y start count

/--
[rawMomentCoefficientBlockList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentCoefficientBlockList_length_eq
  {start count : Nat} :
-- imply
  (rawMomentCoefficientBlockList start count).length = 800 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentCoefficientBlockList_length start count

/--
[weightedListEval_rawMomentCoefficientBlockList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentCoefficientBlockList_eq
  {X Y : Real}
  {start count : Nat} :
-- imply
  weightedListEval (denseMomentWeight X Y) (rawMomentCoefficientBlockList start count) = ((List.range count).map fun offset => weightedListEval (denseMomentWeight X Y) (rawMomentStateCoefficientList (start + offset))).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentCoefficientBlockList X Y start count

/--
[rawMomentCoefficientList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma rawMomentCoefficientList_length_eq :
-- imply
  rawMomentCoefficientList.length = 800 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rawMomentCoefficientList_length

/--
[weightedListEval_rawMomentCoefficientList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentCoefficientList_eq
  {X Y : Real} :
-- imply
  weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList = ((List.range 512).map fun s => weightedListEval (denseMomentWeight X Y) (rawMomentStateCoefficientList s)).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentCoefficientList X Y

/--
[weightedListEval_rawMomentCoefficientList_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_rawMomentCoefficientList_stateSum_eq
  {X Y : Real}
-- given
  (hX : X ≠ 0) :
-- imply
  weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList = ((List.range 512).map fun s => X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) * ((List.range 512).map fun v => X ^ (Int.toNat (halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) : Int)).sum * ((List.range 512).map fun q => X ^ (Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) * Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_rawMomentCoefficientList_stateSum X Y hX

/--
[weightedListEval_denseMomentWeight_eq_grid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma weightedListEval_denseMomentWeight_eq_grid_eq
  {X Y : Real}
  {coefficients : List Int}
-- given
  (hlength : coefficients.length = 800) :
-- imply
  weightedListEval (denseMomentWeight X Y) coefficients = ((List.range 80).map fun ex => ((List.range 10).map fun ey => (coefficients.getD (10 * ex + ey) 0 : Real) * X ^ (ex : Int) * Y ^ (ey : Int)).sum).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.weightedListEval_denseMomentWeight_eq_grid X Y coefficients hlength

/--
[BiPoly.eval_rawMomentPolyOfCoefficientList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma eval_rawMomentPolyOfCoefficientList_eq
  {X Y : Real}
  {coefficients : List Int}
-- given
  (hlength : coefficients.length = 800) :
-- imply
  (rawMomentPolyOfCoefficientList coefficients).eval X Y = weightedListEval (denseMomentWeight X Y) coefficients := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_rawMomentPolyOfCoefficientList X Y coefficients hlength

/--
[BiPoly.eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean)
-/
@[path]
private lemma eval_rawMomentPoly_eq
  {X Y : Real} :
-- imply
  rawMomentPoly.eval X Y = weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_rawMomentPoly X Y


-- created on 2026-10-23
