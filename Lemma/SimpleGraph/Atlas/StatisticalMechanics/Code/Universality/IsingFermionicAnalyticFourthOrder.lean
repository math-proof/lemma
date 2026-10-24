import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicAnalyticFourthOrder
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[contDiffOn_complexLine_of_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma contDiffOn_complexLine_of_contDiffOn_eq
  {n : Nat}
  {U : Set Complex}
  {z d : Complex}
  {s : Set Real}
-- given
  (f : Complex -> Real)
  (hf : ContDiffOn Real n f U)
  (hline : Set.MapsTo (fun t : Real => z + (t : Complex) * d) s U) :
-- imply
  ContDiffOn Real n (fun t : Real => f (z + (t : Complex) * d)) s := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.contDiffOn_complexLine_of_contDiffOn n f U z d s hf hline

/--
[contDiffOn_im_of_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma contDiffOn_im_of_analyticOnNhd_eq
  {n : Nat}
  {U : Set Complex}
-- given
  (Phi : Complex -> Complex)
  (hPhi : AnalyticOnNhd Complex Phi U) :
-- imply
  ContDiffOn Real n (fun z => (Phi z).im) U := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.contDiffOn_im_of_analyticOnNhd n Phi U hPhi

/--
[exists_iteratedFDeriv_norm_bound_on_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma exists_iteratedFDeriv_norm_bound_on_compact_eq
  {U K : Set Complex}
-- given
  (Phi : Complex -> Complex)
  (hU : IsOpen U)
  (hK : IsCompact K)
  (hKU : K ⊆ U)
  (hPhi : AnalyticOnNhd Complex Phi U) :
-- imply
  exists M : NNReal, forall w, w ∈ K -> ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.exists_iteratedFDeriv_norm_bound_on_compact Phi U K hU hK hKU hPhi

/--
[complexLine_mapsTo_uIcc_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma complexLine_mapsTo_uIcc_of_convex_eq
  {U : Set Complex}
  {z d : Complex}
-- given
  (hU : Convex Real U)
  (h : Real)
  (hz : z ∈ U)
  (hend : z + (h : Complex) * d ∈ U) :
-- imply
  Set.MapsTo (fun t : Real => z + (t : Complex) * d) (Set.uIcc 0 h) U := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.complexLine_mapsTo_uIcc_of_convex U hU z d h hz hend

/--
[iteratedDeriv_complexLine_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma iteratedDeriv_complexLine_eq_eq
  {n : Nat}
  {z d : Complex}
  {t : Real}
-- given
  (f : Complex -> Real)
  (hf : ContDiff Real n f) :
-- imply
  iteratedDeriv n (fun s : Real => f (z + (s : Complex) * d)) t = iteratedFDeriv Real n f (z + (t : Complex) * d) (fun _ => d) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.iteratedDeriv_complexLine_eq n f z d t hf

/--
[iteratedDeriv_complexLine_eq_of_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma iteratedDeriv_complexLine_eq_of_contDiffOn_eq
  {n : Nat}
  {U : Set Complex}
  {z d : Complex}
  {t : Real}
-- given
  (f : Complex -> Real)
  (hU : IsOpen U)
  (hf : ContDiffOn Real n f U)
  (ht : z + (t : Complex) * d ∈ U) :
-- imply
  iteratedDeriv n (fun s : Real => f (z + (s : Complex) * d)) t = iteratedFDeriv Real n f (z + (t : Complex) * d) (fun _ => d) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.iteratedDeriv_complexLine_eq_of_contDiffOn n f U z d t hU hf ht

/--
[abs_iteratedDeriv_complexLine_four_le_tensorNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma abs_iteratedDeriv_complexLine_four_le_tensorNorm_eq
  {z d : Complex}
  {t M : Real}
-- given
  (f : Complex -> Real)
  (hf : ContDiff Real 4 f)
  (hbound : forall w, ‖iteratedFDeriv Real 4 f w‖ <= M) :
-- imply
  |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * d)) t| <= M * ‖d‖ ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.abs_iteratedDeriv_complexLine_four_le_tensorNorm f z d t M hf hbound

/--
[abs_iteratedDeriv_complexLine_four_le_tensorNormAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma abs_iteratedDeriv_complexLine_four_le_tensorNormAt_eq
  {U : Set Complex}
  {z d : Complex}
  {t M : Real}
-- given
  (f : Complex -> Real)
  (hU : IsOpen U)
  (hf : ContDiffOn Real 4 f U)
  (ht : z + (t : Complex) * d ∈ U)
  (hbound : ‖iteratedFDeriv Real 4 f (z + (t : Complex) * d)‖ <= M) :
-- imply
  |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * d)) t| <= M * ‖d‖ ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.abs_iteratedDeriv_complexLine_four_le_tensorNormAt f U z d t M hU hf ht hbound

/--
[abs_iteratedDeriv_complexLine_four_le_tensorNormOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma abs_iteratedDeriv_complexLine_four_le_tensorNormOn_eq
  {U : Set Complex}
  {z d : Complex}
  {t M : Real}
-- given
  (f : Complex -> Real)
  (hU : IsOpen U)
  (hf : ContDiffOn Real 4 f U)
  (ht : z + (t : Complex) * d ∈ U)
  (hbound : forall w, w ∈ U -> ‖iteratedFDeriv Real 4 f w‖ <= M) :
-- imply
  |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * d)) t| <= M * ‖d‖ ^ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.abs_iteratedDeriv_complexLine_four_le_tensorNormOn f U z d t M hU hf ht hbound

/--
[norm_one_add_I_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma norm_one_add_I_pow_four_eq :
-- imply
  ‖(1 + Complex.I : Complex)‖ ^ 4 = 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.norm_one_add_I_pow_four

/--
[norm_one_sub_I_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma norm_one_sub_I_pow_four_eq :
-- imply
  ‖(1 - Complex.I : Complex)‖ ^ 4 = 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.norm_one_sub_I_pow_four

/--
[iteratedDeriv_complexLine_two_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma iteratedDeriv_complexLine_two_eq_eq
  {z d : Complex}
-- given
  (f : Complex -> Real)
  (hf : ContDiffAt Real 2 f z) :
-- imply
  iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * d)) 0 = iteratedFDeriv Real 2 f z ![d, d] := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.iteratedDeriv_complexLine_two_eq f z d hf

/--
[harmonicAt_diagonal_iteratedDeriv_add_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma harmonicAt_diagonal_iteratedDeriv_add_eq_zero_eq
  {z : Complex}
-- given
  (f : Complex -> Real)
  (hharmonic : HarmonicAt f z) :
-- imply
  iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * (1 + Complex.I))) 0 + iteratedDeriv 2 (fun t : Real => f (z + (t : Complex) * (1 - Complex.I))) 0 = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.harmonicAt_diagonal_iteratedDeriv_add_eq_zero f z hharmonic

/--
[DirectionalFourthOrderHarmonicData.ofContDiffHarmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma ofContDiffHarmonic_eq
  {z : Complex}
  {boundOne boundTwo : Real}
-- given
  (f : Complex -> Real)
  (hf : ContDiff Real 4 f)
  (hfourthOne : forall t, |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * (1 + Complex.I))) t| <= boundOne)
  (hfourthTwo : forall t, |iteratedDeriv 4 (fun s : Real => f (z + (s : Complex) * (1 - Complex.I))) t| <= boundTwo)
  (hharmonic : HarmonicAt f z) :
-- imply
  DirectionalFourthOrderHarmonicData f z boundOne boundTwo where contDiffOne := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.DirectionalFourthOrderHarmonicData.ofContDiffHarmonic f z boundOne boundTwo hf hfourthOne hfourthTwo hharmonic

/--
[DirectionalFourthOrderHarmonicData.ofLineContDiffAnalyticIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma ofLineContDiffAnalyticIm_eq
  {z : Complex}
  {boundOne boundTwo : Real}
-- given
  (Phi : Complex -> Complex)
  (hcontOne : ContDiff Real 4 (fun t : Real => (Phi (z + (t : Complex) * (1 + Complex.I))).im))
  (hcontTwo : ContDiff Real 4 (fun t : Real => (Phi (z + (t : Complex) * (1 - Complex.I))).im))
  (hfourthOne : forall t, |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
  (hfourthTwo : forall t, |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
  (hanalytic : AnalyticAt Complex Phi z) :
-- imply
  DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z boundOne boundTwo where contDiffOne := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.DirectionalFourthOrderHarmonicData.ofLineContDiffAnalyticIm Phi z boundOne boundTwo hcontOne hcontTwo hfourthOne hfourthTwo hanalytic

/--
[DirectionalFourthOrderHarmonicData.ofContDiffAnalyticIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma ofContDiffAnalyticIm_eq
  {z : Complex}
  {boundOne boundTwo : Real}
-- given
  (Phi : Complex -> Complex)
  (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
  (hfourthOne : forall t, |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
  (hfourthTwo : forall t, |iteratedDeriv 4 (fun s : Real => (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
  (hanalytic : AnalyticAt Complex Phi z) :
-- imply
  DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z boundOne boundTwo := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.DirectionalFourthOrderHarmonicData.ofContDiffAnalyticIm Phi z boundOne boundTwo hsmooth hfourthOne hfourthTwo hanalytic

/--
[DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAnalyticFourthOrder.lean)
-/
@[path]
private lemma ofAnalyticTensorNorm_eq
  {z : Complex}
  {M : Real}
-- given
  (Phi : Complex -> Complex)
  (hsmooth : ContDiff Real 4 (fun w => (Phi w).im))
  (htensor : forall w, ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
  (hanalytic : AnalyticAt Complex Phi z) :
-- imply
  DirectionalFourthOrderHarmonicData (fun w => (Phi w).im) z (4 * M) (4 * M) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.DirectionalFourthOrderHarmonicData.ofAnalyticTensorNorm Phi z M hsmooth htensor hanalytic


-- created on 2026-10-23
