import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates
open StatMech StatMech.FrontierA


/--
[oddPrismLowerBlockSiteEquiv_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerBlockSiteEquiv_surface_eq
  {n : Nat}
  {i j : Fin (2 * n + 1)} :
-- imply
  oddPrismLowerBlockSiteEquiv n (oddPrismLowerHalfSurfaceSite n i j) = (i, j, Fin.last n) := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerBlockSiteEquiv_surface n i j

/--
[oddPrismUpperBlockReflectedSiteEquiv_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperBlockReflectedSiteEquiv_surface_eq
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismUpperBlockReflectedSiteEquiv n (oddPrismUpperHalfSurfaceSite n hn i j) = (i, j, oddPrismUpperSeamLayerIndex n hn) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperBlockReflectedSiteEquiv_surface n hn i j

/--
[spin_oddPrismLowerHalfSurfaceSite_eq_layer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_oddPrismLowerHalfSurfaceSite_eq_layer_eq
  {n : Nat}
  {sigma : ConfigSpace (OddPrismLowerBlockSite n)}
  {i j : Fin (2 * n + 1)} :
-- imply
  spin sigma (oddPrismLowerHalfSurfaceSite n i j) = spin (oddPrismLowerBlockLayer n sigma (Fin.last n)) (i, j) := by
-- proof
  apply StatMech.FrontierA.spin_oddPrismLowerHalfSurfaceSite_eq_layer n sigma i j

/--
[spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer_eq
  {n : Nat}
  {sigma : ConfigSpace (OddPrismUpperBlockSite n)}
  {i j : Fin (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) = spin (oddPrismUpperBlockReflectedLayer n sigma (oddPrismUpperSeamLayerIndex n hn)) (i, j) := by
-- proof
  apply StatMech.FrontierA.spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer n hn sigma i j

/--
[oddPrismUnequalBridgeInteraction_eq_layerDotProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeInteraction_eq_layerDotProduct_eq
  {n : Nat}
  {a : ConfigSpace (OddPrismLowerBlockSite n)}
  {b : ConfigSpace (OddPrismUpperBlockSite n)}
-- given
  (hn : 0 < n) :
-- imply
  unequalReplicaBridgeInteraction (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) a b = ∑ p : Fin (2 * n + 1) × Fin (2 * n + 1), spin (oddPrismLowerBlockLayer n a (Fin.last n)) p * spin (oddPrismUpperBlockReflectedLayer n b (oddPrismUpperSeamLayerIndex n hn)) p := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeInteraction_eq_layerDotProduct n hn a b

/--
[oddPrismLayerHalfWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerHalfWeight_pos_eq
  {beta : Real}
  {n : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismLayerHalfWeight beta n s := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerHalfWeight_pos beta n s

/--
[oddPrismLowerTransferTail_eq_mulVec_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerTransferTail_eq_mulVec_upper_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismLowerTransferTail beta n = rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ oddPrismUpperTransferTail beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerTransferTail_eq_mulVec_upper beta n hn

/--
[oddPrismLowerConditionedVector_eq_transfer_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerConditionedVector_eq_transfer_upper_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismLowerConditionedVector beta n = fun s => oddPrismLayerHalfWeight beta n s * (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ (fun q => oddPrismUpperConditionedVector beta n q / oddPrismLayerHalfWeight beta n q)) s := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerConditionedVector_eq_transfer_upper beta n hn

/--
[oddPrismPureSeamKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_pos_eq
  {r : Real}
  {n : Nat}
  {s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismPureSeamKernel r n s q := by
-- proof
  apply StatMech.FrontierA.oddPrismPureSeamKernel_pos r n s q

/--
[oddPrismTiltedSeamTransfer_eq_rectangularTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTiltedSeamTransfer_eq_rectangularTransfer_eq
  {beta : Real}
  {n : Nat} :
-- imply
  oddPrismTiltedSeamTransfer beta n beta = rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) := by
-- proof
  apply StatMech.FrontierA.oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n

/--
[oddPrismTiltedSeamTransfer_eq_transfer_mul_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTiltedSeamTransfer_eq_transfer_mul_exp_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismTiltedSeamTransfer beta n r s t = rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) s t * Real.exp ((r - beta) * oddPrismLayerSeamInteraction n s t) := by
-- proof
  apply StatMech.FrontierA.oddPrismTiltedSeamTransfer_eq_transfer_mul_exp beta n r s t

/--
[oddPrismTransferBridgeRawMoment_eq_tailContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_tailContraction_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = ∑ s, oddPrismLowerTransferTail beta n s * (oddPrismTiltedSeamTransfer beta n r *ᵥ oddPrismUpperTransferTail beta n) s := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_tailContraction beta n r

/--
[oddPrismTransferBridgeRawMoment_eq_oneStepContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_oneStepContraction_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = ∑ s, (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ oddPrismUpperTransferTail beta n) s * (oddPrismTiltedSeamTransfer beta n r *ᵥ oddPrismUpperTransferTail beta n) s := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_oneStepContraction beta n hn r

/--
[oddPrismLayerSeamInteraction_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_flip_right_eq
  {n : Nat}
  {s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismLayerSeamInteraction n s (FieldGhostDict.flipV q) = -oddPrismLayerSeamInteraction n s q := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_flip_right n s q

/--
[oddPrismPureSeamKernel_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_flip_right_eq
  {r : Real}
  {n : Nat}
  {s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismPureSeamKernel r n s (FieldGhostDict.flipV q) = oddPrismPureSeamKernel (-r) n s q := by
-- proof
  apply StatMech.FrontierA.oddPrismPureSeamKernel_flip_right r n s q

/--
[oddPrismTransferBridgeRawMoment_neg_eq_flipped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_neg_eq_flipped_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta n (-r) = oddPrismTransferBridgeFlippedRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_neg_eq_flipped beta n r

/--
[oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawFirst beta n (-r) = -oddPrismTransferBridgeFlippedRawFirst beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped beta n r

/--
[oddPrismTransferBridgeRawSecond_neg_eq_flipped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawSecond_neg_eq_flipped_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawSecond beta n (-r) = oddPrismTransferBridgeFlippedRawSecond beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawSecond_neg_eq_flipped beta n r

/--
[oddPrismTransferBridgeVariance_neg_eq_flipped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_neg_eq_flipped_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n (-r) = oddPrismTransferBridgeFlippedVariance beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_neg_eq_flipped beta n r

/--
[oddPrismGraphBridgeRawMoment_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawMoment_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  0 < oddPrismGraphBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawMoment_pos beta n r

/--
[oddPrismUnequalBridgeVariance_eq_graphRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVariance_eq_graphRaw_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  unequalReplicaBridgeVariance (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) r = oddPrismGraphBridgeRawSecond beta n r / oddPrismGraphBridgeRawMoment beta n r - (oddPrismGraphBridgeRawFirst beta n r / oddPrismGraphBridgeRawMoment beta n r) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVariance_eq_graphRaw beta n r

/--
[oddPrismGraphBridgeRawMoment_beta_eq_plusPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawMoment_beta_eq_plusPartition_eq
  {beta : Real}
  {n : Nat} :
-- imply
  oddPrismGraphBridgeRawMoment beta n beta = rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawMoment_beta_eq_plusPartition beta n

/--
[oddPrismTransferBridgeRawMoment_beta_eq_plusPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_beta_eq_plusPartition_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferBridgeRawMoment beta n beta = rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_beta_eq_plusPartition beta n hn

/--
[oddPrismGraphBridgeRawMoment_beta_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawMoment_beta_eq_transfer_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismGraphBridgeRawMoment beta n beta = oddPrismTransferBridgeRawMoment beta n beta := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawMoment_beta_eq_transfer beta n hn

/--
[spin_oddPrismBlockConfigEquiv_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_oddPrismBlockConfigEquiv_lower_eq
  {n : Nat}
  {a : ConfigSpace (OddPrismLowerBlockSite n)}
  {b : ConfigSpace (OddPrismUpperBlockSite n)}
  {v : OddPrismLowerBlockSite n} :
-- imply
  spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin a v := by
-- proof
  apply StatMech.FrontierA.spin_oddPrismBlockConfigEquiv_lower n a b v

/--
[spin_oddPrismBlockConfigEquiv_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_oddPrismBlockConfigEquiv_upper_eq
  {n : Nat}
  {a : ConfigSpace (OddPrismLowerBlockSite n)}
  {b : ConfigSpace (OddPrismUpperBlockSite n)}
  {v : OddPrismUpperBlockSite n} :
-- imply
  spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin b v := by
-- proof
  apply StatMech.FrontierA.spin_oddPrismBlockConfigEquiv_upper n a b v

/--
[oddPrismFullSeamInteraction_join](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullSeamInteraction_join_eq
  {n : Nat}
  {a : ConfigSpace (OddPrismLowerBlockSite n)}
  {b : ConfigSpace (OddPrismUpperBlockSite n)} :
-- imply
  oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n (a, b)) = unequalReplicaBridgeInteraction (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) a b := by
-- proof
  apply StatMech.FrontierA.oddPrismFullSeamInteraction_join n a b

/--
[oddPrismFullSeamInteraction_eq_rectangularInterface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullSeamInteraction_eq_rectangularInterface_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismFullSeamInteraction n sigma = rectangularPrismInterfaceInteraction sigma := by
-- proof
  apply StatMech.FrontierA.oddPrismFullSeamInteraction_eq_rectangularInterface n hn sigma

/--
[rectangularPrismInterfaceInteraction_eq_layerSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismInterfaceInteraction_eq_layerSeam_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  rectangularPrismInterfaceInteraction sigma = oddPrismLayerSeamInteraction n (rectangularPrismLayer sigma ⟨n, by omega⟩) (rectangularPrismLayer sigma ⟨n + 1, by omega⟩) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismInterfaceInteraction_eq_layerSeam n hn sigma

/--
[rectangularPrismLayer_splitConfig_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismLayer_splitConfig_lower_eq
  {n : Nat}
  {k : Fin (n + 1)}
-- given
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p) ⟨k.val, by omega⟩ = p.1 k := by
-- proof
  apply StatMech.FrontierA.rectangularPrismLayer_splitConfig_lower n p k

/--
[rectangularPrismLayer_splitConfig_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismLayer_splitConfig_upper_eq
  {n : Nat}
  {k : Fin n}
-- given
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p) ⟨2 * n - k.val, by omega⟩ = p.2 k := by
-- proof
  apply StatMech.FrontierA.rectangularPrismLayer_splitConfig_upper n p k

/--
[rectangularPrismLayer_positiveSplitConfig_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismLayer_positiveSplitConfig_lower_eq
  {n : Nat}
  {k : Fin (n + 1)}
-- given
  (hn : 0 < n)
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin (n - 1 + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) ⟨k.val, by omega⟩ = p.1 k := by
-- proof
  apply StatMech.FrontierA.rectangularPrismLayer_positiveSplitConfig_lower n hn p k

/--
[rectangularPrismLayer_positiveSplitConfig_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismLayer_positiveSplitConfig_upper_eq
  {n : Nat}
  {k : Fin (n - 1 + 1)}
-- given
  (hn : 0 < n)
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin (n - 1 + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) ⟨2 * n - k.val, by omega⟩ = p.2 k := by
-- proof
  apply StatMech.FrontierA.rectangularPrismLayer_positiveSplitConfig_upper n hn p k

/--
[oddPrismFullTiltedTransitionProduct_positiveSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedTransitionProduct_positiveSplit_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n)
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin (n - 1 + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  oddPrismFullTiltedTransitionProduct beta n r (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) = (∏ j : Fin n, rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (p.1 j.castSucc) (p.1 j.succ)) * oddPrismTiltedSeamTransfer beta n r (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1))) * ∏ j : Fin (n - 1), rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (p.2 j.castSucc) (p.2 j.succ) := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedTransitionProduct_positiveSplit beta n hn r p

/--
[oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismFullTiltedTransitionProduct beta n r sigma = (∏ z : Fin (2 * n), rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (rectangularPrismLayer sigma z.castSucc) (rectangularPrismLayer sigma z.succ)) * Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp beta n hn r sigma

/--
[oddPrismFullTiltedWeight_eq_pathWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedWeight_eq_pathWeight_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v) sigma * Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) = oddPrismFullTiltedPathWeight beta n r sigma := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedWeight_eq_pathWeight beta n hn r sigma

/--
[sum_transferTailPathWeight_mul_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_transferTailPathWeight_mul_endpoint_eq
  [Fintype E]
  [DecidableEq E]
  {A : Matrix E E Real}
  {k : Nat}
-- given
  (hA : A.IsHermitian)
  (a f : E -> Real) :
-- imply
  (∑ q : Fin (k + 1) -> E, transferTailPathWeight A a k q * f (q (Fin.last k))) = ∑ s, ((A ^ k) *ᵥ a) s * f s := by
-- proof
  apply StatMech.FrontierA.sum_transferTailPathWeight_mul_endpoint A hA a f k

/--
[oddPrismFullTiltedPathWeight_positiveSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedPathWeight_positiveSplit_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n)
  (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) × (Fin (n - 1 + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
-- imply
  oddPrismFullTiltedPathWeight beta n r (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) = oddPrismSplitPathWeight beta n r p := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedPathWeight_positiveSplit beta n hn r p

/--
[sum_oddPrismSplitPathWeight_eq_transferRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_oddPrismSplitPathWeight_eq_transferRawMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  (∑ p, oddPrismSplitPathWeight beta n r p) = oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismSplitPathWeight_eq_transferRawMoment beta n hn r

/--
[oddPrismFullTiltedRawMoment_eq_transferRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedRawMoment_eq_transferRawMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismFullTiltedRawMoment beta n r = oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedRawMoment_eq_transferRawMoment beta n hn r

/--
[oddPrismFullTiltedWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFullTiltedWeight_factor_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {a : ConfigSpace (OddPrismLowerBlockSite n)}
  {b : ConfigSpace (OddPrismUpperBlockSite n)} :
-- imply
  wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v) (oddPrismBlockConfigEquiv n (a, b)) * Real.exp ((r - beta) * oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n (a, b))) = wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) a * wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) b * Real.exp (r * unequalReplicaBridgeInteraction (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) a b) := by
-- proof
  apply StatMech.FrontierA.oddPrismFullTiltedWeight_factor beta n r a b

/--
[oddPrismGraphBridgeRawMoment_eq_fullTilted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawMoment_eq_fullTilted_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismGraphBridgeRawMoment beta n r = oddPrismFullTiltedRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawMoment_eq_fullTilted beta n r

/--
[oddPrismGraphBridgeRawMoment_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawMoment_eq_transfer_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismGraphBridgeRawMoment beta n r = oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawMoment_eq_transfer beta n hn r

/--
[hasDerivAt_weightedSeamExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_weightedSeamExp_eq
  {w I r : Real} :
-- imply
  HasDerivAt (fun t => w * Real.exp (t * I)) (w * (I * Real.exp (r * I))) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_weightedSeamExp w I r

/--
[hasDerivAt_weightedSeamFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_weightedSeamFirst_eq
  {w I r : Real} :
-- imply
  HasDerivAt (fun t => w * (I * Real.exp (t * I))) (w * (I ^ 2 * Real.exp (r * I))) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_weightedSeamFirst w I r

/--
[hasDerivAt_oddPrismTransferBridgeRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismTransferBridgeRawMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  HasDerivAt (oddPrismTransferBridgeRawMoment beta n) (oddPrismTransferBridgeRawFirst beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismTransferBridgeRawMoment beta n r

/--
[hasDerivAt_oddPrismTransferBridgeRawFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismTransferBridgeRawFirst_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  HasDerivAt (oddPrismTransferBridgeRawFirst beta n) (oddPrismTransferBridgeRawSecond beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismTransferBridgeRawFirst beta n r

/--
[hasDerivAt_oddPrismGraphBridgeRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismGraphBridgeRawMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  HasDerivAt (oddPrismGraphBridgeRawMoment beta n) (oddPrismGraphBridgeRawFirst beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismGraphBridgeRawMoment beta n r

/--
[hasDerivAt_oddPrismGraphBridgeRawFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismGraphBridgeRawFirst_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  HasDerivAt (oddPrismGraphBridgeRawFirst beta n) (oddPrismGraphBridgeRawSecond beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismGraphBridgeRawFirst beta n r

/--
[oddPrismGraphBridgeRawFirst_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawFirst_eq_transfer_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismGraphBridgeRawFirst beta n r = oddPrismTransferBridgeRawFirst beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawFirst_eq_transfer beta n hn r

/--
[oddPrismGraphBridgeRawSecond_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismGraphBridgeRawSecond_eq_transfer_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismGraphBridgeRawSecond beta n r = oddPrismTransferBridgeRawSecond beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismGraphBridgeRawSecond_eq_transfer beta n hn r

/--
[oddPrismUnequalBridgeVariance_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVariance_eq_transfer_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  unequalReplicaBridgeVariance (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) r = oddPrismTransferBridgeVariance beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVariance_eq_transfer beta n hn r

/--
[oddPrismTransferBridgeRawMoment_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  0 < oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_pos beta n hn r

/--
[oddPrismTransferBridgeVariance_eq_numerator_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_eq_numerator_div_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferBridgeVariance beta n r = oddPrismTransferBridgeVarianceNumerator beta n r / oddPrismTransferBridgeRawMoment beta n r ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_eq_numerator_div beta n hn r

/--
[hasDerivAt_oddPrismTransferBridgeLogRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismTransferBridgeLogRawMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  HasDerivAt (fun t => Real.log (oddPrismTransferBridgeRawMoment beta n t)) (oddPrismTransferBridgeRawFirst beta n r / oddPrismTransferBridgeRawMoment beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismTransferBridgeLogRawMoment beta n hn r

/--
[hasDerivAt_oddPrismTransferBridgeLogDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismTransferBridgeLogDerivative_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  HasDerivAt (fun t => oddPrismTransferBridgeRawFirst beta n t / oddPrismTransferBridgeRawMoment beta n t) (oddPrismTransferBridgeVariance beta n r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismTransferBridgeLogDerivative beta n hn r

/--
[oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferBridgeVariance beta n r <= oddPrismTransferBridgeVariance beta n (-r) ↔ oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos beta n hn r

/--
[two_mul_finiteExpVarianceNumerator_eq_pairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma two_mul_finiteExpVarianceNumerator_eq_pairSum_eq
  [Fintype E]
  {r : Real}
-- given
  (w I : E -> Real) :
-- imply
  2 * (finiteExpSecond w I r * finiteExpMoment w I r - finiteExpFirst w I r ^ 2) = ∑ x, ∑ y, w x * w y * ((I x - I y) ^ 2 * Real.exp (r * (I x + I y))) := by
-- proof
  apply StatMech.FrontierA.two_mul_finiteExpVarianceNumerator_eq_pairSum w I r

/--
[two_mul_finiteExpVarianceSkew_eq_fourStateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma two_mul_finiteExpVarianceSkew_eq_fourStateSum_eq
  [Fintype E]
  {r : Real}
-- given
  (w I : E -> Real) :
-- imply
  2 * finiteExpVarianceSkew w I r = ∑ x, ∑ y, ∑ z, ∑ q, w x * w y * w z * w q * (I x - I y) ^ 2 * (Real.exp (r * (I x + I y - I z - I q)) - Real.exp (-r * (I x + I y - I z - I q))) := by
-- proof
  apply StatMech.FrontierA.two_mul_finiteExpVarianceSkew_eq_fourStateSum w I r

/--
[oddPrismLowerConditionedVector_eq_threeLayerEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerConditionedVector_eq_threeLayerEndpoint_eq
  {beta : Real}
  {n : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismLowerConditionedVector beta n s = oddPrismLayerHalfWeight beta n s ^ 2 * ∑ v, oddPrismPureSeamKernel beta n s v * oddPrismUpperConditionedVector beta n v := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s

/--
[oddPrismThreeLayerWeight_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerWeight_swap_eq
  {beta : Real}
  {n : Nat}
  {a b : Real}
  {s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismThreeLayerWeight beta n a b s t v = oddPrismThreeLayerWeight beta n a b s v t * Real.exp ((a - b) * (oddPrismLayerSeamInteraction n s t - oddPrismLayerSeamInteraction n s v)) := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerWeight_swap beta n a b s v t

/--
[rectangularPrismTransfer_pow_mulVec_boundary_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismTransfer_pow_mulVec_boundary_pos_eq
  {beta : Real}
  {n k : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < ((rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ k) *ᵥ rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1)) s := by
-- proof
  apply StatMech.FrontierA.rectangularPrismTransfer_pow_mulVec_boundary_pos beta n k s

/--
[oddPrismUpperConditionedVector_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperConditionedVector_pos_eq
  {beta : Real}
  {n : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismUpperConditionedVector beta n s := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperConditionedVector_pos beta n s

/--
[oddPrismThreeLayerWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerWeight_pos_eq
  {beta : Real}
  {n : Nat}
  {a b : Real}
  {s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismThreeLayerWeight beta n a b s v t := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerWeight_pos beta n a b s v t

/--
[oddPrismThreeLayerWeight_le_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerWeight_le_swap_eq
  {beta : Real}
  {n : Nat}
  {a b : Real}
  {s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hba : b <= a)
  (hI : oddPrismLayerSeamInteraction n s v <= oddPrismLayerSeamInteraction n s t) :
-- imply
  oddPrismThreeLayerWeight beta n a b s v t <= oddPrismThreeLayerWeight beta n a b s t v := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerWeight_le_swap beta n hba s v t hI

/--
[oddPrismTransferBridgeRawMoment_eq_threeLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_threeLayer_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = oddPrismThreeLayerRawMoment beta n beta r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_threeLayer beta n hn r

/--
[oddPrismThreeLayerRawMoment_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerRawMoment_symm_eq
  {beta : Real}
  {n : Nat}
  {a b : Real} :
-- imply
  oddPrismThreeLayerRawMoment beta n a b = oddPrismThreeLayerRawMoment beta n b a := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerRawMoment_symm beta n a b

/--
[oddPrismThreeLayerMarkedRawMoment_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerMarkedRawMoment_swap_eq
  {beta : Real}
  {n : Nat}
  {a b : Real}
-- given
  (F : Real -> Real -> Real) :
-- imply
  oddPrismThreeLayerMarkedRawMoment beta n a b F = oddPrismThreeLayerMarkedRawMoment beta n b a (fun x y => F y x) := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerMarkedRawMoment_swap beta n a b F

/--
[oddPrismTransferBridgeRawMoment_eq_finiteExpMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_finiteExpMoment_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = finiteExpMoment (oddPrismTransferPairBaseWeight beta n) (oddPrismTransferPairInteraction n) r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_finiteExpMoment beta n r

/--
[oddPrismTransferBridgeRawFirst_eq_finiteExpFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawFirst_eq_finiteExpFirst_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawFirst beta n r = finiteExpFirst (oddPrismTransferPairBaseWeight beta n) (oddPrismTransferPairInteraction n) r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawFirst_eq_finiteExpFirst beta n r

/--
[oddPrismTransferBridgeRawSecond_eq_finiteExpSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawSecond_eq_finiteExpSecond_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawSecond beta n r = finiteExpSecond (oddPrismTransferPairBaseWeight beta n) (oddPrismTransferPairInteraction n) r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawSecond_eq_finiteExpSecond beta n r

/--
[oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVarianceSkewNumerator beta n r = finiteExpVarianceSkew (oddPrismTransferPairBaseWeight beta n) (oddPrismTransferPairInteraction n) r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp beta n r

/--
[two_mul_oddPrismTransferBridgeVarianceSkewNumerator_eq_fourStateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma two_mul_oddPrismTransferBridgeVarianceSkewNumerator_eq_fourStateSum_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  2 * oddPrismTransferBridgeVarianceSkewNumerator beta n r = let w := oddPrismTransferPairBaseWeight beta n let I := oddPrismTransferPairInteraction n ∑ x, ∑ y, ∑ z, ∑ q, w x * w y * w z * w q * (I x - I y) ^ 2 * (Real.exp (r * (I x + I y - I z - I q)) - Real.exp (-r * (I x + I y - I z - I q))) := by
-- proof
  apply StatMech.FrontierA.two_mul_oddPrismTransferBridgeVarianceSkewNumerator_eq_fourStateSum beta n r

/--
[finiteMarginal_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma finiteMarginal_logSupermodular_eq
  [Fintype A]
  [Fintype B]
  [DistribLattice A]
  [DistribLattice B]
  {x y : A}
-- given
  (F : A × B -> Real)
  (hF : 0 <= F)
  (hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y)) :
-- imply
  (∑ b, F (x, b)) * (∑ b, F (y, b)) <= (∑ b, F (x ⊓ y, b)) * (∑ b, F (x ⊔ y, b)) := by
-- proof
  apply StatMech.FrontierA.finiteMarginal_logSupermodular F hF hlog x y

/--
[rectangularLayerInternalInteraction_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerInternalInteraction_supermodular_eq
  {m n : Nat}
  {s t : RectangularLayerConfig m n} :
-- imply
  rectangularLayerInternalInteraction s + rectangularLayerInternalInteraction t <= rectangularLayerInternalInteraction (s ⊔ t) + rectangularLayerInternalInteraction (s ⊓ t) := by
-- proof
  apply StatMech.FrontierA.rectangularLayerInternalInteraction_supermodular s t

/--
[rectangularLayerBoundaryInteraction_modular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerBoundaryInteraction_modular_eq
  {m n : Nat}
  {s t : RectangularLayerConfig m n} :
-- imply
  (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin s p) + (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin t p) = (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (s ⊔ t) p) + ∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (s ⊓ t) p := by
-- proof
  apply StatMech.FrontierA.rectangularLayerBoundaryInteraction_modular s t

/--
[rectangularLayerBoltzmannInteraction_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerBoltzmannInteraction_supermodular_eq
  {beta : Real}
  {m n : Nat}
  {s t : RectangularLayerConfig m n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularLayerBoltzmannInteraction 1 beta s + rectangularLayerBoltzmannInteraction 1 beta t <= rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) + rectangularLayerBoltzmannInteraction 1 beta (s ⊓ t) := by
-- proof
  apply StatMech.FrontierA.rectangularLayerBoltzmannInteraction_supermodular hbeta s t

/--
[oddPrismLayerHalfWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerHalfWeight_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismLayerHalfWeight beta n s * oddPrismLayerHalfWeight beta n t <= oddPrismLayerHalfWeight beta n (s ⊔ t) * oddPrismLayerHalfWeight beta n (s ⊓ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerHalfWeight_logSupermodular hbeta n s t

/--
[oddPrismLayerSeamInteraction_pair_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_pair_supermodular_eq
  {n : Nat}
  {s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismLayerSeamInteraction n s v + oddPrismLayerSeamInteraction n t w <= oddPrismLayerSeamInteraction n (s ⊔ t) (v ⊔ w) + oddPrismLayerSeamInteraction n (s ⊓ t) (v ⊓ w) := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_pair_supermodular n s t v w

/--
[oddPrismPureSeamKernel_pair_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_pair_logSupermodular_eq
  {r : Real}
  {n : Nat}
  {s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hr : 0 <= r) :
-- imply
  oddPrismPureSeamKernel r n s v * oddPrismPureSeamKernel r n t w <= oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) * oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) := by
-- proof
  apply StatMech.FrontierA.oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w

/--
[oddPrismTiltedSeamTransfer_pair_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTiltedSeamTransfer_pair_logSupermodular_eq
  {beta r : Real}
  {n : Nat}
  {s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hr : 0 <= r) :
-- imply
  oddPrismTiltedSeamTransfer beta n r s v * oddPrismTiltedSeamTransfer beta n r t w <= oddPrismTiltedSeamTransfer beta n r (s ⊔ t) (v ⊔ w) * oddPrismTiltedSeamTransfer beta n r (s ⊓ t) (v ⊓ w) := by
-- proof
  apply StatMech.FrontierA.oddPrismTiltedSeamTransfer_pair_logSupermodular hbeta hr n s t v w

/--
[rectangularLayerFaceBoundary_modular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerFaceBoundary_modular_eq
  {beta : Real}
  {m n : Nat}
  {s t : RectangularLayerConfig m n} :
-- imply
  rectangularLayerFaceBoundary 1 beta s + rectangularLayerFaceBoundary 1 beta t = rectangularLayerFaceBoundary 1 beta (s ⊔ t) + rectangularLayerFaceBoundary 1 beta (s ⊓ t) := by
-- proof
  apply StatMech.FrontierA.rectangularLayerFaceBoundary_modular beta s t

/--
[rectangularPrismTransferBoundaryVector_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismTransferBoundaryVector_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) s * rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) t <= rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) (s ⊓ t) * rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismTransferBoundaryVector_logSupermodular hbeta n s t

/--
[transferTailPathWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma transferTailPathWeight_logSupermodular_eq
  [Fintype E]
  [DistribLattice E]
  {A : Matrix E E Real}
  {k : Nat}
-- given
  (a : E -> Real)
  (ha0 : 0 <= a)
  (hA0 : ∀ x y, 0 <= A x y)
  (ha : ∀ x y, a x * a y <= a (x ⊓ y) * a (x ⊔ y))
  (hA : ∀ x y u v, A x u * A y v <= A (x ⊓ y) (u ⊓ v) * A (x ⊔ y) (u ⊔ v))
  (q r : Fin (k + 1) -> E) :
-- imply
  transferTailPathWeight A a k q * transferTailPathWeight A a k r <= transferTailPathWeight A a k (q ⊓ r) * transferTailPathWeight A a k (q ⊔ r) := by
-- proof
  apply StatMech.FrontierA.transferTailPathWeight_logSupermodular A a ha0 hA0 ha hA k q r

/--
[sum_transferTailPathWeight_fixed_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_transferTailPathWeight_fixed_endpoint_eq
  [Fintype E]
  [DecidableEq E]
  {A : Matrix E E Real}
  {k : Nat}
  {s : E}
-- given
  (hA : A.IsHermitian)
  (a : E -> Real) :
-- imply
  (∑ q : Fin k -> E, transferTailPathWeight A a k (Fin.snoc q s)) = ((A ^ k) *ᵥ a) s := by
-- proof
  apply StatMech.FrontierA.sum_transferTailPathWeight_fixed_endpoint A hA a k s

/--
[oddPrismUpperSlabEndpointMarginal_eq_conditioned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabEndpointMarginal_eq_conditioned_eq
  {beta : Real}
  {n : Nat} :
-- imply
  oddPrismUpperSlabEndpointMarginal beta n (n - 1) = oddPrismUpperConditionedVector beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabEndpointMarginal_eq_conditioned beta n

/--
[oddPrismUpperSlabPathWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabPathWeight_logSupermodular_eq
  {beta : Real}
  {n k : Nat}
-- given
  (hbeta : 0 <= beta)
  (q r : Fin (k + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
-- imply
  oddPrismUpperSlabPathWeight beta n k q * oddPrismUpperSlabPathWeight beta n k r <= oddPrismUpperSlabPathWeight beta n k (q ⊓ r) * oddPrismUpperSlabPathWeight beta n k (q ⊔ r) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabPathWeight_logSupermodular hbeta n k q r

/--
[oddPrismUpperSlabEndpointMarginal_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabEndpointMarginal_logSupermodular_eq
  {beta : Real}
  {n k : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismUpperSlabEndpointMarginal beta n k s * oddPrismUpperSlabEndpointMarginal beta n k t <= oddPrismUpperSlabEndpointMarginal beta n k (s ⊓ t) * oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabEndpointMarginal_logSupermodular hbeta n k s t

/--
[oddPrismUpperConditionedVector_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperConditionedVector_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismUpperConditionedVector beta n s * oddPrismUpperConditionedVector beta n t <= oddPrismUpperConditionedVector beta n (s ⊓ t) * oddPrismUpperConditionedVector beta n (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperConditionedVector_logSupermodular hbeta n s t

/--
[oddPrismUpperOneStepMarginal_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperOneStepMarginal_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismUpperOneStepMarginal beta n s * oddPrismUpperOneStepMarginal beta n t <= oddPrismUpperOneStepMarginal beta n (s ⊓ t) * oddPrismUpperOneStepMarginal beta n (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperOneStepMarginal_logSupermodular hbeta n s t

/--
[oddPrismLowerConditionedVector_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerConditionedVector_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  oddPrismLowerConditionedVector beta n s * oddPrismLowerConditionedVector beta n t <= oddPrismLowerConditionedVector beta n (s ⊓ t) * oddPrismLowerConditionedVector beta n (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerConditionedVector_logSupermodular hbeta n hn s t

/--
[oddPrismTransferPairBaseWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferPairBaseWeight_logSupermodular_eq
  {beta : Real}
  {n : Nat}
  {x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  oddPrismTransferPairBaseWeight beta n x * oddPrismTransferPairBaseWeight beta n y <= oddPrismTransferPairBaseWeight beta n (x ⊓ y) * oddPrismTransferPairBaseWeight beta n (x ⊔ y) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferPairBaseWeight_logSupermodular hbeta n hn x y

/--
[oddPrismLowerConditionedVector_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLowerConditionedVector_pos_eq
  {beta : Real}
  {n : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismLowerConditionedVector beta n s := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerConditionedVector_pos beta n s

/--
[oddPrismTransferPairBaseWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferPairBaseWeight_pos_eq
  {beta : Real}
  {n : Nat}
  {x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismTransferPairBaseWeight beta n x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferPairBaseWeight_pos beta n x

/--
[oddPrismTransferTiltedPairWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairWeight_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismTransferTiltedPairWeight beta n r x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairWeight_pos beta n r x

/--
[oddPrismTransferTiltedPairWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairWeight_logSupermodular_eq
  {beta r : Real}
  {n : Nat}
  {x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hr : 0 <= r)
  (hn : 0 < n) :
-- imply
  oddPrismTransferTiltedPairWeight beta n r x * oddPrismTransferTiltedPairWeight beta n r y <= oddPrismTransferTiltedPairWeight beta n r (x ⊓ y) * oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairWeight_logSupermodular hbeta hr n hn x y

/--
[oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = ∑ x, oddPrismTransferTiltedPairWeight beta n r x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight beta n r

/--
[flipV_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma flipV_inf_eq
  {s t : ConfigSpace V} :
-- imply
  FieldGhostDict.flipV (s ⊓ t) = FieldGhostDict.flipV s ⊔ FieldGhostDict.flipV t := by
-- proof
  apply StatMech.FrontierA.flipV_inf s t

/--
[flipV_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma flipV_sup_eq
  {s t : ConfigSpace V} :
-- imply
  FieldGhostDict.flipV (s ⊔ t) = FieldGhostDict.flipV s ⊓ FieldGhostDict.flipV t := by
-- proof
  apply StatMech.FrontierA.flipV_sup s t

/--
[rectangularLayerInternalInteraction_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerInternalInteraction_flip_eq
  {m n : Nat}
  {s : RectangularLayerConfig m n} :
-- imply
  rectangularLayerInternalInteraction (FieldGhostDict.flipV s) = rectangularLayerInternalInteraction s := by
-- proof
  apply StatMech.FrontierA.rectangularLayerInternalInteraction_flip s

/--
[spin_neg_add_le_inf_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_neg_add_le_inf_sup_eq
  {s t : ConfigSpace V}
  {p : V} :
-- imply
  -spin s p + spin t p <= -spin (s ⊓ t) p + spin (s ⊔ t) p := by
-- proof
  apply StatMech.FrontierA.spin_neg_add_le_inf_sup s t p

/--
[rectangularLayerBoundaryInteraction_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerBoundaryInteraction_flip_eq
  {m n : Nat}
  {s : RectangularLayerConfig m n} :
-- imply
  (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (FieldGhostDict.flipV s) p) = -∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin s p := by
-- proof
  apply StatMech.FrontierA.rectangularLayerBoundaryInteraction_flip s

/--
[rectangularLayerBoundaryInteraction_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerBoundaryInteraction_cross_eq
  {m n : Nat}
  {s t : RectangularLayerConfig m n} :
-- imply
  -(∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin s p) + ∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin t p <= -(∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (s ⊓ t) p) + ∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (s ⊔ t) p := by
-- proof
  apply StatMech.FrontierA.rectangularLayerBoundaryInteraction_cross s t

/--
[rectangularLayerBoltzmannInteraction_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerBoltzmannInteraction_flip_cross_eq
  {beta : Real}
  {m n : Nat}
  {s t : RectangularLayerConfig m n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularLayerBoltzmannInteraction 1 beta (FieldGhostDict.flipV s) + rectangularLayerBoltzmannInteraction 1 beta t <= rectangularLayerBoltzmannInteraction 1 beta (FieldGhostDict.flipV (s ⊓ t)) + rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.rectangularLayerBoltzmannInteraction_flip_cross hbeta s t

/--
[oddPrismLayerHalfWeight_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerHalfWeight_flip_cross_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) * oddPrismLayerHalfWeight beta n t <= oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) * oddPrismLayerHalfWeight beta n (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerHalfWeight_flip_cross hbeta n s t

/--
[rectangularLayerFaceBoundary_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerFaceBoundary_flip_eq
  {beta : Real}
  {m n : Nat}
  {s : RectangularLayerConfig m n} :
-- imply
  rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) = -rectangularLayerFaceBoundary 1 beta s := by
-- proof
  apply StatMech.FrontierA.rectangularLayerFaceBoundary_flip beta s

/--
[rectangularLayerFaceBoundary_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularLayerFaceBoundary_flip_cross_eq
  {beta : Real}
  {m n : Nat}
  {s t : RectangularLayerConfig m n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) + rectangularLayerFaceBoundary 1 beta t <= rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV (s ⊓ t)) + rectangularLayerFaceBoundary 1 beta (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.rectangularLayerFaceBoundary_flip_cross hbeta s t

/--
[rectangularPrismTransferBoundaryVector_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismTransferBoundaryVector_flip_cross_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV s) * rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) t <= rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV (s ⊓ t)) * rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismTransferBoundaryVector_flip_cross hbeta n s t

/--
[oddPrismLayerSeamInteraction_flip_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_flip_both_eq
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismLayerSeamInteraction n (FieldGhostDict.flipV s) (FieldGhostDict.flipV t) = oddPrismLayerSeamInteraction n s t := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_flip_both n s t

/--
[oddPrismPureSeamKernel_flip_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_flip_both_eq
  {r : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismPureSeamKernel r n (FieldGhostDict.flipV s) (FieldGhostDict.flipV t) = oddPrismPureSeamKernel r n s t := by
-- proof
  apply StatMech.FrontierA.oddPrismPureSeamKernel_flip_both r n s t

/--
[oddPrismPureSeamKernel_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_flip_cross_eq
  {r : Real}
  {n : Nat}
  {s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hr : 0 <= r) :
-- imply
  oddPrismPureSeamKernel r n (FieldGhostDict.flipV s) (FieldGhostDict.flipV v) * oddPrismPureSeamKernel r n t w <= oddPrismPureSeamKernel r n (FieldGhostDict.flipV (s ⊓ t)) (FieldGhostDict.flipV (v ⊓ w)) * oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) := by
-- proof
  apply StatMech.FrontierA.oddPrismPureSeamKernel_flip_cross hr n s t v w

/--
[rectangularPrismTransfer_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma rectangularPrismTransfer_flip_cross_eq
  {beta : Real}
  {n : Nat}
  {s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV s) (FieldGhostDict.flipV v) * rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) t w <= rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV (s ⊓ t)) (FieldGhostDict.flipV (v ⊓ w)) * rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) (s ⊔ t) (v ⊔ w) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismTransfer_flip_cross hbeta n s t v w

/--
[finiteCrossMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma finiteCrossMarginal_eq
  [Fintype A]
  [Fintype B]
  [DistribLattice A]
  [DistribLattice B]
  {x y : A}
-- given
  (Fminus Fplus : A × B -> Real)
  (hminus : 0 <= Fminus)
  (hplus : 0 <= Fplus)
  (hcross : ∀ x y, Fminus x * Fplus y <= Fminus (x ⊓ y) * Fplus (x ⊔ y)) :
-- imply
  (∑ b, Fminus (x, b)) * (∑ b, Fplus (y, b)) <= (∑ b, Fminus (x ⊓ y, b)) * (∑ b, Fplus (x ⊔ y, b)) := by
-- proof
  apply StatMech.FrontierA.finiteCrossMarginal Fminus Fplus hminus hplus hcross x y

/--
[oddPrismFlipLayerPath_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFlipLayerPath_apply_eq
  {m n k : Nat}
  {j : Fin k}
-- given
  (q : Fin k -> RectangularLayerConfig m n) :
-- imply
  oddPrismFlipLayerPath q j = FieldGhostDict.flipV (q j) := by
-- proof
  apply StatMech.FrontierA.oddPrismFlipLayerPath_apply q j

/--
[oddPrismFlipLayerPath_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismFlipLayerPath_involutive_eq
  {m n k : Nat}
-- given
  (q : Fin k -> RectangularLayerConfig m n) :
-- imply
  oddPrismFlipLayerPath (oddPrismFlipLayerPath q) = q := by
-- proof
  apply StatMech.FrontierA.oddPrismFlipLayerPath_involutive q

/--
[transferTailPathWeight_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma transferTailPathWeight_flip_cross_eq
  [Fintype E]
  [DistribLattice E]
  {A : Matrix E E Real}
  {k : Nat}
-- given
  (flip : E -> E)
  (a : E -> Real)
  (ha0 : 0 <= a)
  (hA0 : ∀ x y, 0 <= A x y)
  (ha : ∀ x y, a (flip x) * a y <= a (flip (x ⊓ y)) * a (x ⊔ y))
  (hA : ∀ x y u v, A (flip x) (flip u) * A y v <= A (flip (x ⊓ y)) (flip (u ⊓ v)) * A (x ⊔ y) (u ⊔ v))
  (q r : Fin (k + 1) -> E) :
-- imply
  transferTailPathWeight A a k (fun j => flip (q j)) * transferTailPathWeight A a k r <= transferTailPathWeight A a k (fun j => flip ((q ⊓ r) j)) * transferTailPathWeight A a k (q ⊔ r) := by
-- proof
  apply StatMech.FrontierA.transferTailPathWeight_flip_cross flip A a ha0 hA0 ha hA k q r

/--
[oddPrismUpperSlabPathWeight_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabPathWeight_flip_cross_eq
  {beta : Real}
  {n k : Nat}
-- given
  (hbeta : 0 <= beta)
  (q r : Fin (k + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
-- imply
  oddPrismUpperSlabPathWeight beta n k (oddPrismFlipLayerPath q) * oddPrismUpperSlabPathWeight beta n k r <= oddPrismUpperSlabPathWeight beta n k (oddPrismFlipLayerPath (q ⊓ r)) * oddPrismUpperSlabPathWeight beta n k (q ⊔ r) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabPathWeight_flip_cross hbeta n k q r

/--
[oddPrismUpperSlabFlippedEndpointMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabFlippedEndpointMarginal_eq_eq
  {beta : Real}
  {n k : Nat}
  {s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismUpperSlabFlippedEndpointMarginal beta n k s = oddPrismUpperSlabEndpointMarginal beta n k (FieldGhostDict.flipV s) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabFlippedEndpointMarginal_eq beta n k s

/--
[oddPrismUpperSlabEndpointMarginal_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperSlabEndpointMarginal_flip_cross_eq
  {beta : Real}
  {n k : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismUpperSlabFlippedEndpointMarginal beta n k s * oddPrismUpperSlabEndpointMarginal beta n k t <= oddPrismUpperSlabFlippedEndpointMarginal beta n k (s ⊓ t) * oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperSlabEndpointMarginal_flip_cross hbeta n k s t

/--
[oddPrismUpperConditionedVector_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUpperConditionedVector_flip_cross_eq
  {beta : Real}
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV s) * oddPrismUpperConditionedVector beta n t <= oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (s ⊓ t)) * oddPrismUpperConditionedVector beta n (s ⊔ t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperConditionedVector_flip_cross hbeta n s t

/--
[oddPrismTransferFlippedTiltedPairWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferFlippedTiltedPairWeight_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  0 < oddPrismTransferFlippedTiltedPairWeight beta n r x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferFlippedTiltedPairWeight_pos beta n r x

/--
[oddPrismTransferTiltedPairWeight_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairWeight_flip_cross_eq
  {beta r : Real}
  {n : Nat}
  {x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hr : 0 <= r)
  (hn : 0 < n) :
-- imply
  oddPrismTransferFlippedTiltedPairWeight beta n r x * oddPrismTransferTiltedPairWeight beta n r y <= oddPrismTransferFlippedTiltedPairWeight beta n r (x ⊓ y) * oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairWeight_flip_cross hbeta hr n hn x y

/--
[oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeFlippedRawMoment beta n r = ∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight beta n r

/--
[oddPrismTransferBridgeFlippedRawMoment_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeFlippedRawMoment_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  0 < oddPrismTransferBridgeFlippedRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r

/--
[sum_oddPrismTransferTiltedPairProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_oddPrismTransferTiltedPairProb_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  (∑ x, oddPrismTransferTiltedPairProb beta n r x) = 1 := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismTransferTiltedPairProb beta n hn r

/--
[sum_oddPrismTransferFlippedTiltedPairProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_oddPrismTransferFlippedTiltedPairProb_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x) = 1 := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismTransferFlippedTiltedPairProb beta n hn r

/--
[oddPrismTransferTiltedPairProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairProb_nonneg_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  0 <= oddPrismTransferTiltedPairProb beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairProb_nonneg beta n hn r

/--
[oddPrismTransferFlippedTiltedPairProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferFlippedTiltedPairProb_nonneg_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  0 <= oddPrismTransferFlippedTiltedPairProb beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferFlippedTiltedPairProb_nonneg beta n hn r

/--
[oddPrismTransferTiltedPairProb_flip_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairProb_flip_cross_eq
  {beta r : Real}
  {n : Nat}
  {x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hr : 0 <= r)
  (hn : 0 < n) :
-- imply
  oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferTiltedPairProb beta n r y <= oddPrismTransferFlippedTiltedPairProb beta n r (x ⊓ y) * oddPrismTransferTiltedPairProb beta n r (x ⊔ y) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairProb_flip_cross hbeta hr n hn x y

/--
[oddPrismTransferFlippedTiltedPair_le_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferFlippedTiltedPair_le_of_monotone_eq
  {beta r : Real}
  {n : Nat}
  {g : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real}
-- given
  (hbeta : 0 <= beta)
  (hr : 0 <= r)
  (hn : 0 < n)
  (hg : Monotone g)
  (hg0 : 0 <= g) :
-- imply
  (∑ x, g x * oddPrismTransferFlippedTiltedPairProb beta n r x) <= ∑ x, g x * oddPrismTransferTiltedPairProb beta n r x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferFlippedTiltedPair_le_of_monotone hbeta hr n hn hg hg0

/--
[oddPrismTransferTiltedPairProb_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairProb_mean_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) = oddPrismTransferBridgeRawFirst beta n r / oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairProb_mean beta n r

/--
[oddPrismTransferTiltedPairProb_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferTiltedPairProb_second_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) = oddPrismTransferBridgeRawSecond beta n r / oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferTiltedPairProb_second beta n r

/--
[oddPrismTransferBridgeVariance_eq_pairProbVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_eq_pairProbVariance_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n r = (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) - (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_eq_pairProbVariance beta n r

/--
[oddPrismTransferFlippedTiltedPairProb_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferFlippedTiltedPairProb_mean_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) = oddPrismTransferBridgeFlippedRawFirst beta n r / oddPrismTransferBridgeFlippedRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferFlippedTiltedPairProb_mean beta n r

/--
[oddPrismTransferFlippedTiltedPairProb_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferFlippedTiltedPairProb_second_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) = oddPrismTransferBridgeFlippedRawSecond beta n r / oddPrismTransferBridgeFlippedRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferFlippedTiltedPairProb_second beta n r

/--
[oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeFlippedVariance beta n r = (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) - (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance beta n r

/--
[oddPrismTransferBridgeVariance_le_neg_iff_pairProbVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_le_neg_iff_pairProbVariance_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n r <= oddPrismTransferBridgeVariance beta n (-r) ↔ (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) - (∑ x, oddPrismTransferTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) ^ 2 <= (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x ^ 2) - (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x * oddPrismTransferPairInteraction n x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_le_neg_iff_pairProbVariance beta n r

/--
[oddPrismTransferPairInteraction_eq_sum_agreementSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferPairInteraction_eq_sum_agreementSpin_eq
  {n : Nat}
  {x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) × RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismTransferPairInteraction n x = ∑ p, oddPrismTransferPairAgreementSpin n p x := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferPairInteraction_eq_sum_agreementSpin n x

/--
[oddPrismTransferBridgeVariance_eq_sum_covarianceRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_eq_sum_covarianceRows_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n r = ∑ p, oddPrismTransferTiltedPairCovarianceRow beta n r p := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_eq_sum_covarianceRows beta n r

/--
[oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeFlippedVariance beta n r = ∑ p, oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows beta n r

/--
[oddPrismTransferBridgeVariance_le_neg_of_covarianceRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_le_neg_of_covarianceRows_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hrow : ∀ p, oddPrismTransferTiltedPairCovarianceRow beta n r p <= oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p) :
-- imply
  oddPrismTransferBridgeVariance beta n r <= oddPrismTransferBridgeVariance beta n (-r) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_le_neg_of_covarianceRows beta n r hrow

/--
[spin_ghsLAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma spin_ghsLAgreement_eq
  {s t : ConfigSpace V}
  {p : V} :
-- imply
  spin (ghsLAgreement s t) p = spin s p * spin t p := by
-- proof
  apply StatMech.FrontierA.spin_ghsLAgreement s t p

/--
[oddPrismLayerSeamInteraction_eq_agreementSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_eq_agreementSpin_eq
  {n : Nat}
  {s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismLayerSeamInteraction n s t = oddPrismTransferAgreementSpin n (ghsLAgreement s t) := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_eq_agreementSpin n s t

/--
[oddPrismLayerSeamInteraction_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_mate_eq
  {n : Nat}
  {q s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)} :
-- imply
  oddPrismLayerSeamInteraction n s (ghsLMate q s) = oddPrismTransferAgreementSpin n q := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_mate n q s

/--
[oddPrismTransferAgreementFibreMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementFibreMass_pos_eq
  {beta : Real}
  {n : Nat}
  {q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  0 < oddPrismTransferAgreementFibreMass beta n q := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementFibreMass_pos beta n q

/--
[oddPrismTransferBridgeRawMoment_eq_agreementTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_eq_agreementTilt_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta n r = ∑ q, oddPrismTransferAgreementFibreMass beta n q * Real.exp (r * oddPrismTransferAgreementSpin n q) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawMoment_eq_agreementTilt beta n r

/--
[oddPrismTransferBridgeRawFirst_eq_agreementTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawFirst_eq_agreementTilt_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawFirst beta n r = ∑ q, oddPrismTransferAgreementFibreMass beta n q * (oddPrismTransferAgreementSpin n q * Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawFirst_eq_agreementTilt beta n r

/--
[oddPrismTransferBridgeRawSecond_eq_agreementTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawSecond_eq_agreementTilt_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeRawSecond beta n r = ∑ q, oddPrismTransferAgreementFibreMass beta n q * (oddPrismTransferAgreementSpin n q ^ 2 * Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeRawSecond_eq_agreementTilt beta n r

/--
[oddPrismTransferAgreementTiltProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementTiltProb_pos_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
  {q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))}
-- given
  (hn : 0 < n) :
-- imply
  0 < oddPrismTransferAgreementTiltProb beta n r q := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementTiltProb_pos beta n hn r q

/--
[sum_oddPrismTransferAgreementTiltProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma sum_oddPrismTransferAgreementTiltProb_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n) :
-- imply
  (∑ q, oddPrismTransferAgreementTiltProb beta n r q) = 1 := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismTransferAgreementTiltProb beta n hn r

/--
[oddPrismTransferAgreementSpin_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementSpin_monotone_eq
  {n : Nat} :
-- imply
  Monotone (oddPrismTransferAgreementSpin n) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementSpin_monotone n

/--
[oddPrismTransferAgreementTiltProb_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementTiltProb_mean_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q) = oddPrismTransferBridgeRawFirst beta n r / oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementTiltProb_mean beta n r

/--
[oddPrismTransferAgreementTiltProb_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementTiltProb_second_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q ^ 2) = oddPrismTransferBridgeRawSecond beta n r / oddPrismTransferBridgeRawMoment beta n r := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementTiltProb_second beta n r

/--
[oddPrismTransferBridgeVariance_eq_agreementVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_eq_agreementVariance_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n r = (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q ^ 2) - (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_eq_agreementVariance beta n r

/--
[oddPrismTransferBridgeVariance_le_neg_iff_agreementVariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_le_neg_iff_agreementVariance_eq
  {beta : Real}
  {n : Nat}
  {r : Real} :
-- imply
  oddPrismTransferBridgeVariance beta n r <= oddPrismTransferBridgeVariance beta n (-r) ↔ (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q ^ 2) - (∑ q, oddPrismTransferAgreementTiltProb beta n r q * oddPrismTransferAgreementSpin n q) ^ 2 <= (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q * oddPrismTransferAgreementSpin n q ^ 2) - (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q * oddPrismTransferAgreementSpin n q) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_le_neg_iff_agreementVariance beta n r

/--
[ghsLMateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma ghsLMateEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  {s q : ConfigSpace V} :
-- imply
  ghsLMateEquiv s q = ghsLMate q s := by
-- proof
  apply StatMech.FrontierA.ghsLMateEquiv_apply s q

/--
[ghsLAgreement_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma ghsLAgreement_chain_eq
  {s t v : ConfigSpace V} :
-- imply
  ghsLAgreement (ghsLAgreement s t) (ghsLAgreement t v) = ghsLAgreement s v := by
-- proof
  apply StatMech.FrontierA.ghsLAgreement_chain s t v

/--
[oddPrismLayerSeamInteraction_mate_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismLayerSeamInteraction_mate_signed_eq
  {n : Nat}
  {c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  oddPrismLayerSeamInteraction n s (ghsLMate c t) = ∑ p, spin c p * (spin s p * spin t p) := by
-- proof
  apply StatMech.FrontierA.oddPrismLayerSeamInteraction_mate_signed n c s t

/--
[oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling_eq
  {n : Nat}
  {a b : Real}
  {c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  a * oddPrismLayerSeamInteraction n s (ghsLMate c t) + b * oddPrismLayerSeamInteraction n s t = ∑ p, (b + a * spin c p) * (spin s p * spin t p) := by
-- proof
  apply StatMech.FrontierA.oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling n a b c s t

/--
[oddPrism_endpointAgreementCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrism_endpointAgreementCoupling_nonneg_eq
  {beta r : Real}
  {n : Nat}
  {c : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))}
  {p : Fin (2 * n + 1) × Fin (2 * n + 1)}
-- given
  (hr : 0 <= r)
  (hrb : r <= beta) :
-- imply
  0 <= beta + r * spin c p := by
-- proof
  apply StatMech.FrontierA.oddPrism_endpointAgreementCoupling_nonneg hr hrb c p

/--
[oddPrismThreeLayerRawMoment_eq_endpointAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerRawMoment_eq_endpointAgreement_eq
  {beta : Real}
  {n : Nat}
  {a b : Real} :
-- imply
  oddPrismThreeLayerRawMoment beta n a b = oddPrismEndpointAgreementThreeLayerRawMoment beta n a b := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerRawMoment_eq_endpointAgreement beta n a b

/--
[oddPrismThreeLayerRawMoment_eq_gram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerRawMoment_eq_gram_eq
  {beta : Real}
  {n : Nat}
  {a b : Real} :
-- imply
  oddPrismThreeLayerRawMoment beta n a b = ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 * oddPrismThreeLayerEndpointSum beta n a s * oddPrismThreeLayerEndpointSum beta n b s := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerRawMoment_eq_gram beta n a b

/--
[oddPrismThreeLayerRawMoment_sq_le_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismThreeLayerRawMoment_sq_le_diagonal_eq
  {beta : Real}
  {n : Nat}
  {a b : Real} :
-- imply
  oddPrismThreeLayerRawMoment beta n a b ^ 2 <= oddPrismThreeLayerRawMoment beta n a a * oddPrismThreeLayerRawMoment beta n b b := by
-- proof
  apply StatMech.FrontierA.oddPrismThreeLayerRawMoment_sq_le_diagonal beta n a b

/--
[oddPrismAgreementEndpointKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_pos_eq
  {beta : Real}
  {n : Nat}
  {a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  0 < oddPrismAgreementEndpointKernel beta n a q := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_pos beta n a q

/--
[oddPrismAgreementEndpointKernel_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_symm_eq
  {beta : Real}
  {n : Nat}
  {a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  oddPrismAgreementEndpointKernel beta n a q = oddPrismAgreementEndpointKernel beta n q a := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_symm beta n a q

/--
[oddPrismAgreementEndpointKernel_quadratic_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_quadratic_eq_eq
  {beta : Real}
  {n : Nat}
-- given
  (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
-- imply
  (∑ a, ∑ q, f a * oddPrismAgreementEndpointKernel beta n a q * f q) = ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 * (∑ a, f a * oddPrismUpperConditionedVector beta n (ghsLMate a s)) ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_quadratic_eq beta n f

/--
[oddPrismAgreementEndpointKernel_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_quadratic_nonneg_eq
  {beta : Real}
  {n : Nat}
-- given
  (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
-- imply
  0 <= ∑ a, ∑ q, f a * oddPrismAgreementEndpointKernel beta n a q * f q := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_quadratic_nonneg beta n f

/--
[oddPrismTransferAgreementFibreMass_eq_kernelTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismTransferAgreementFibreMass_eq_kernelTilt_eq
  {beta : Real}
  {n : Nat}
  {q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismTransferAgreementFibreMass beta n q = ∑ a, oddPrismAgreementEndpointKernel beta n a q * Real.exp (beta * oddPrismTransferAgreementSpin n a) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferAgreementFibreMass_eq_kernelTilt beta n hn q

/--
[unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
  {r : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (hr : 0 <= r)
  (hvar : forall t, 0 <= t -> t <= r -> unequalReplicaBridgeVariance G H K J hf hg t <= unequalReplicaBridgeVariance G H K J hf hg (-t)) :
-- imply
  unequalReplicaBridgeFreeEnergy G H K J hf hg r <= 2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc G H K J hf hg r hr hvar

/--
[oddPrismUnequalBridgeFreeEnergy_le_of_transferVarianceOrder_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeFreeEnergy_le_of_transferVarianceOrder_Icc_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n)
  (hvar : forall t, 0 <= t -> t <= beta -> oddPrismTransferBridgeVariance beta n t <= oddPrismTransferBridgeVariance beta n (-t)) :
-- imply
  oddPrismUnequalBridgeFreeEnergy beta n <= 2 * beta * unequalReplicaBridgeMean (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeFreeEnergy_le_of_transferVarianceOrder_Icc beta hbeta n hn hvar


-- created on 2026-10-23
