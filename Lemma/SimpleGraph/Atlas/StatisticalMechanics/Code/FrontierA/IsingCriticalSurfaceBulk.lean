import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[translatedBox_subset_boxFinset_of_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma translatedBox_subset_boxFinset_of_margin_eq
  {d n r : Nat}
  {x : Site d}
-- given
  (hmargin : forall k, (x k).natAbs + r <= n) :
-- imply
  (boxFinset d r).image (fun y => Multiplicative.ofAdd x • y) <= boxFinset d n := by
-- proof
  apply StatMech.FrontierA.translatedBox_subset_boxFinset_of_margin x hmargin

/--
[oddPrismLowerHalfSurfaceSite_translatedBox_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismLowerHalfSurfaceSite_translatedBox_subset_eq
  {n r : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hiLower : r <= i.val)
  (hiUpper : i.val + r <= 2 * n)
  (hjLower : r <= j.val)
  (hjUpper : j.val + r <= 2 * n) :
-- imply
  (boxFinset 3 r).image (fun y => Multiplicative.ofAdd (rectangularPrismSiteEquivSctBoxDobrushin n (oddPrismLowerHalfSurfaceSite n i j).1).1 • y) <= boxFinset 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfSurfaceSite_translatedBox_subset n r i j hiLower hiUpper hjLower hjUpper

/--
[oddPrismPlusSpinMean_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismPlusSpinMean_nonneg_eq
  {beta : Real}
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  0 <= oddPrismPlusSpinMean beta n v := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusSpinMean_nonneg beta hbeta n v

/--
[oddPrismPlusSpinMean_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismPlusSpinMean_le_one_eq
  {beta : Real}
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  oddPrismPlusSpinMean beta n v <= 1 := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusSpinMean_le_one beta n v

/--
[isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap_eq
  {n r : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hiLower : r <= i.val)
  (hiUpper : i.val + r <= 2 * n)
  (hjLower : r <= j.val)
  (hjUpper : j.val + r <= 2 * n) :
-- imply
  oddPrismPlusSpinMean (Ising.betaC 3) n (oddPrismLowerHalfSurfaceSite n i j).1 <= (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} - (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} := by
-- proof
  apply StatMech.FrontierA.isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap n r i j hiLower hiUpper hjLower hjUpper

/--
[isingCritical_oddPrismPlusSurfaceSpinMean_tendsto_zero_of_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma isingCritical_oddPrismPlusSurfaceSpinMean_tendsto_zero_of_margin_eq
-- given
  (r : Nat -> Nat)
  (i j : (n : Nat) -> Fin (2 * n + 1))
  (hr : Tendsto r atTop atTop)
  (hiLower : forall n, r n <= (i n).val)
  (hiUpper : forall n, (i n).val + r n <= 2 * n)
  (hjLower : forall n, r n <= (j n).val)
  (hjUpper : forall n, (j n).val + r n <= 2 * n) :
-- imply
  Tendsto (fun n => oddPrismPlusSpinMean (Ising.betaC 3) n (oddPrismLowerHalfSurfaceSite n (i n) (j n)).1) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_oddPrismPlusSurfaceSpinMean_tendsto_zero_of_margin r i j hr hiLower hiUpper hjLower hjUpper

/--
[oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalSurfaceSpinSquareAverage atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero

/--
[replicaBridgeMoment_mul_partition_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma replicaBridgeMoment_mul_partition_sq_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMoment G J hf sites r * ZJ G.edgeFinset J hf ^ 2 = ∑ a : ConfigSpace V, ∑ b : ConfigSpace V, wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b * Real.exp (r * replicaBridgeInteraction sites a b) := by
-- proof
  apply StatMech.FrontierA.replicaBridgeMoment_mul_partition_sq G J hf sites r

/--
[oddPrismLowerHalfBridgeSiteMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismLowerHalfBridgeSiteMean_eq_eq
  {beta : Real}
  {n : Nat}
  {q : Fin (2 * n + 1) × Fin (2 * n + 1)} :
-- imply
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _ expJ (oddPrismLowerHalfGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun sigma => spin sigma (oddPrismLowerHalfBridgeSites n q)) = oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfBridgeSiteMean_eq beta n q

/--
[oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hvar : letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _ forall t, 0 <= t -> replicaBridgeVariance (oddPrismLowerHalfGraph n) (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (oddPrismLowerHalfBridgeSites n) t <= replicaBridgeVariance (oddPrismLowerHalfGraph n) (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (oddPrismLowerHalfBridgeSites n) (-t)) :
-- imply
  oddPrismLowerHalfBridgeFreeEnergy beta n <= 2 * beta * ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1), oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order beta hbeta n hvar

/--
[oddPrismLowerHalfSurfaceSpinMeanAt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismLowerHalfSurfaceSpinMeanAt_nonneg_eq
  {beta : Real}
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  0 <= oddPrismLowerHalfSurfaceSpinMeanAt beta n i j := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfSurfaceSpinMeanAt_nonneg beta hbeta n i j

/--
[oddPrismCriticalLowerHalfSpinSquareAverage_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinSquareAverage_le_plus_eq
  {n : Nat} :
-- imply
  oddPrismCriticalLowerHalfSpinSquareAverage n <= oddPrismCriticalSurfaceSpinSquareAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinSquareAverage_le_plus n

/--
[oddPrismCriticalLowerHalfSpinSquareAverage_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinSquareAverage_nonneg_eq
  {n : Nat} :
-- imply
  0 <= oddPrismCriticalLowerHalfSpinSquareAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinSquareAverage_nonneg n

/--
[oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalLowerHalfSpinSquareAverage atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero

/--
[unequalReplicaBridgeMoment_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeMoment_pos_eq
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
  (hg : W -> Real) :
-- imply
  0 < unequalReplicaBridgeMoment G H K J hf hg r := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMoment_pos G H K J hf hg r

/--
[wJ_crossInterface_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma wJ_crossInterface_factor_eq
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
  {a : ConfigSpace V}
  {b : ConfigSpace W}
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  wJ K.edgeFinset (fun _ => J) (Sum.elim hf hg) (isingSumConfigEquiv.symm (a, b)) = wJ G.edgeFinset (fun _ => J) hf a * wJ H.edgeFinset (fun _ => J) hg b * Real.exp (J * unequalReplicaBridgeInteraction G H K a b) := by
-- proof
  apply StatMech.FrontierA.wJ_crossInterface_factor G H K hcross J hf hg a b

/--
[ZJ_crossInterface_eq_mul_unequalMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma ZJ_crossInterface_eq_mul_unequalMoment_eq
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
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  ZJ K.edgeFinset (fun _ => J) (Sum.elim hf hg) = ZJ G.edgeFinset (fun _ => J) hf * ZJ H.edgeFinset (fun _ => J) hg * unequalReplicaBridgeMoment G H K J hf hg J := by
-- proof
  apply StatMech.FrontierA.ZJ_crossInterface_eq_mul_unequalMoment G H K hcross J hf hg

/--
[unequalReplicaBridgeInteraction_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeInteraction_flip_right_eq
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
  {a : ConfigSpace V}
  {b : ConfigSpace W}
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K) :
-- imply
  unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) = -unequalReplicaBridgeInteraction G H K a b := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeInteraction_flip_right G H K hcross a b

/--
[unequalReplicaExp2_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaExp2_neg_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (F : ConfigSpace V -> ConfigSpace W -> Real) :
-- imply
  unequalReplicaExp2 G H J hf hg (fun a b => -F a b) = -unequalReplicaExp2 G H J hf hg F := by
-- proof
  apply StatMech.FrontierA.unequalReplicaExp2_neg G H J hf hg F

/--
[unequalReplicaExp2_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaExp2_flip_right_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {J : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (F : ConfigSpace V -> ConfigSpace W -> Real) :
-- imply
  unequalReplicaExp2 G H J hf (fun x => -hg x) F = unequalReplicaExp2 G H J hf hg (fun a b => F a (FieldGhostDict.flipV b)) := by
-- proof
  apply StatMech.FrontierA.unequalReplicaExp2_flip_right G H J hf hg F

/--
[unequalReplicaBridgeMoment_neg_eq_negRightField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeMoment_neg_eq_negRightField_eq
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
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMoment G H K J hf hg (-r) = unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMoment_neg_eq_negRightField G H K hcross J hf hg r

/--
[unequalReplicaBridgeMean_neg_eq_negRightField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeMean_neg_eq_negRightField_eq
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
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMean G H K J hf hg (-r) = -unequalReplicaBridgeMean G H K J hf (fun x => -hg x) r := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMean_neg_eq_negRightField G H K hcross J hf hg r

/--
[unequalReplicaBridgeVariance_neg_eq_negRightField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeVariance_neg_eq_negRightField_eq
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
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeVariance G H K J hf hg (-r) = unequalReplicaBridgeVariance G H K J hf (fun x => -hg x) r := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeVariance_neg_eq_negRightField G H K hcross J hf hg r

/--
[ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg_eq
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
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  ZJ K.edgeFinset (fun _ => J) (Sum.elim hf (fun x => -hg x)) = ZJ G.edgeFinset (fun _ => J) hf * ZJ H.edgeFinset (fun _ => J) hg * unequalReplicaBridgeMoment G H K J hf hg (-J) := by
-- proof
  apply StatMech.FrontierA.ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg G H K hcross J hf hg

/--
[hasDerivAt_unequalReplicaBridgeMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_unequalReplicaBridgeMoment_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (unequalReplicaBridgeMoment G H K J hf hg) ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W, wJ G.edgeFinset (fun _ => J) hf a * wJ H.edgeFinset (fun _ => J) hg b * (unequalReplicaBridgeInteraction G H K a b * Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) / (ZJ G.edgeFinset (fun _ => J) hf * ZJ H.edgeFinset (fun _ => J) hg)) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_unequalReplicaBridgeMoment G H K J hf hg r

/--
[hasDerivAt_unequalReplicaBridgeWeightedMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_unequalReplicaBridgeWeightedMean_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (fun t => ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W, wJ G.edgeFinset (fun _ => J) hf a * wJ H.edgeFinset (fun _ => J) hg b * (unequalReplicaBridgeInteraction G H K a b * Real.exp (t * unequalReplicaBridgeInteraction G H K a b))) / (ZJ G.edgeFinset (fun _ => J) hf * ZJ H.edgeFinset (fun _ => J) hg))) ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W, wJ G.edgeFinset (fun _ => J) hf a * wJ H.edgeFinset (fun _ => J) hg b * (unequalReplicaBridgeInteraction G H K a b ^ 2 * Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) / (ZJ G.edgeFinset (fun _ => J) hf * ZJ H.edgeFinset (fun _ => J) hg)) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_unequalReplicaBridgeWeightedMean G H K J hf hg r

/--
[hasDerivAt_unequalReplicaBridgeMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_unequalReplicaBridgeMean_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (unequalReplicaBridgeMean G H K J hf hg) (unequalReplicaBridgeVariance G H K J hf hg r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_unequalReplicaBridgeMean G H K J hf hg r

/--
[hasDerivAt_log_unequalReplicaBridgeMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_log_unequalReplicaBridgeMoment_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (fun t => Real.log (unequalReplicaBridgeMoment G H K J hf hg t)) (unequalReplicaBridgeMean G H K J hf hg r) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_unequalReplicaBridgeMoment G H K J hf hg r

/--
[hasDerivAt_unequalReplicaBridgeFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_unequalReplicaBridgeFreeEnergy_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (unequalReplicaBridgeFreeEnergy G H K J hf hg) (unequalReplicaBridgeMean G H K J hf hg r + unequalReplicaBridgeMean G H K J hf hg (-r)) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_unequalReplicaBridgeFreeEnergy G H K J hf hg r

/--
[hasDerivAt_unequalReplicaBridgeSymmetricMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma hasDerivAt_unequalReplicaBridgeSymmetricMean_eq
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
  (hg : W -> Real) :
-- imply
  HasDerivAt (fun t => unequalReplicaBridgeMean G H K J hf hg t + unequalReplicaBridgeMean G H K J hf hg (-t)) (unequalReplicaBridgeVariance G H K J hf hg r - unequalReplicaBridgeVariance G H K J hf hg (-r)) r := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_unequalReplicaBridgeSymmetricMean G H K J hf hg r

/--
[unequalReplicaBridgeFreeEnergy_le_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma unequalReplicaBridgeFreeEnergy_le_of_variance_order_eq
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
  (hvar : forall t, 0 <= t -> unequalReplicaBridgeVariance G H K J hf hg t <= unequalReplicaBridgeVariance G H K J hf hg (-t)) :
-- imply
  unequalReplicaBridgeFreeEnergy G H K J hf hg r <= 2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeFreeEnergy_le_of_variance_order G H K J hf hg r hr hvar

/--
[oddPrismUnequalGlue_plus_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismUnequalGlue_plus_partition_eq
  {beta : Real}
  {n : Nat} :
-- imply
  ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta) (Sum.elim (fun v : OddPrismLowerBlockSite n => beta * oddPrismPlusField n v.1) (fun v : OddPrismUpperBlockSite n => beta * oddPrismPlusField n v.1)) = scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1) (oddPrismPlusField n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalGlue_plus_partition beta n

/--
[oddPrismUnequalGlue_dobrushin_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismUnequalGlue_dobrushin_partition_eq
  {beta : Real}
  {n : Nat} :
-- imply
  ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta) (Sum.elim (fun v : OddPrismLowerBlockSite n => beta * oddPrismPlusField n v.1) (fun v : OddPrismUpperBlockSite n => -(beta * oddPrismPlusField n v.1))) = scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1) (oddPrismDobrushinField n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalGlue_dobrushin_partition beta n

/--
[rectangularPrismPlusPartition_eq_unequalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_eq_unequalBridge_eq
  {beta : Real}
  {n : Nat} :
-- imply
  rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n = ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) * ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) * oddPrismUnequalBridgeMoment beta n beta := by
-- proof
  apply StatMech.FrontierA.rectangularPrismPlusPartition_eq_unequalBridge beta n

/--
[rectangularPrismDobrushinPartition_eq_unequalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma rectangularPrismDobrushinPartition_eq_unequalBridge_eq
  {beta : Real}
  {n : Nat} :
-- imply
  rectangularPrismDobrushinPartition 1 beta (2 * n + 1) (2 * n + 1) n = ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) * ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) * oddPrismUnequalBridgeMoment beta n (-beta) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismDobrushinPartition_eq_unequalBridge beta n

/--
[rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge_eq
  {beta : Real}
  {n : Nat} :
-- imply
  StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta (2 * n + 1) (2 * n + 1) n = oddPrismUnequalBridgeFreeEnergy beta n := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge beta n

/--
[standardCubicInterfaceDensity_eq_oddPrismUnequalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_eq_oddPrismUnequalBridge_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  standardCubicInterfaceDensity beta n = oddPrismUnequalBridgeFreeEnergy beta n / (((2 * n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_eq_oddPrismUnequalBridge beta n hn

/--
[oddPrismUnequalBridgeVarianceOrder_iff_crossField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVarianceOrder_iff_crossField_eq
  {beta : Real}
  {n : Nat} :
-- imply
  OddPrismUnequalBridgeVarianceOrder beta n <-> OddPrismUnequalBridgeCrossFieldVarianceOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVarianceOrder_iff_crossField beta n

/--
[oddPrismUnequalBridgeFreeEnergy_le_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeFreeEnergy_le_of_variance_order_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hvar : OddPrismUnequalBridgeVarianceOrder beta n) :
-- imply
  oddPrismUnequalBridgeFreeEnergy beta n <= 2 * beta * unequalReplicaBridgeMean (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeFreeEnergy_le_of_variance_order beta hbeta n hvar


-- created on 2026-10-23
