import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[varyingFiniteGibbs_tendsto_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma varyingFiniteGibbs_tendsto_of_unique_eq
  {d : Nat}
  {beta : Real}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
-- given
  (hunique : forall (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu], IsDLRState d beta 0 mu -> mu = (muLim : Measure _))
  (eta : Nat -> ConfigSpace (Site d))
  (radius : Nat -> Nat)
  (hradius : Tendsto radius atTop atTop) :
-- imply
  WeakConvergesTo (fun k => fvProbabilityMeasure (eta k) (radius k) (bondFinsetTouch d (radius k)) beta 0) muLim := by
-- proof
  apply StatMech.FrontierA.varyingFiniteGibbs_tendsto_of_unique beta muLim hunique eta radius hradius

/--
[isingCritical_varyingFiniteGibbs_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_varyingFiniteGibbs_tendsto_eq
  {d : Nat}
-- given
  (eta : Nat -> ConfigSpace (Site 3))
  (radius : Nat -> Nat)
  (hradius : Tendsto radius atTop atTop) :
-- imply
  WeakConvergesTo (fun k => fvProbabilityMeasure (eta k) (radius k) (bondFinsetTouch 3 (radius k)) (Ising.betaC 3) 0) (minusState 3 (Ising.betaC 3) 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_varyingFiniteGibbs_tendsto eta radius hradius

/--
[isingCritical_varyingFiniteGibbs_localExpectation_sub_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_varyingFiniteGibbs_localExpectation_sub_tendsto_zero_eq
  {d : Nat}
  {f : BoundedContinuousFunction (ConfigSpace (Site 3)) Real}
-- given
  (eta zeta : Nat -> ConfigSpace (Site 3))
  (radius rho : Nat -> Nat)
  (hradius : Tendsto radius atTop atTop)
  (hrho : Tendsto rho atTop atTop) :
-- imply
  Tendsto (fun k => (∫ omega, f omega ∂fvMeasure (eta k) (radius k) (bondFinsetTouch 3 (radius k)) (Ising.betaC 3) 0) - ∫ omega, f omega ∂fvMeasure (zeta k) (rho k) (bondFinsetTouch 3 (rho k)) (Ising.betaC 3) 0) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_varyingFiniteGibbs_localExpectation_sub_tendsto_zero eta zeta radius rho hradius hrho f

/--
[isingCritical_varyingFiniteGibbs_spin_sub_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_varyingFiniteGibbs_spin_sub_tendsto_zero_eq
  {d : Nat}
  {x : Site 3}
-- given
  (eta zeta : Nat -> ConfigSpace (Site 3))
  (radius rho : Nat -> Nat)
  (hradius : Tendsto radius atTop atTop)
  (hrho : Tendsto rho atTop atTop) :
-- imply
  Tendsto (fun k => (∫ omega, spin omega x ∂fvMeasure (eta k) (radius k) (bondFinsetTouch 3 (radius k)) (Ising.betaC 3) 0) - ∫ omega, spin omega x ∂fvMeasure (zeta k) (rho k) (bondFinsetTouch 3 (rho k)) (Ising.betaC 3) 0) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_varyingFiniteGibbs_spin_sub_tendsto_zero eta zeta radius rho hradius hrho x

/--
[gvMeasure_real_sub_abs_le_inner_extremal_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma gvMeasure_real_sub_abs_le_inner_extremal_gap_eq
  {d : Nat}
  {Sin Sout : Finset (Site d)}
  {beta : Real}
  {h : Real}
  {eta zeta : ConfigSpace (Site d)}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hsub : Sin ⊆ Sout)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  |(gvMeasure eta Sout beta h).real A - (gvMeasure zeta Sout beta h).real A| ≤ (gvPlusMeasure Sin beta h).real A - (gvMinusMeasure Sin beta h).real A := by
-- proof
  apply StatMech.FrontierA.gvMeasure_real_sub_abs_le_inner_extremal_gap hsub hbeta hh eta zeta hAmeas hAinc

/--
[isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero_eq
  {d : Nat}
  {x : Site 3} :
-- imply
  Tendsto (fun n => (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real {omega | omega x = true} - (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real {omega | omega x = true}) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero x

/--
[gvMeasure_spinUp_sub_abs_le_critical_centeredGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma gvMeasure_spinUp_sub_abs_le_critical_centeredGap_eq
  {d : Nat}
  {Sout : Finset (Site 3)}
  {eta zeta : ConfigSpace (Site 3)}
  {x : Site 3}
  {n : Nat}
-- given
  (hcontain : (boxFinset 3 n).image (fun y => Multiplicative.ofAdd x • y) ⊆ Sout) :
-- imply
  |(gvMeasure eta Sout (Ising.betaC 3) 0).real {omega | omega x = true} - (gvMeasure zeta Sout (Ising.betaC 3) 0).real {omega | omega x = true}| ≤ (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} - (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} := by
-- proof
  apply StatMech.FrontierA.gvMeasure_spinUp_sub_abs_le_critical_centeredGap Sout eta zeta x n hcontain

/--
[isingCritical_gvBoundary_spinUp_sub_abs_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_gvBoundary_spinUp_sub_abs_tendsto_zero_eq
  {d : Nat}
  {x : Site 3}
-- given
  (Sout : Nat -> Finset (Site 3))
  (eta zeta : Nat -> ConfigSpace (Site 3))
  (hcontain : forall n, (boxFinset 3 n).image (fun y => Multiplicative.ofAdd x • y) ⊆ Sout n) :
-- imply
  Tendsto (fun n => |(gvMeasure (eta n) (Sout n) (Ising.betaC 3) 0).real {omega | omega x = true} - (gvMeasure (zeta n) (Sout n) (Ising.betaC 3) 0).real {omega | omega x = true}|) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_gvBoundary_spinUp_sub_abs_tendsto_zero Sout eta zeta x hcontain

/--
[expJ_spin_induce_le_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma expJ_spin_induce_le_inhomogeneous_eq
  {d : Nat}
  [Fintype U]
  [DecidableEq U]
  {K : SimpleGraph U}
  [DecidableRel K.Adj]
  [DecidablePred P]
  {beta : Real}
  {x : {u // P u}}
-- given
  (P : U -> Prop)
  (hbeta : 0 <= beta)
  (hf : U -> Real)
  (hhf : forall u, 0 <= hf u) :
-- imply
  expJ (K.comap (Subtype.val : {u // P u} -> U)).edgeFinset (fun _ => beta) (fun u => hf u.1) (fun s => spin s x) <= expJ K.edgeFinset (fun _ => beta) hf (fun s => spin s x.1) := by
-- proof
  apply StatMech.FrontierA.expJ_spin_induce_le_inhomogeneous K P beta hbeta hf hhf x

/--
[plusMeasure_spin_eq_spinUp_sub_minus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma plusMeasure_spin_eq_spinUp_sub_minus_eq
  {d : Nat}
  {d n : Nat}
  {beta : Real}
  {x : Site d} :
-- imply
  (∫ omega, spin omega x ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) = (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} - (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} := by
-- proof
  apply StatMech.FrontierA.plusMeasure_spin_eq_spinUp_sub_minus d n beta x

/--
[isingCritical_oddPrismPlusSpinMean_le_centeredGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_oddPrismPlusSpinMean_le_centeredGap_eq
  {d : Nat}
  {n r : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n}
-- given
  (hcontain : (boxFinset 3 r).image (fun y => Multiplicative.ofAdd (rectangularPrismSiteEquivSctBoxDobrushin n v).1 • y) ⊆ boxFinset 3 n) :
-- imply
  oddPrismPlusSpinMean (Ising.betaC 3) n v <= (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} - (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} := by
-- proof
  apply StatMech.FrontierA.isingCritical_oddPrismPlusSpinMean_le_centeredGap n r v hcontain

/--
[oddPrismInternalEdge_not_isDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismInternalEdge_not_isDiag_eq
  {d : Nat}
  {n : Nat}
  {q : OddPrismInternalIndex n} :
-- imply
  ¬ (oddPrismInternalEdge n q).IsDiag := by
-- proof
  apply StatMech.FrontierA.oddPrismInternalEdge_not_isDiag n q

/--
[oddPrismInternalGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismInternalGraph_edgeFinset_eq
  {d : Nat}
  {n : Nat}
  [Fintype (oddPrismInternalGraph n).edgeSet] :
-- imply
  (oddPrismInternalGraph n).edgeFinset = oddPrismInternalEdges n := by
-- proof
  apply StatMech.FrontierA.oddPrismInternalGraph_edgeFinset n

/--
[oddPrismLowerHalfSurfaceSpinMeanAt_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismLowerHalfSurfaceSpinMeanAt_le_plus_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismLowerHalfSurfaceSpinMeanAt beta n i j <= oddPrismPlusSpinMean beta n (oddPrismLowerHalfSurfaceSite n i j).1 := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfSurfaceSpinMeanAt_le_plus beta hbeta n i j

/--
[oddPrismLowerHalfSurfaceSpinMean_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismLowerHalfSurfaceSpinMean_le_plus_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta) :
-- imply
  oddPrismLowerHalfSurfaceSpinMean beta n <= oddPrismPlusSpinMean beta n (oddPrismLowerHalfCenter n).1 := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfSurfaceSpinMean_le_plus beta hbeta n

/--
[oddPrismLowerHalfCenter_to_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismLowerHalfCenter_to_origin_eq
  {d : Nat}
  {n : Nat} :
-- imply
  (rectangularPrismSiteEquivSctBoxDobrushin n (oddPrismLowerHalfCenter n).1).1 = origin 3 := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfCenter_to_origin n

/--
[isingCritical_oddPrismPlusCenter_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_oddPrismPlusCenter_tendsto_zero_eq
  {d : Nat} :
-- imply
  Tendsto (fun n => oddPrismPlusSpinMean (Ising.betaC 3) n (oddPrismLowerHalfCenter n).1) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_oddPrismPlusCenter_tendsto_zero

/--
[oddPrismLowerHalfSurfaceSpinMean_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma oddPrismLowerHalfSurfaceSpinMean_nonneg_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta) :
-- imply
  0 <= oddPrismLowerHalfSurfaceSpinMean beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerHalfSurfaceSpinMean_nonneg beta hbeta n

/--
[isingCritical_oddPrismLowerHalfSurfaceSpinMean_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_oddPrismLowerHalfSurfaceSpinMean_tendsto_zero_eq
  {d : Nat} :
-- imply
  Tendsto (oddPrismLowerHalfSurfaceSpinMean (Ising.betaC 3)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_oddPrismLowerHalfSurfaceSpinMean_tendsto_zero

/--
[mem_criticalCenteredSlab_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma mem_criticalCenteredSlab_iff_eq
  {d : Nat}
  {L H : Nat}
  {x : Site 3} :
-- imply
  x ∈ criticalCenteredSlab L H ↔ (x 0).natAbs ≤ L ∧ (x 1).natAbs ≤ L ∧ (x 2).natAbs ≤ H := by
-- proof
  apply StatMech.FrontierA.mem_criticalCenteredSlab_iff

/--
[translatedBox_subset_criticalCenteredSlab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma translatedBox_subset_criticalCenteredSlab_eq
  {d : Nat}
  {L H r : Nat}
  {x : Site 3}
-- given
  (hx0 : (x 0).natAbs + r ≤ L)
  (hx1 : (x 1).natAbs + r ≤ L)
  (hx2 : (x 2).natAbs + r ≤ H) :
-- imply
  (boxFinset 3 r).image (fun y => Multiplicative.ofAdd x • y) ⊆ criticalCenteredSlab L H := by
-- proof
  apply StatMech.FrontierA.translatedBox_subset_criticalCenteredSlab L H r x hx0 hx1 hx2

/--
[criticalCenteredSlab_spinUp_sub_abs_le_centeredGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma criticalCenteredSlab_spinUp_sub_abs_le_centeredGap_eq
  {d : Nat}
  {L H r : Nat}
  {x : Site 3}
  {eta zeta : ConfigSpace (Site 3)}
-- given
  (hx0 : (x 0).natAbs + r ≤ L)
  (hx1 : (x 1).natAbs + r ≤ L)
  (hx2 : (x 2).natAbs + r ≤ H) :
-- imply
  |(gvMeasure eta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real {omega | omega x = true} - (gvMeasure zeta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real {omega | omega x = true}| ≤ (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} - (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} := by
-- proof
  apply StatMech.FrontierA.criticalCenteredSlab_spinUp_sub_abs_le_centeredGap L H r x hx0 hx1 hx2 eta zeta

/--
[isingCritical_centeredSlab_origin_boundaryInfluence_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean)
-/
@[path]
private lemma isingCritical_centeredSlab_origin_boundaryInfluence_tendsto_zero_eq
  {d : Nat}
-- given
  (L H : Nat -> Nat)
  (eta zeta : Nat -> ConfigSpace (Site 3))
  (hsize : Tendsto (fun n => min (L n) (H n)) atTop atTop) :
-- imply
  Tendsto (fun n => |(gvMeasure (eta n) (criticalCenteredSlab (L n) (H n)) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true} - (gvMeasure (zeta n) (criticalCenteredSlab (L n) (H n)) (Ising.betaC 3) 0).real {omega | omega (origin 3) = true}|) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingCritical_centeredSlab_origin_boundaryInfluence_tendsto_zero L H eta zeta hsize


-- created on 2026-10-23
