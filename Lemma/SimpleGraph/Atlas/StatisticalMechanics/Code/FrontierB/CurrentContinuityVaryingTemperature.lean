import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
open Filter MeasureTheory ProbabilityTheory MeasurableSpace Set Topology StatMech StatMech.FrontierB


/--
[continuous_fvWeight_beta_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma continuous_fvWeight_beta_boundary_eq
  {d : Nat}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : Real)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun z : Real × ConfigSpace (Site d) => fvWeight z.2 n B z.1 h tau) := by
-- proof
  apply StatMech.FrontierB.continuous_fvWeight_beta_boundary n B h tau

/--
[continuous_fvZ_beta_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma continuous_fvZ_beta_boundary_eq
  {d : Nat}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : Real) :
-- imply
  Continuous (fun z : Real × ConfigSpace (Site d) => fvZ z.2 n B z.1 h) := by
-- proof
  apply StatMech.FrontierB.continuous_fvZ_beta_boundary n B h

/--
[continuous_fvProb_beta_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma continuous_fvProb_beta_boundary_eq
  {d : Nat}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : Real)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun z : Real × ConfigSpace (Site d) => fvProb z.2 n B z.1 h tau) := by
-- proof
  apply StatMech.FrontierB.continuous_fvProb_beta_boundary n B h tau

/--
[continuous_specApply_beta_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma continuous_specApply_beta_boundary_eq
  {d : Nat}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (h : Real) :
-- imply
  Continuous (fun z : Real × ConfigSpace (Site d) => specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2) := by
-- proof
  apply StatMech.FrontierB.continuous_specApply_beta_boundary n B h f

/--
[specApply_tendstoUniformly_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma specApply_tendstoUniformly_beta_eq
  {d : Nat}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) →ᵇ Real}
  {betaSeq : Nat → Real}
  {beta : Real}
-- given
  (h : Real)
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  TendstoUniformly (fun k omega => specApply n B (betaSeq k) h (f : ConfigSpace (Site d) → Real) omega) (fun omega => specApply n B beta h (f : ConfigSpace (Site d) → Real) omega) atTop := by
-- proof
  apply StatMech.FrontierB.specApply_tendstoUniformly_beta n B h f hbeta

/--
[fvMeasure_specApply_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma fvMeasure_specApply_integral_eq_eq
  {d : Nat}
  {eta : ConfigSpace (Site d)}
  {n m : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hnm : n ≤ m)
  (beta h : Real) :
-- imply
  (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂(fvMeasure eta m (bondFinsetTouch d m) beta h)) = ∫ omega, f omega ∂(fvMeasure eta m (bondFinsetTouch d m) beta h) := by
-- proof
  apply StatMech.FrontierB.fvMeasure_specApply_integral_eq eta hnm beta h f

/--
[integral_specApply_tendsto_of_beta_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma integral_specApply_tendsto_of_beta_tendsto_eq
  {d : Nat}
  {mu : Nat → ProbabilityMeasure (ConfigSpace (Site d))}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
  {betaSeq : Nat → Real}
  {beta h : Real}
  {n : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hmu : WeakConvergesTo mu muLim)
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  Tendsto (fun k => ∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h (f : ConfigSpace (Site d) → Real) omega ∂(mu k : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂(muLim : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_specApply_tendsto_of_beta_tendsto mu muLim hmu hbeta n f

/--
[isingSpecFull_bind_eq_of_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma isingSpecFull_bind_eq_of_integral_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
-- given
  (beta h : Real)
  (hinv : ∀ (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real), (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂mu) = ∫ omega, f omega ∂mu) :
-- imply
  (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu := by
-- proof
  apply StatMech.FrontierB.isingSpecFull_bind_eq_of_integral_eq beta h mu hinv n

/--
[compProd_rect_of_isingSpecFull_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma compProd_rect_of_isingSpecFull_bind_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
  {s : Set (ConfigSpace (Site d))}
  {t : Set (ConfigSpace (Site d))}
-- given
  (beta h : Real)
  (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu)
  (hs : MeasurableSet[outsideSigma (box d n)] s)
  (ht : MeasurableSet t) :
-- imply
  ((mu.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) beta h)) (s ×ˢ t) = mu (s ∩ t) := by
-- proof
  apply StatMech.FrontierB.compProd_rect_of_isingSpecFull_bind_eq beta h mu n hbind hs ht

/--
[isDLRState_of_specApply_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma isDLRState_of_specApply_integral_eq_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (beta h : Real)
  (hinv : ∀ (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real), (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂mu) = ∫ omega, f omega ∂mu) :
-- imply
  IsDLRState d beta h mu := by
-- proof
  apply StatMech.FrontierB.isDLRState_of_specApply_integral_eq beta h mu hinv

/--
[varyingFiniteGibbsWeakLimit_isDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma varyingFiniteGibbsWeakLimit_isDLR_eq
  {d : Nat}
  {eta : Nat → ConfigSpace (Site d)}
  {radius : Nat → Nat}
  {betaSeq : Nat → Real}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
-- given
  (beta h : Real)
  (hradius : Tendsto radius atTop atTop)
  (hbeta : Tendsto betaSeq atTop (nhds beta))
  (hweak : WeakConvergesTo (fun k => fvProbabilityMeasure (eta k) (radius k) (bondFinsetTouch d (radius k)) (betaSeq k) h) muLim) :
-- imply
  IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.varyingFiniteGibbsWeakLimit_isDLR eta radius betaSeq beta h hradius hbeta muLim hweak

/--
[varyingFreeGibbsWeakLimit_isDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma varyingFreeGibbsWeakLimit_isDLR_eq
  {d : Nat}
  {radius : Nat → Nat}
  {betaSeq : Nat → Real}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
-- given
  (beta h : Real)
  (hradius : Tendsto radius atTop atTop)
  (hbeta : Tendsto betaSeq atTop (nhds beta))
  (hweak : WeakConvergesTo (fun k => freeMeasure d (radius k) (betaSeq k) h) muLim) :
-- imply
  IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.varyingFreeGibbsWeakLimit_isDLR radius betaSeq beta h hradius hbeta muLim hweak

/--
[freeState_isDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma freeState_isDLR_eq
  {d : Nat}
-- given
  (beta h : Real) :
-- imply
  IsDLRState d beta h (freeState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.freeState_isDLR beta h

/--
[currentContinuity_freeState_eq_minusState_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_freeState_eq_minusState_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (freeState d beta 0 : Measure (ConfigSpace (Site d))) = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_freeState_eq_minusState_of_freeLROZero beta hbeta0 hd hLRO

/--
[currentContinuity_plusState_eq_freeState_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_plusState_eq_freeState_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (plusState d beta 0 : Measure (ConfigSpace (Site d))) = (freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_plusState_eq_freeState_of_freeLROZero beta hbeta0 hd hLRO

/--
[currentContinuity_allTwoPoint_eq_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_allTwoPoint_eq_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  ∀ x y : Site d, currentContinuityPlusTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta x y := by
-- proof
  apply StatMech.FrontierB.currentContinuity_allTwoPoint_eq_of_freeLROZero beta hbeta0 hd hLRO

/--
[isingSpecFull_bind_eq_of_isDLRState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma isingSpecFull_bind_eq_of_isDLRState_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
-- given
  (beta h : Real)
  (hmu : IsDLRState d beta h mu) :
-- imply
  (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu := by
-- proof
  apply StatMech.FrontierB.isingSpecFull_bind_eq_of_isDLRState beta h mu hmu n

/--
[specApply_integral_eq_of_isDLRState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma specApply_integral_eq_of_isDLRState_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {n : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (beta h : Real)
  (hmu : IsDLRState d beta h mu) :
-- imply
  (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂mu) = ∫ omega, f omega ∂mu := by
-- proof
  apply StatMech.FrontierB.specApply_integral_eq_of_isDLRState beta h mu hmu n f

/--
[varyingDLRWeakLimit_isDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma varyingDLRWeakLimit_isDLR_eq
  {d : Nat}
  {mu : Nat → ProbabilityMeasure (ConfigSpace (Site d))}
  {betaSeq : Nat → Real}
  {muLim : ProbabilityMeasure (ConfigSpace (Site d))}
-- given
  (beta h : Real)
  (hmu : ∀ k, IsDLRState d (betaSeq k) h (mu k : Measure (ConfigSpace (Site d))))
  (hbeta : Tendsto betaSeq atTop (nhds beta))
  (hweak : WeakConvergesTo mu muLim) :
-- imply
  IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.varyingDLRWeakLimit_isDLR mu betaSeq beta h hmu hbeta muLim hweak

/--
[currentContinuity_varyingDLR_tendsto_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_varyingDLR_tendsto_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
  {mu : Nat → ProbabilityMeasure (ConfigSpace (Site d))}
  {betaSeq : Nat → Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hmu : ∀ k, IsDLRState d (betaSeq k) 0 (mu k : Measure (ConfigSpace (Site d))))
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  WeakConvergesTo mu (minusState d beta 0) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_varyingDLR_tendsto_of_freeLROZero beta hbeta0 hd hLRO mu betaSeq hmu hbeta

/--
[currentContinuity_varyingFiniteGibbs_tendsto_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_varyingFiniteGibbs_tendsto_of_freeLROZero_eq
  {d : Nat}
  {beta : Real}
  {eta : Nat → ConfigSpace (Site d)}
  {radius : Nat → Nat}
  {betaSeq : Nat → Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hradius : Tendsto radius atTop atTop)
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  WeakConvergesTo (fun k => fvProbabilityMeasure (eta k) (radius k) (bondFinsetTouch d (radius k)) (betaSeq k) 0) (minusState d beta 0) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_varyingFiniteGibbs_tendsto_of_freeLROZero beta hbeta0 hd hLRO eta radius betaSeq hradius hbeta

/--
[currentContinuity_varyingDLR_localExpectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_varyingDLR_localExpectation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {mu : Nat → ProbabilityMeasure (ConfigSpace (Site d))}
  {betaSeq : Nat → Real}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hmu : ∀ k, IsDLRState d (betaSeq k) 0 (mu k : Measure (ConfigSpace (Site d))))
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  Tendsto (fun k => ∫ omega, f omega ∂(mu k : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, f omega ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_varyingDLR_localExpectation_tendsto beta hbeta0 hd hLRO mu betaSeq hmu hbeta f

/--
[currentContinuity_varyingFiniteGibbs_localExpectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean)
-/
@[path]
private lemma currentContinuity_varyingFiniteGibbs_localExpectation_tendsto_eq
  {d : Nat}
  {beta : Real}
  {eta : Nat → ConfigSpace (Site d)}
  {radius : Nat → Nat}
  {betaSeq : Nat → Real}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hbeta0 : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta)
  (hradius : Tendsto radius atTop atTop)
  (hbeta : Tendsto betaSeq atTop (nhds beta)) :
-- imply
  Tendsto (fun k => ∫ omega, f omega ∂(fvMeasure (eta k) (radius k) (bondFinsetTouch d (radius k)) (betaSeq k) 0)) atTop (nhds (∫ omega, f omega ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_varyingFiniteGibbs_localExpectation_tendsto beta hbeta0 hd hLRO eta radius betaSeq hradius hbeta f


-- created on 2026-10-23
