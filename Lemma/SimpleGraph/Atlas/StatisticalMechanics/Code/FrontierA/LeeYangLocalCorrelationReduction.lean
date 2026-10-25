import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part4
open Complex Filter MeasureTheory Metric Set Topology StatMech StatMech.FrontierA


/--
[leeYangBoxSpinProduct_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_ofReal_eq
  {d n : ℕ}
  {A : Finset (Site d)}
-- given
  (beta h : ℝ) :
-- imply
  leeYangBoxSpinProduct d beta A n (h : ℂ) = (isingExpectation (boxGraph d n) beta h (spinProd (boxSpinSupport d n A)) : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_ofReal d n beta h A

/--
[leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane_eq
  {d n : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n) {h : ℂ | 0 < h.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane d n hbeta A

/--
[leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane_eq
  {d n : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n) {h : ℂ | h.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane d n hbeta A

/--
[leeYangBoxSpinProduct_tendsto_of_nonneg_real_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_tendsto_of_nonneg_real_field_eq
  {d : ℕ}
  {A : Finset (Site d)}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop (nhds (Complex.ofReal (∫ omega, spinProd A omega ∂(freeState d beta h : Measure (ConfigSpace (Site d)))))) := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_tendsto_of_nonneg_real_field d beta h hbeta hh A

/--
[isingExpectation_spinProd_neg_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma isingExpectation_spinProd_neg_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation G beta (-h) (spinProd A) = (-1 : ℝ) ^ A.card * isingExpectation G beta h (spinProd A) := by
-- proof
  apply StatMech.FrontierA.isingExpectation_spinProd_neg_field G beta h A

/--
[boxSpinSupport_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma boxSpinSupport_card_eq_eq
  {d n : ℕ}
  {A : Finset (Site d)}
-- given
  (hA : ↑A ⊆ box d n) :
-- imply
  (boxSpinSupport d n A).card = A.card := by
-- proof
  apply StatMech.FrontierA.boxSpinSupport_card_eq d n A hA

/--
[leeYangBoxSpinProduct_tendsto_of_neg_real_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_tendsto_of_neg_real_field_eq
  {d : ℕ}
  {A : Finset (Site d)}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : h < 0) :
-- imply
  Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop (nhds ((((-1 : ℝ) : ℂ) ^ A.card) * Complex.ofReal (∫ omega, spinProd A omega ∂(freeState d beta (-h) : Measure (ConfigSpace (Site d)))))) := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_tendsto_of_neg_real_field d beta h hbeta hh A

/--
[continuousOn_leeYangSpinProductRightEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma continuousOn_leeYangSpinProductRightEnvelope_eq
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 < beta) :
-- imply
  ContinuousOn (leeYangSpinProductRightEnvelope beta A) {h : ℂ | 0 < h.re} := by
-- proof
  apply StatMech.FrontierA.continuousOn_leeYangSpinProductRightEnvelope hbeta A

/--
[continuousOn_leeYangSpinProductLeftEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma continuousOn_leeYangSpinProductLeftEnvelope_eq
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 < beta) :
-- imply
  ContinuousOn (leeYangSpinProductLeftEnvelope beta A) {h : ℂ | h.re < 0} := by
-- proof
  apply StatMech.FrontierA.continuousOn_leeYangSpinProductLeftEnvelope hbeta A

/--
[leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
  {K : Set ℂ}
-- given
  (hbeta : 0 < beta)
  (hpoint : LeeYangSpinProductRightBound d beta A)
  (hK : IsCompact K)
  (hKright : K ⊆ {h : ℂ | 0 < h.re}) :
-- imply
  ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane d hbeta A hpoint hK hKright

/--
[leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
  {K : Set ℂ}
-- given
  (hbeta : 0 < beta)
  (hpoint : LeeYangSpinProductLeftBound d beta A)
  (hK : IsCompact K)
  (hKleft : K ⊆ {h : ℂ | h.re < 0}) :
-- imply
  ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane d hbeta A hpoint hK hKleft

/--
[leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hpoint : LeeYangSpinProductRightBound d beta A) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ TendstoLocallyUniformlyOn (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g) atTop {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound d hd hbeta A hpoint

/--
[leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hpoint : LeeYangSpinProductLeftBound d beta A) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ TendstoLocallyUniformlyOn (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g) atTop {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound d hd hbeta A hpoint

/--
[multiAffine_sign_update_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma multiAffine_sign_update_norm_le_eq
  [DecidableEq I]
  {p : (I → ℂ) → ℂ}
  {z : I → ℂ}
  {i : I}
-- given
  (hpAff : IsMultiAffine p)
  (hpStable : PolydiscStable p)
  (hz : ∀ j, ‖z j‖ < 1) :
-- imply
  ‖p (Function.update z i (-z i))‖ ≤ ((1 + ‖z i‖) / (1 - ‖z i‖)) * ‖p z‖ := by
-- proof
  apply StatMech.FrontierA.multiAffine_sign_update_norm_le p hpAff hpStable z hz i

/--
[leeYangMonomial_anchorSupport_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangMonomial_anchorSupport_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {z : LeeYangVar G → ℂ} :
-- imply
  leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s)) z = ∏ v : V, if s v = false then z (leeYangAnchor G v) else 1 := by
-- proof
  apply StatMech.FrontierA.leeYangMonomial_anchorSupport_flip G s z

/--
[leeYangSignedProduct_eq_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSignedProduct_eq_spinProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {A : Finset V}
  {q : ℂ} :
-- imply
  (∏ v : V, if s v = false then leeYangSignedDiagonal G A q (leeYangAnchor G v) else 1) = (spinProd A s : ℂ) * q ^ minusSpinCount s := by
-- proof
  apply StatMech.FrontierA.leeYangSignedProduct_eq_spinProd G s A q

/--
[leeYangSignedDiagonal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSignedDiagonal_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℂ} :
-- imply
  leeYangSignedDiagonal G ∅ q = leeYangDiagonal G q := by
-- proof
  apply StatMech.FrontierA.leeYangSignedDiagonal_empty G q

/--
[leeYangSignedDiagonal_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSignedDiagonal_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {v : V}
  {q : ℂ}
-- given
  (hv : v ∉ A) :
-- imply
  leeYangSignedDiagonal G (insert v A) q = Function.update (leeYangSignedDiagonal G A q) (leeYangAnchor G v) (-q) := by
-- proof
  apply StatMech.FrontierA.leeYangSignedDiagonal_insert G A v hv q

/--
[leeYangSignedDiagonal_norm_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSignedDiagonal_norm_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {q : ℂ}
-- given
  (hq : ‖q‖ < 1) :
-- imply
  ∀ k, ‖leeYangSignedDiagonal G A q k‖ < 1 := by
-- proof
  apply StatMech.FrontierA.leeYangSignedDiagonal_norm_lt G A hq

/--
[leeYangContracted_signed_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangContracted_signed_norm_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {q : ℂ}
  {A : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hq : ‖q‖ < 1) :
-- imply
  ‖leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)‖ ≤ ((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card * ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖ := by
-- proof
  apply StatMech.FrontierA.leeYangContracted_signed_norm_le G hbeta hq A

/--
[leeYangContracted_signed_eq_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangContracted_signed_eq_spin_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {q : ℂ} :
-- imply
  (Real.exp (beta * G.edgeFinset.card) : ℂ) * leeYangContractedProduct G beta (leeYangSignedDiagonal G A q) = ∑ s : ConfigSpace V, (spinProd A s : ℂ) * (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
-- proof
  apply StatMech.FrontierA.leeYangContracted_signed_eq_spin_sum G beta A q

/--
[leeYangObservable_fugacity_eq_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangObservable_fugacity_eq_signed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
-- given
  (h : ℂ) :
-- imply
  Complex.exp (-(beta : ℂ) * h * Fintype.card V) * leeYangComplexFieldObservableNumerator G beta (fun s ↦ (spinProd A s : ℂ)) h = (Real.exp (beta * G.edgeFinset.card) : ℂ) * leeYangContractedProduct G beta (leeYangSignedDiagonal G A (Complex.exp (-2 * (beta : ℂ) * h))) := by
-- proof
  apply StatMech.FrontierA.leeYangObservable_fugacity_eq_signed G beta A h

/--
[leeYangComplexFieldExpectation_spinProd_eq_contractedRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_spinProd_eq_contractedRatio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {h : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : h.re ≠ 0) :
-- imply
  leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) h = leeYangContractedProduct G beta (leeYangSignedDiagonal G A (Complex.exp (-2 * (beta : ℂ) * h))) / leeYangContractedProduct G beta (leeYangDiagonal G (Complex.exp (-2 * (beta : ℂ) * h))) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_spinProd_eq_contractedRatio G hbeta A hh

/--
[leeYangComplexFieldExpectation_spinProd_norm_le_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_spinProd_norm_le_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
  {h : ℂ}
-- given
  (hbeta : 0 < beta)
  (hh : 0 < h.re) :
-- imply
  ‖leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) h‖ ≤ ((1 + ‖Complex.exp (-2 * (beta : ℂ) * h)‖) / (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)) ^ A.card := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_spinProd_norm_le_right G hbeta A hh

/--
[boxSpinSupport_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma boxSpinSupport_card_le_eq
  {d n : ℕ}
  {A : Finset (Site d)} :
-- imply
  (boxSpinSupport d n A).card ≤ A.card := by
-- proof
  apply StatMech.FrontierA.boxSpinSupport_card_le d n A

/--
[leeYangSpinProductRightBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSpinProductRightBound_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 < beta) :
-- imply
  LeeYangSpinProductRightBound d beta A := by
-- proof
  apply StatMech.FrontierA.leeYangSpinProductRightBound d hbeta A

/--
[leeYangComplexFieldPartition_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldPartition G beta (-h) = leeYangComplexFieldPartition G beta h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_neg G beta h

/--
[leeYangComplexFieldObservable_spinProd_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangComplexFieldObservable_spinProd_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldObservableNumerator G beta (fun s ↦ (spinProd A s : ℂ)) (-h) = (((-1 : ℝ) : ℂ) ^ A.card) * leeYangComplexFieldObservableNumerator G beta (fun s ↦ (spinProd A s : ℂ)) h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldObservable_spinProd_neg G beta h A

/--
[leeYangComplexFieldExpectation_spinProd_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangComplexFieldExpectation_spinProd_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V}
-- given
  (h : ℂ) :
-- imply
  leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) (-h) = (((-1 : ℝ) : ℂ) ^ A.card) * leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) h := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldExpectation_spinProd_neg G beta h A

/--
[leeYangSpinProductLeftBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangSpinProductLeftBound_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 < beta) :
-- imply
  LeeYangSpinProductLeftBound d beta A := by
-- proof
  apply StatMech.FrontierA.leeYangSpinProductLeftBound d hbeta A

/--
[leeYangBoxSpinProduct_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ TendstoLocallyUniformlyOn (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g) atTop {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_rightHalfPlane d hd hbeta A

/--
[leeYangBoxSpinProduct_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean)
-/
@[path]
private lemma leeYangBoxSpinProduct_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ TendstoLocallyUniformlyOn (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g) atTop {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBoxSpinProduct_leftHalfPlane d hd hbeta A


-- created on 2026-10-23
