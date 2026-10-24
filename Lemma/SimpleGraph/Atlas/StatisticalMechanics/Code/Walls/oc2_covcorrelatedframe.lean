import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_covcorrelatedframe
open Finset StatMech StatMech.Walls


/--
[oc2_meanCorr_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_meanCorr_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_meanCorr G p q g = ∑ ω, g ω * fkMass G p q ω := by
-- proof
  apply StatMech.Walls.oc2_meanCorr_eq G p q g

/--
[oc2_covCorr_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_def_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorr G p q f g = oc2_meanCorr G p q (fun ω => f ω * g ω) - oc2_meanCorr G p q f * oc2_meanCorr G p q g := by
-- proof
  apply StatMech.Walls.oc2_covCorr_def G p q f g

/--
[oc2_coordRead_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_coordRead_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  oc2_coordRead e ω = if ω e then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.Walls.oc2_coordRead_apply G e ω

/--
[oc2_meanCorr_eq_fkMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_meanCorr_eq_fkMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_meanCorr G p q g = FK.fkMean G p q g := by
-- proof
  apply StatMech.Walls.oc2_meanCorr_eq_fkMean G p q g

/--
[oc2_covCorr_eq_fkCov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_eq_fkCov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorr G p q f g = FK.fkCov G p q f g := by
-- proof
  apply StatMech.Walls.oc2_covCorr_eq_fkCov G p q f g

/--
[oc2_coordRead_eq_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_coordRead_eq_coord_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V} :
-- imply
  oc2_coordRead e = (FK.coord e : ConfigSpace (Sym2 V) → ℝ) := by
-- proof
  apply StatMech.Walls.oc2_coordRead_eq_coord G e

/--
[oc2_covCorr_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorr G p q f g = oc2_covCorr G p q g f := by
-- proof
  apply StatMech.Walls.oc2_covCorr_symm G p q f g

/--
[oc2_covCorr_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_add_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (f g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  oc2_covCorr G p q f (fun ω => g ω + h ω) = oc2_covCorr G p q f g + oc2_covCorr G p q f h := by
-- proof
  apply StatMech.Walls.oc2_covCorr_add_right G p q f g h

/--
[oc2_covCorr_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {s : Finset ι}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {g : ι → ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorr G p q f (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, oc2_covCorr G p q f (g i) := by
-- proof
  apply StatMech.Walls.oc2_covCorr_sum_right G p q s f g

/--
[oc2_meanCorr_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_meanCorr_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {c : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_meanCorr G p q (fun ω => c * g ω) = c * oc2_meanCorr G p q g := by
-- proof
  apply StatMech.Walls.oc2_meanCorr_const_mul G p q c g

/--
[oc2_meanCorr_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_meanCorr_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  oc2_meanCorr G p q (fun ω => g ω + h ω) = oc2_meanCorr G p q g + oc2_meanCorr G p q h := by
-- proof
  apply StatMech.Walls.oc2_meanCorr_add G p q g h

/--
[oc2_covCorr_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_smul_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {c : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorr G p q f (fun ω => c * g ω) = c * oc2_covCorr G p q f g := by
-- proof
  apply StatMech.Walls.oc2_covCorr_smul_right G p q c f g

/--
[oc2_covCorr_const_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorr_const_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {c : ℝ}
-- given
  (hZ : FK.fkZ G p q ≠ 0) :
-- imply
  oc2_covCorr G p q f (fun _ => c) = 0 := by
-- proof
  apply StatMech.Walls.oc2_covCorr_const_right G p q f hZ

/--
[oc2_meanCorr_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_meanCorr_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hZ : FK.fkZ G p q ≠ 0) :
-- imply
  oc2_meanCorr G p q (fun _ => (1 : ℝ)) = 1 := by
-- proof
  apply StatMech.Walls.oc2_meanCorr_one G p q hZ

/--
[oc2_covCorrSum_eq_fkCovSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorrSum_eq_fkCovSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  oc2_covCorrSum G p q f = ∑ e ∈ G.edgeFinset, FK.fkCov G p q f (FK.coord e) := by
-- proof
  apply StatMech.Walls.oc2_covCorrSum_eq_fkCovSum G p q f

/--
[oc2_thetaCorr_eq_fkProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_thetaCorr_eq_fkProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  oc2_thetaCorr G p q (A.indicator (fun _ => (1 : ℝ))) = FK.fkProbOf G p q A := by
-- proof
  apply StatMech.Walls.oc2_thetaCorr_eq_fkProbOf G p q A

/--
[oc2_var_indicator_ccf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_var_indicator_ccf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  oc2_covCorr G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ))) = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
-- proof
  apply StatMech.Walls.oc2_var_indicator_ccf G p q A

/--
[oc2_covCorrFrame_hits_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorrFrame_hits_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
  {θμ covCorr : ℝ} :
-- imply
  oc_CodingCovBridge (ν := ν) f θμ covCorr ↔ (covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f) := by
-- proof
  apply StatMech.Walls.oc2_covCorrFrame_hits_bridge G f θμ covCorr

/--
[oc2_covCorrFrame_codingFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorrFrame_codingFixedPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) := by
-- proof
  apply StatMech.Walls.oc2_covCorrFrame_codingFixedPoint G f

/--
[oc2_covCorrFrame_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_covCorrFrame_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
  {θμ covCorr : ℝ}
-- given
  (hbridge : oc_CodingCovBridge (ν := ν) f θμ covCorr) :
-- imply
  covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_covCorrFrame_pinned G f θμ covCorr hbridge

/--
[oc2_correlated_covLowerBound_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean)
-/
@[path]
private lemma oc2_correlated_covLowerBound_frame_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {ν : Sym2 V → Bool → ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  [Fintype κ]
  [Nonempty κ]
  {T : κ → DecisionTree (Sym2 V)}
  {R : κ → Sym2 V → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
  {p qf : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hsum : ∀ e, (∑ k, R k e) ≤ D)
  (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ))) (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ)))) (oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))))) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ))) * (1 - oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ))))) ≤ D * oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc2_correlated_covLowerBound_frame G hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum p qf hbridge


-- created on 2026-10-23
