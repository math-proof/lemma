import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.RussoHamming
open StatMech StatMech.BeffaraDC


/--
[expect_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  expect p (A.indicator (fun _ => (1 : ℝ))) = prob p A := by
-- proof
  apply StatMech.BeffaraDC.expect_indicator p A

/--
[expect_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_add_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f g : ConfigSpace E → ℝ} :
-- imply
  expect p (fun ω => f ω + g ω) = expect p f + expect p g := by
-- proof
  apply StatMech.BeffaraDC.expect_add p f g

/--
[expect_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_const_mul_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {c : ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  expect p (fun ω => c * f ω) = c * expect p f := by
-- proof
  apply StatMech.BeffaraDC.expect_const_mul p c f

/--
[expect_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_mono_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (h : ∀ ω, f ω ≤ g ω) :
-- imply
  expect p f ≤ expect p g := by
-- proof
  apply StatMech.BeffaraDC.expect_mono hp0 hp1 h

/--
[expect_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (h : ∀ ω, 0 ≤ f ω) :
-- imply
  0 ≤ expect p f := by
-- proof
  apply StatMech.BeffaraDC.expect_nonneg hp0 hp1 h

/--
[configWeight_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma configWeight_sum_one_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  ∑ ω : ConfigSpace E, configWeight p ω = 1 := by
-- proof
  apply StatMech.BeffaraDC.configWeight_sum_one p

/--
[configWeight_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma configWeight_logModular_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {a b : ConfigSpace E} :
-- imply
  configWeight p a * configWeight p b = configWeight p (a ⊔ b) * configWeight p (a ⊓ b) := by
-- proof
  apply StatMech.BeffaraDC.configWeight_logModular p a b

/--
[configWeight_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma configWeight_fkg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  FKGLatticeCondition (configWeight (E := E) p) := by
-- proof
  apply StatMech.BeffaraDC.configWeight_fkg p

/--
[fkg_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma fkg_cov_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  expect p f * expect p g ≤ expect p (fun ω => f ω * g ω) := by
-- proof
  apply StatMech.BeffaraDC.fkg_cov hp0 hp1 hf hg

/--
[numOpen_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma numOpen_eq_sum_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E} :
-- imply
  (numOpen ω : ℝ) = ∑ e, (if ω e then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.numOpen_eq_sum ω

/--
[le_open_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma le_open_coord_eq
  [Fintype E]
  [DecidableEq E]
  {ω ω' : ConfigSpace E}
  {e : E}
-- given
  (hle : ω ≤ ω')
  (h : ω e = true) :
-- imply
  ω' e = true := by
-- proof
  apply StatMech.BeffaraDC.le_open_coord hle e h

/--
[numOpen_add_hammingDist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma numOpen_add_hammingDist_eq
  [Fintype E]
  [DecidableEq E]
  {ω ω' : ConfigSpace E}
-- given
  (hle : ω ≤ ω') :
-- imply
  numOpen ω' = numOpen ω + hammingDist ω ω' := by
-- proof
  apply StatMech.BeffaraDC.numOpen_add_hammingDist hle

/--
[numOpen_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma numOpen_mono_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Monotone (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.numOpen_mono

/--
[numOpen_add_hamming_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma numOpen_add_hamming_mono_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)} :
-- imply
  Monotone (fun ω => (numOpen ω : ℝ) + (hammingToSet A ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.numOpen_add_hamming_mono A

/--
[sum_prob_openEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma sum_prob_openEdge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  ∑ e : E, prob p (openEdge e) = expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.sum_prob_openEdge p

/--
[sum_prob_inter_openEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma sum_prob_inter_openEdge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  ∑ e : E, prob p (A ∩ openEdge e) = expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.sum_prob_inter_openEdge p A

/--
[cov_with_numOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma cov_with_numOpen_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  p * (1 - p) * ∑ e, pivotalProb p A e = expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ)) - prob p A * expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.cov_with_numOpen p A hA

/--
[expect_indicator_hamming_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_indicator_hamming_zero_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) = 0 := by
-- proof
  apply StatMech.BeffaraDC.expect_indicator_hamming_zero p A

/--
[prob_mul_expect_hamming_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma prob_mul_expect_hamming_le_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hA : IsIncreasing A) :
-- imply
  prob p A * expect p (fun ω => (hammingToSet A ω : ℝ)) ≤ expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ)) - prob p A * expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.prob_mul_expect_hamming_le hp0 hp1 A hA

/--
[russoHamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma russoHamming_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  4 * prob p A * expect p (fun ω => (hammingToSet A ω : ℝ)) ≤ deriv (fun p => prob p A) p := by
-- proof
  apply StatMech.BeffaraDC.russoHamming hp0 hp1 A hA

/--
[expect_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_neg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  expect p (fun ω => - f ω) = - expect p f := by
-- proof
  apply StatMech.BeffaraDC.expect_neg p f

/--
[fkg_anticorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma fkg_anticorr_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hf : Antitone f)
  (hg : Monotone g) :
-- imply
  expect p (fun ω => f ω * g ω) ≤ expect p f * expect p g := by
-- proof
  apply StatMech.BeffaraDC.fkg_anticorr hp0 hp1 hf hg

/--
[hasDerivAt_expect_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma hasDerivAt_expect_raw_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => expect p f) (∑ ω, f ω * ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
-- proof
  apply StatMech.BeffaraDC.hasDerivAt_expect_raw f p

/--
[differentiable_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma differentiable_expect_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ} :
-- imply
  Differentiable ℝ (fun p => expect p f) := by
-- proof
  apply StatMech.BeffaraDC.differentiable_expect f

/--
[deriv_term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma deriv_term_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ω : ConfigSpace E}
  {e : E}
-- given
  (hp0 : p ≠ 0)
  (hp1 : (1 : ℝ) - p ≠ 0) :
-- imply
  weightOff p e ω * (if ω e then (1 : ℝ) else -1) = configWeight p ω * ((if ω e then (1 : ℝ) else 0) - p) / (p * (1 - p)) := by
-- proof
  apply StatMech.BeffaraDC.deriv_term_eq hp0 hp1 ω e

/--
[deriv_omega_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma deriv_omega_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ω : ConfigSpace E}
-- given
  (hp0 : p ≠ 0)
  (hp1 : (1 : ℝ) - p ≠ 0) :
-- imply
  ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1) = configWeight p ω * ((numOpen ω : ℝ) - p * (Fintype.card E)) / (p * (1 - p)) := by
-- proof
  apply StatMech.BeffaraDC.deriv_omega_eq hp0 hp1 ω

/--
[hasDerivAt_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma hasDerivAt_expect_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp0 : p ≠ 0)
  (hp1 : (1 : ℝ) - p ≠ 0) :
-- imply
  HasDerivAt (fun p => expect p f) ((expect p (fun ω => f ω * (numOpen ω : ℝ)) - p * (Fintype.card E) * expect p f) / (p * (1 - p))) p := by
-- proof
  apply StatMech.BeffaraDC.hasDerivAt_expect f hp0 hp1

/--
[deriv_expect_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma deriv_expect_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp0 : p ≠ 0)
  (hp1 : (1 : ℝ) - p ≠ 0) :
-- imply
  deriv (fun p => expect p f) p = (expect p (fun ω => f ω * (numOpen ω : ℝ)) - p * (Fintype.card E) * expect p f) / (p * (1 - p)) := by
-- proof
  apply StatMech.BeffaraDC.deriv_expect_eq f hp0 hp1

/--
[expect_numOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_numOpen_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) = p * (Fintype.card E) := by
-- proof
  apply StatMech.BeffaraDC.expect_numOpen p

/--
[expect_antitoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_antitoneOn_eq
  [Fintype E]
  [DecidableEq E]
  {p₁ p₂ : ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hp1 : 0 < p₁)
  (hp2 : p₂ < 1)
  (hf : Antitone f) :
-- imply
  AntitoneOn (fun p => expect p f) (Set.Icc p₁ p₂) := by
-- proof
  apply StatMech.BeffaraDC.expect_antitoneOn hp1 hp2 hf

/--
[hammingToSet_real_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma hammingToSet_real_antitone_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  Antitone (fun ω => (hammingToSet A ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.hammingToSet_real_antitone A hA

/--
[differentiable_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma differentiable_prob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)} :
-- imply
  Differentiable ℝ (fun p => prob p A) := by
-- proof
  apply StatMech.BeffaraDC.differentiable_prob A

/--
[prob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma prob_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ prob p A := by
-- proof
  apply StatMech.BeffaraDC.prob_nonneg hp0 hp1 A

/--
[expect_hamming_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma expect_hamming_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.expect_hamming_nonneg hp0 hp1 A

/--
[gronwall_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma gronwall_prob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {c : ℝ}
  {p₁ p₂ : ℝ}
-- given
  (hp : p₁ ≤ p₂)
  (hdiff : ∀ p ∈ Set.Icc p₁ p₂, c * prob p A ≤ deriv (fun p => prob p A) p) :
-- imply
  prob p₁ A ≤ prob p₂ A * Real.exp (- c * (p₂ - p₁)) := by
-- proof
  apply StatMech.BeffaraDC.gronwall_prob A c hp hdiff

/--
[russoHammingIntegrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean)
-/
@[path]
private lemma russoHammingIntegrated_eq
  [Fintype E]
  [DecidableEq E]
  {p₁ p₂ : ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp1 : 0 < p₁)
  (hp12 : p₁ < p₂)
  (hp2 : p₂ < 1)
  (hA : IsIncreasing A) :
-- imply
  prob p₁ A ≤ prob p₂ A * Real.exp (- 4 * (p₂ - p₁) * expect p₂ (fun ω => (hammingToSet A ω : ℝ))) := by
-- proof
  apply StatMech.BeffaraDC.russoHammingIntegrated hp1 hp12 hp2 A hA


-- created on 2026-10-23
