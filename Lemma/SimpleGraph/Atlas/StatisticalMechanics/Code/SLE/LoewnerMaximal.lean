import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
open Complex Set Metric Filter Topology StatMech StatMech.SLE


/--
[positiveOn_Icc_of_deriv_nonneg_while_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma positiveOn_Icc_of_deriv_nonneg_while_pos_eq
  {T : ℝ}
  {f : ℝ → ℝ}
-- given
  (hcont : ContinuousOn f (Icc (0 : ℝ) T))
  (hzero : 0 < f 0)
  (hderiv : ∀ s ∈ Ioo (0 : ℝ) T, 0 < f s → ∃ v : ℝ, HasDerivAt f v s ∧ 0 ≤ v) :
-- imply
  ∀ s ∈ Icc (0 : ℝ) T, 0 < f s := by
-- proof
  apply StatMech.SLE.positiveOn_Icc_of_deriv_nonneg_while_pos hcont hzero hderiv

/--
[LoewnerForwardSolution.continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousOn_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T : ℝ}
  {g : LoewnerForwardSolution W z T} :
-- imply
  ContinuousOn g.curve (Icc (0 : ℝ) T) := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.continuousOn g

/--
[LoewnerForwardSolution.re_gt_driverBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma re_gt_driverBarrier_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T M d : ℝ}
  {g : LoewnerForwardSolution W z T}
-- given
  (hd : 0 < d)
  (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
  (hz : M + d ≤ z.re) :
-- imply
  ∀ s ∈ Icc (0 : ℝ) T, M + d / 2 < (g.curve s).re := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.re_gt_driverBarrier g hd hW hz

/--
[LoewnerForwardSolution.im_ge_exp_of_driverBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma im_ge_exp_of_driverBarrier_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T M d : ℝ}
  {g : LoewnerForwardSolution W z T}
-- given
  (hd : 0 < d)
  (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
  (hz : M + d ≤ z.re) :
-- imply
  ∀ s ∈ Icc (0 : ℝ) T, z.im * Real.exp (-(2 / (d / 2) ^ 2) * s) ≤ (g.curve s).im := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.im_ge_exp_of_driverBarrier g hd hW hz

/--
[LoewnerForwardSolution.im_antitoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma im_antitoneOn_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T : ℝ}
  {g : LoewnerForwardSolution W z T} :
-- imply
  AntitoneOn (fun t ↦ (g.curve t).im) (Icc (0 : ℝ) T) := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.im_antitoneOn g

/--
[LoewnerForwardSolution.hasDerivWithinAt_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma hasDerivWithinAt_Ici_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T : ℝ}
  {g : LoewnerForwardSolution W z T} :
-- imply
  ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt g.curve (loewnerField W t (g.curve t)) (Ici t) t := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.hasDerivWithinAt_Ici g

/--
[LoewnerForwardSolution.eqOn_overlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma eqOn_overlap_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {S T : ℝ}
  {g : LoewnerForwardSolution W z S}
-- given
  (hS : 0 < S)
  (hT : 0 < T)
  (h : LoewnerForwardSolution W z T) :
-- imply
  EqOn g.curve h.curve (Icc (0 : ℝ) (min S T)) := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.eqOn_overlap hS hT g h

/--
[LoewnerForwardSolution.initial_eq_of_eq_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma initial_eq_of_eq_at_eq
  {W : ℝ → ℝ}
  {z w : ℂ}
  {S T t : ℝ}
  {g : LoewnerForwardSolution W z S}
-- given
  (hS : 0 < S)
  (hT : 0 < T)
  (h : LoewnerForwardSolution W w T)
  (ht0 : 0 < t)
  (htS : t < S)
  (htT : t < T)
  (heq : g.curve t = h.curve t) :
-- imply
  z = w := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.initial_eq_of_eq_at hS hT g h ht0 htS htT heq

/--
[exists_loewnerBackwardSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerBackwardSegment_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (hu : 0 ≤ u)
  (hy : 0 < y.im)
  (hshort : u < y.im ^ 2 / 16) :
-- imply
  ∃ x : ℂ, ∃ g : LoewnerForwardSolution (fun r ↦ W (s + r)) x u, g.curve u = y := by
-- proof
  apply StatMech.SLE.exists_loewnerBackwardSegment hW hu hy hshort

/--
[LoewnerForwardSolution.append_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma append_terminal_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {S T : ℝ}
  {g : LoewnerForwardSolution W z S}
-- given
  (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T)
  (hS : 0 ≤ S)
  (hT : 0 ≤ T) :
-- imply
  (g.append h hS hT).curve (S + T) = h.curve T := by
-- proof
  apply StatMech.SLE.LoewnerForwardSolution.append_terminal g h hS hT

/--
[exists_loewnerBackwardSolution_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerBackwardSolution_steps_eq
  {W : ℝ → ℝ}
  {u : ℝ}
  {n : ℕ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (hu : 0 ≤ u)
  (hy : 0 < y.im)
  (hshort : u < y.im ^ 2 / 16) :
-- imply
  ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x ((n : ℝ) * u), g.curve ((n : ℝ) * u) = y := by
-- proof
  apply StatMech.SLE.exists_loewnerBackwardSolution_steps hW hu n hy hshort

/--
[exists_loewnerBackwardSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerBackwardSolution_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : 0 < y.im) :
-- imply
  ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x t, g.curve t = y := by
-- proof
  apply StatMech.SLE.exists_loewnerBackwardSolution hW ht hy

/--
[exists_loewnerForwardSolution_steps_of_driverBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerForwardSolution_steps_of_driverBarrier_eq
  {W : ℝ → ℝ}
  {T M d u : ℝ}
  {z : ℂ}
  {n : ℕ}
-- given
  (hWcont : Continuous W)
  (hd : 0 < d)
  (hu : 0 ≤ u)
  (hzim : 0 < z.im)
  (hzre : M + d ≤ z.re)
  (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
  (hstep : u < (z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)) ^ 2 / 8)
  (hnT : (n : ℝ) * u ≤ T) :
-- imply
  Nonempty (LoewnerForwardSolution W z ((n : ℝ) * u)) := by
-- proof
  apply StatMech.SLE.exists_loewnerForwardSolution_steps_of_driverBarrier hWcont hd hu hzim hzre hW hstep n hnT

/--
[exists_loewnerForwardSolution_of_driverBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerForwardSolution_of_driverBarrier_eq
  {W : ℝ → ℝ}
  {T M d : ℝ}
  {z : ℂ}
-- given
  (hWcont : Continuous W)
  (hT : 0 ≤ T)
  (hd : 0 < d)
  (hzim : 0 < z.im)
  (hzre : M + d ≤ z.re)
  (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M) :
-- imply
  Nonempty (LoewnerForwardSolution W z T) := by
-- proof
  apply StatMech.SLE.exists_loewnerForwardSolution_of_driverBarrier hWcont hT hd hzim hzre hW

/--
[exists_loewnerForwardSolution_of_driverLowerBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerForwardSolution_of_driverLowerBarrier_eq
  {W : ℝ → ℝ}
  {T m d : ℝ}
  {z : ℂ}
-- given
  (hWcont : Continuous W)
  (hT : 0 ≤ T)
  (hd : 0 < d)
  (hzim : 0 < z.im)
  (hzre : z.re ≤ m - d)
  (hW : ∀ s ∈ Icc (0 : ℝ) T, m ≤ W s) :
-- imply
  Nonempty (LoewnerForwardSolution W z T) := by
-- proof
  apply StatMech.SLE.exists_loewnerForwardSolution_of_driverLowerBarrier hWcont hT hd hzim hzre hW

/--
[exists_isLoewnerAdmissibleDuration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_isLoewnerAdmissibleDuration_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ∃ T, IsLoewnerAdmissibleDuration W z T := by
-- proof
  apply StatMech.SLE.exists_isLoewnerAdmissibleDuration hW hz

/--
[IsLoewnerAdmissibleDuration.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mono_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {S T : ℝ}
-- given
  (hT : IsLoewnerAdmissibleDuration W z T)
  (hS : 0 < S)
  (hST : S ≤ T) :
-- imply
  IsLoewnerAdmissibleDuration W z S := by
-- proof
  apply StatMech.SLE.IsLoewnerAdmissibleDuration.mono hT hS hST

/--
[ofReal_le_loewnerLifetime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma ofReal_le_loewnerLifetime_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T : ℝ}
-- given
  (hT : IsLoewnerAdmissibleDuration W z T) :
-- imply
  ENNReal.ofReal T ≤ loewnerLifetime W z := by
-- proof
  apply StatMech.SLE.ofReal_le_loewnerLifetime hT

/--
[loewnerLifetime_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerLifetime_pos_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  0 < loewnerLifetime W z := by
-- proof
  apply StatMech.SLE.loewnerLifetime_pos hW hz

/--
[ofReal_im_sq_div_eight_le_loewnerLifetime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma ofReal_im_sq_div_eight_le_loewnerLifetime_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ENNReal.ofReal (z.im ^ 2 / 8) ≤ loewnerLifetime W z := by
-- proof
  apply StatMech.SLE.ofReal_im_sq_div_eight_le_loewnerLifetime hW hz

/--
[exists_admissibleDuration_gt_of_ofReal_lt_lifetime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_admissibleDuration_gt_of_ofReal_lt_lifetime_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {t : ℝ}
-- given
  (hlt : ENNReal.ofReal t < loewnerLifetime W z) :
-- imply
  ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
-- proof
  apply StatMech.SLE.exists_admissibleDuration_gt_of_ofReal_lt_lifetime hlt

/--
[isBeforeLoewnerLifetime_iff_exists_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isBeforeLoewnerLifetime_iff_exists_admissible_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {t : ℝ}
-- given
  (ht : 0 ≤ t) :
-- imply
  IsBeforeLoewnerLifetime W z t ↔ ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
-- proof
  apply StatMech.SLE.isBeforeLoewnerLifetime_iff_exists_admissible ht

/--
[loewnerMaximalCurve_eq_forwardSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_eq_forwardSolution_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T t : ℝ}
  {g : LoewnerForwardSolution W z T}
-- given
  (hT : 0 < T)
  (ht : t ∈ Ico (0 : ℝ) T) :
-- imply
  loewnerMaximalCurve W z t = g.curve t := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_eq_forwardSolution hT g ht

/--
[loewnerMaximalCurve_flow_of_forwardSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_flow_of_forwardSolution_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {T s u : ℝ}
  {g : LoewnerForwardSolution W z T}
-- given
  (hT : 0 < T)
  (hs0 : 0 ≤ s)
  (hu0 : 0 ≤ u)
  (hsuT : s + u < T) :
-- imply
  loewnerMaximalCurve W z (s + u) = loewnerMaximalCurve (fun r ↦ W (s + r)) (loewnerMaximalCurve W z s) u := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_flow_of_forwardSolution hT g hs0 hu0 hsuT

/--
[loewnerMaximalCurve_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  loewnerMaximalCurve W z 0 = z := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_zero hW hz

/--
[loewnerMaximalCurve_mem_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_mem_upperHalfPlane_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {t : ℝ}
-- given
  (ht : IsBeforeLoewnerLifetime W z t) :
-- imply
  loewnerMaximalCurve W z t ∈ upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_mem_upperHalfPlane ht

/--
[loewnerMaximalCurve_im_antitoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_im_antitoneOn_eq
  {W : ℝ → ℝ}
  {z : ℂ} :
-- imply
  AntitoneOn (fun t ↦ (loewnerMaximalCurve W z t).im) {t | IsBeforeLoewnerLifetime W z t} := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_im_antitoneOn

/--
[loewnerMaximalCurve_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_hasDerivAt_eq
  {W : ℝ → ℝ}
  {z : ℂ}
  {t : ℝ}
-- given
  (ht0 : 0 < t)
  (htLife : ENNReal.ofReal t < loewnerLifetime W z) :
-- imply
  HasDerivAt (loewnerMaximalCurve W z) (loewnerField W t (loewnerMaximalCurve W z t)) t := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_hasDerivAt ht0 htLife

/--
[loewnerMaximalCurve_hasDerivWithinAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalCurve_hasDerivWithinAt_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  HasDerivWithinAt (loewnerMaximalCurve W z) (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 := by
-- proof
  apply StatMech.SLE.loewnerMaximalCurve_hasDerivWithinAt_zero hW hz

/--
[loewner_maximal_forward_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewner_maximal_forward_exists_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  0 < loewnerLifetime W z ∧ loewnerMaximalCurve W z 0 = z ∧ (∀ t, IsBeforeLoewnerLifetime W z t → loewnerMaximalCurve W z t ∈ upperHalfPlane) ∧ HasDerivWithinAt (loewnerMaximalCurve W z) (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 ∧ ∀ t, 0 < t → ENNReal.ofReal t < loewnerLifetime W z → HasDerivAt (loewnerMaximalCurve W z) (loewnerField W t (loewnerMaximalCurve W z t)) t := by
-- proof
  apply StatMech.SLE.loewner_maximal_forward_exists hW hz

/--
[mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hz : z ∈ upperHalfPlane)
  (hlt : t < z.im ^ 2 / 8) :
-- imply
  z ∈ loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight hW ht hz hlt

/--
[mem_loewnerUnswallowedDomain_of_forwardSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mem_loewnerUnswallowedDomain_of_forwardSolution_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
  {g : LoewnerForwardSolution W z t}
-- given
  (hWcont : Continuous W)
  (ht : 0 ≤ t)
  (hz : z ∈ upperHalfPlane) :
-- imply
  z ∈ loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.mem_loewnerUnswallowedDomain_of_forwardSolution hWcont ht hz g

/--
[mem_loewnerUnswallowedDomain_of_driverBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mem_loewnerUnswallowedDomain_of_driverBarrier_eq
  {W : ℝ → ℝ}
  {t M d : ℝ}
  {z : ℂ}
-- given
  (hWcont : Continuous W)
  (ht : 0 ≤ t)
  (hd : 0 < d)
  (hz : z ∈ upperHalfPlane)
  (hzre : M + d ≤ z.re)
  (hW : ∀ s ∈ Icc (0 : ℝ) t, W s ≤ M) :
-- imply
  z ∈ loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.mem_loewnerUnswallowedDomain_of_driverBarrier hWcont ht hd hz hzre hW

/--
[mem_loewnerUnswallowedDomain_of_driverLowerBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mem_loewnerUnswallowedDomain_of_driverLowerBarrier_eq
  {W : ℝ → ℝ}
  {t m d : ℝ}
  {z : ℂ}
-- given
  (hWcont : Continuous W)
  (ht : 0 ≤ t)
  (hd : 0 < d)
  (hz : z ∈ upperHalfPlane)
  (hzre : z.re ≤ m - d)
  (hW : ∀ s ∈ Icc (0 : ℝ) t, m ≤ W s) :
-- imply
  z ∈ loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.mem_loewnerUnswallowedDomain_of_driverLowerBarrier hWcont ht hd hz hzre hW

/--
[loewnerUnswallowedDomain_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerUnswallowedDomain_nonempty_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  (loewnerUnswallowedDomain W t).Nonempty := by
-- proof
  apply StatMech.SLE.loewnerUnswallowedDomain_nonempty hW ht

/--
[loewnerMaximalMaps_flow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_flow_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {z : ℂ}
-- given
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
-- imply
  loewnerMaximalMaps W (s + u) z = loewnerMaximalMaps (fun r ↦ W (s + r)) u (loewnerMaximalMaps W s z) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_flow hs hu hz

/--
[loewnerMaximalMaps_mem_shiftedUnswallowedDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_mem_shiftedUnswallowedDomain_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {z : ℂ}
-- given
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
-- imply
  loewnerMaximalMaps W s z ∈ loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hz

/--
[mem_loewnerUnswallowedDomain_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma mem_loewnerUnswallowedDomain_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : z ∈ upperHalfPlane) :
-- imply
  z ∈ loewnerUnswallowedDomain W 0 := by
-- proof
  apply StatMech.SLE.mem_loewnerUnswallowedDomain_zero hW hz

/--
[loewnerMaximalMaps_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : z ∈ upperHalfPlane) :
-- imply
  loewnerMaximalMaps W 0 z = z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_zero hW hz

/--
[loewnerMaximalMaps_mem_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_mem_upperHalfPlane_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
-- given
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  loewnerMaximalMaps W t z ∈ upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_mem_upperHalfPlane hz

/--
[loewnerMaximalMaps_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_hasDerivAt_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
-- given
  (ht : 0 < t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  HasDerivAt (fun s ↦ loewnerMaximalMaps W s z) (loewnerField W t (loewnerMaximalMaps W t z)) t := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_hasDerivAt ht hz

/--
[loewnerMaximalMaps_hasDerivWithinAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_hasDerivWithinAt_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : z ∈ upperHalfPlane) :
-- imply
  HasDerivWithinAt (fun s ↦ loewnerMaximalMaps W s z) (loewnerField W 0 (loewnerMaximalMaps W 0 z)) (Ici (0 : ℝ)) 0 := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_hasDerivWithinAt_zero hW hz

/--
[loewnerMaximalMaps_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_injOn_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  InjOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_injOn hW ht

/--
[loewnerMaximalMaps_surjOn_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_surjOn_upperHalfPlane_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  SurjOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_surjOn_upperHalfPlane hW ht

/--
[loewnerMaximalMaps_bijOn_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_bijOn_upperHalfPlane_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  BijOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_bijOn_upperHalfPlane hW ht

/--
[loewnerMaximalMapsInverse_congr_time](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMapsInverse_congr_time_eq
  {W : ℝ → ℝ}
  {s t : ℝ}
-- given
  (hW : Continuous W)
  (hs : 0 ≤ s)
  (ht : 0 ≤ t)
  (hst : s = t) :
-- imply
  loewnerMaximalMapsInverse hW hs = loewnerMaximalMapsInverse hW ht := by
-- proof
  apply StatMech.SLE.loewnerMaximalMapsInverse_congr_time hW hs ht hst

/--
[loewnerMaximalMapsInverse_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMapsInverse_mem_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : y ∈ upperHalfPlane) :
-- imply
  loewnerMaximalMapsInverse hW ht y ∈ loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.loewnerMaximalMapsInverse_mem hW ht hy

/--
[loewnerMaximalMaps_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_inverse_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : y ∈ upperHalfPlane) :
-- imply
  loewnerMaximalMaps W t (loewnerMaximalMapsInverse hW ht y) = y := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_inverse hW ht hy

/--
[eq_loewnerMaximalMapsInverse_of_mapsTo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma eq_loewnerMaximalMapsInverse_of_mapsTo_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {x y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hx : x ∈ loewnerUnswallowedDomain W t)
  (hy : y ∈ upperHalfPlane)
  (hxy : loewnerMaximalMaps W t x = y) :
-- imply
  x = loewnerMaximalMapsInverse hW ht y := by
-- proof
  apply StatMech.SLE.eq_loewnerMaximalMapsInverse_of_mapsTo hW ht hx hy hxy

/--
[exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : 0 < y.im)
  (hlt : t < y.im ^ 2 / 16) :
-- imply
  ∃ inv : ℂ → ℂ, ContinuousOn inv (closedBall y (y.im / 4)) ∧ MapsTo inv (closedBall y (y.im / 4)) (loewnerUnswallowedDomain W t) ∧ ∀ v ∈ closedBall y (y.im / 4), loewnerMaximalMaps W t (inv v) = v := by
-- proof
  apply StatMech.SLE.exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen hW ht hy hlt

/--
[continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : y ∈ upperHalfPlane)
  (hlt : t < y.im ^ 2 / 16) :
-- imply
  ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
-- proof
  apply StatMech.SLE.continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen hW ht hy hlt

/--
[loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z₀ : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hz₀ : 0 < z₀.im)
  (hlt : t < z₀.im ^ 2 / 16) :
-- imply
  ∃ C : ℝ≥0, closedBall z₀ (z₀.im / 4) ⊆ loewnerUnswallowedDomain W t ∧ LipschitzOnWith C (loewnerMaximalMaps W t) (closedBall z₀ (z₀.im / 4)) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen hW ht hz₀ hlt

/--
[continuousAt_loewnerMaximalMaps_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousAt_loewnerMaximalMaps_of_lt_im_sq_div_sixteen_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z₀ : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hz₀ : 0 < z₀.im)
  (hlt : t < z₀.im ^ 2 / 16) :
-- imply
  ContinuousAt (loewnerMaximalMaps W t) z₀ := by
-- proof
  apply StatMech.SLE.continuousAt_loewnerMaximalMaps_of_lt_im_sq_div_sixteen hW ht hz₀ hlt

/--
[loewnerUnswallowedDomain_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerUnswallowedDomain_zero_eq
  {W : ℝ → ℝ}
-- given
  (hW : Continuous W) :
-- imply
  loewnerUnswallowedDomain W 0 = upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerUnswallowedDomain_zero hW

/--
[loewnerMaximalMaps_satisfiesMaximalLoewnerEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_satisfiesMaximalLoewnerEquation_eq
  {W : ℝ → ℝ}
-- given
  (hW : Continuous W) :
-- imply
  SatisfiesMaximalLoewnerEquation W (loewnerUnswallowedDomain W) (loewnerMaximalMaps W) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_satisfiesMaximalLoewnerEquation hW

/--
[loewnerMaximalMaps_regularAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_regularAt_zero_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : z ∈ upperHalfPlane) :
-- imply
  loewnerUnswallowedDomain W 0 ∈ 𝓝 z ∧ ContinuousAt (loewnerMaximalMaps W 0) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_regularAt_zero hW hz

/--
[loewnerUnswallowedDomain_antitoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerUnswallowedDomain_antitoneOn_eq
  {W : ℝ → ℝ} :
-- imply
  AntitoneOn (loewnerUnswallowedDomain W) (Ici (0 : ℝ)) := by
-- proof
  apply StatMech.SLE.loewnerUnswallowedDomain_antitoneOn W

/--
[loewnerUnswallowedDomain_add_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerUnswallowedDomain_add_subset_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
-- given
  (hs : 0 ≤ s)
  (hu : 0 ≤ u) :
-- imply
  loewnerUnswallowedDomain W (s + u) ⊆ loewnerUnswallowedDomain W s ∩ loewnerMaximalMaps W s ⁻¹' loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
-- proof
  apply StatMech.SLE.loewnerUnswallowedDomain_add_subset W hs hu

/--
[loewnerUnswallowedDomain_add_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerUnswallowedDomain_add_eq_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
-- given
  (hs : 0 ≤ s)
  (hu : 0 ≤ u) :
-- imply
  loewnerUnswallowedDomain W (s + u) = loewnerUnswallowedDomain W s ∩ loewnerMaximalMaps W s ⁻¹' loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
-- proof
  apply StatMech.SLE.loewnerUnswallowedDomain_add_eq W hs hu

/--
[continuous_loewnerDriver_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuous_loewnerDriver_shift_eq
  {W : ℝ → ℝ}
  {s : ℝ}
-- given
  (hW : Continuous W) :
-- imply
  Continuous (fun r ↦ W (s + r)) := by
-- proof
  apply StatMech.SLE.continuous_loewnerDriver_shift hW s

/--
[loewnerMaximalMapsInverse_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMapsInverse_add_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hy : y ∈ upperHalfPlane) :
-- imply
  loewnerMaximalMapsInverse hW (add_nonneg hs hu) y = loewnerMaximalMapsInverse hW hs (loewnerMaximalMapsInverse (continuous_loewnerDriver_shift hW s) hu y) := by
-- proof
  apply StatMech.SLE.loewnerMaximalMapsInverse_add hW hs hu hy

/--
[continuousAt_loewnerMaximalMapsInverse_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousAt_loewnerMaximalMapsInverse_add_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hy : y ∈ upperHalfPlane)
  (hfirst : ContinuousAt (loewnerMaximalMapsInverse hW hs) (loewnerMaximalMapsInverse (continuous_loewnerDriver_shift hW s) hu y))
  (hsecond : ContinuousAt (loewnerMaximalMapsInverse (continuous_loewnerDriver_shift hW s) hu) y) :
-- imply
  ContinuousAt (loewnerMaximalMapsInverse hW (add_nonneg hs hu)) y := by
-- proof
  apply StatMech.SLE.continuousAt_loewnerMaximalMapsInverse_add hW hs hu hy hfirst hsecond

/--
[continuousAt_loewnerMaximalMapsInverse_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousAt_loewnerMaximalMapsInverse_steps_eq
  {W : ℝ → ℝ}
  {u : ℝ}
  {n : ℕ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (hu : 0 ≤ u)
  (hy : y ∈ upperHalfPlane)
  (hshort : u < y.im ^ 2 / 16) :
-- imply
  ContinuousAt (loewnerMaximalMapsInverse hW (mul_nonneg (Nat.cast_nonneg n) hu)) y := by
-- proof
  apply StatMech.SLE.continuousAt_loewnerMaximalMapsInverse_steps hW hu n hy hshort

/--
[continuousAt_loewnerMaximalMapsInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousAt_loewnerMaximalMapsInverse_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {y : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hy : y ∈ upperHalfPlane) :
-- imply
  ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
-- proof
  apply StatMech.SLE.continuousAt_loewnerMaximalMapsInverse hW ht hy

/--
[loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hz : z ∈ loewnerUnswallowedDomain W (s + u))
  (hregular : loewnerUnswallowedDomain W s ∈ 𝓝 z ∧ ContinuousAt (loewnerMaximalMaps W s) z)
  (hshort : u < (loewnerMaximalMaps W s z).im ^ 2 / 16) :
-- imply
  loewnerUnswallowedDomain W (s + u) ∈ 𝓝 z ∧ ContinuousAt (loewnerMaximalMaps W (s + u)) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen hW hs hu hz hregular hshort

/--
[loewnerMaximalMaps_regularAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerMaximalMaps_regularAt_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hz : z ∈ loewnerUnswallowedDomain W t) :
-- imply
  loewnerUnswallowedDomain W t ∈ 𝓝 z ∧ ContinuousAt (loewnerMaximalMaps W t) z := by
-- proof
  apply StatMech.SLE.loewnerMaximalMaps_regularAt hW ht hz

/--
[isOpen_loewnerUnswallowedDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isOpen_loewnerUnswallowedDomain_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  IsOpen (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.isOpen_loewnerUnswallowedDomain hW ht

/--
[continuousOn_loewnerMaximalMaps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousOn_loewnerMaximalMaps_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  ContinuousOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.continuousOn_loewnerMaximalMaps hW ht

/--
[continuousOn_loewnerMaximalMapsInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma continuousOn_loewnerMaximalMapsInverse_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  ContinuousOn (loewnerMaximalMapsInverse hW ht) upperHalfPlane := by
-- proof
  apply StatMech.SLE.continuousOn_loewnerMaximalMapsInverse hW ht

/--
[isConnected_loewnerUnswallowedDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isConnected_loewnerUnswallowedDomain_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  IsConnected (loewnerUnswallowedDomain W t) := by
-- proof
  apply StatMech.SLE.isConnected_loewnerUnswallowedDomain hW ht

/--
[isBeforeLoewnerLifetime_add_iff_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isBeforeLoewnerLifetime_add_iff_shifted_eq
  {W : ℝ → ℝ}
  {s u : ℝ}
  {z : ℂ}
-- given
  (hs : 0 ≤ s)
  (hu : 0 ≤ u)
  (hzs : z ∈ loewnerUnswallowedDomain W s) :
-- imply
  IsBeforeLoewnerLifetime W z (s + u) ↔ IsBeforeLoewnerLifetime (fun r ↦ W (s + r)) (loewnerMaximalMaps W s z) u := by
-- proof
  apply StatMech.SLE.isBeforeLoewnerLifetime_add_iff_shifted hs hu hzs

/--
[loewnerSwallowedSet_subset_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_subset_upperHalfPlane_eq
  {W : ℝ → ℝ}
  {t : ℝ} :
-- imply
  loewnerSwallowedSet W t ⊆ upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_subset_upperHalfPlane W t

/--
[loewnerSwallowedSet_relClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_relClosed_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  ∃ C : Set ℂ, IsClosed C ∧ loewnerSwallowedSet W t = C ∩ upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_relClosed hW ht

/--
[upperHalfPlane_diff_loewnerSwallowedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma upperHalfPlane_diff_loewnerSwallowedSet_eq
  {W : ℝ → ℝ}
  {t : ℝ} :
-- imply
  upperHalfPlane \ loewnerSwallowedSet W t = loewnerUnswallowedDomain W t := by
-- proof
  apply StatMech.SLE.upperHalfPlane_diff_loewnerSwallowedSet W t

/--
[isOpen_upperHalfPlane_diff_loewnerSwallowedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isOpen_upperHalfPlane_diff_loewnerSwallowedSet_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  IsOpen (upperHalfPlane \ loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.isOpen_upperHalfPlane_diff_loewnerSwallowedSet hW ht

/--
[isConnected_upperHalfPlane_diff_loewnerSwallowedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma isConnected_upperHalfPlane_diff_loewnerSwallowedSet_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  IsConnected (upperHalfPlane \ loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.isConnected_upperHalfPlane_diff_loewnerSwallowedSet hW ht

/--
[loewnerSwallowedSet_im_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_im_sq_le_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hz : z ∈ loewnerSwallowedSet W t) :
-- imply
  z.im ^ 2 ≤ 8 * t := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_im_sq_le hW ht hz

/--
[exists_loewnerSwallowedSet_re_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma exists_loewnerSwallowedSet_re_bound_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  ∃ R : ℝ, ∀ z ∈ loewnerSwallowedSet W t, := by
-- proof
  apply StatMech.SLE.exists_loewnerSwallowedSet_re_bound hW ht

/--
[loewnerSwallowedSet_isBounded_of_re_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_isBounded_of_re_bound_eq
  {W : ℝ → ℝ}
  {t R : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
-- imply
  Bornology.IsBounded (loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_isBounded_of_re_bound hW ht hre

/--
[loewnerSwallowedSet_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_isBounded_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  Bornology.IsBounded (loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_isBounded hW ht

/--
[loewnerSwallowedSet_isCompactHull_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_isCompactHull_of_bounded_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hbounded : Bornology.IsBounded (loewnerSwallowedSet W t)) :
-- imply
  IsCompactHull (loewnerSwallowedSet W t) where subset := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_isCompactHull_of_bounded hW ht hbounded

/--
[loewnerSwallowedSet_isCompactHull_of_re_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_isCompactHull_of_re_bound_eq
  {W : ℝ → ℝ}
  {t R : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t)
  (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
-- imply
  IsCompactHull (loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_isCompactHull_of_re_bound hW ht hre

/--
[loewnerSwallowedSet_isCompactHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_isCompactHull_eq
  {W : ℝ → ℝ}
  {t : ℝ}
-- given
  (hW : Continuous W)
  (ht : 0 ≤ t) :
-- imply
  IsCompactHull (loewnerSwallowedSet W t) := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_isCompactHull hW ht

/--
[loewnerSwallowedSet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_zero_eq
  {W : ℝ → ℝ}
-- given
  (hW : Continuous W) :
-- imply
  loewnerSwallowedSet W 0 = ∅ := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_zero hW

/--
[loewnerSwallowedSet_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean)
-/
@[path]
private lemma loewnerSwallowedSet_monotoneOn_eq
  {W : ℝ → ℝ} :
-- imply
  MonotoneOn (loewnerSwallowedSet W) (Ici (0 : ℝ)) := by
-- proof
  apply StatMech.SLE.loewnerSwallowedSet_monotoneOn W


-- created on 2026-10-23
