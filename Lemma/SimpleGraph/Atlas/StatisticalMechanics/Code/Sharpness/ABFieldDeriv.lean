import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABFieldDeriv.Part3
open MeasureTheory Set Finset Function StatMech StatMech.Sharpness


/--
[configWeightV_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma configWeightV_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  configWeightV p ω = edgeWeightV p ω e * weightOffV p e ω := by
-- proof
  apply StatMech.Sharpness.configWeightV_eq p e ω

/--
[weightOffV_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma weightOffV_congr_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {e : E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e', e' ≠ e → ω e' = ω' e') :
-- imply
  weightOffV p e ω = weightOffV p e ω' := by
-- proof
  apply StatMech.Sharpness.weightOffV_congr p e h

/--
[weightOffV_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma weightOffV_update_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {e : E}
  {t : ℝ}
  {ω : ConfigSpace E} :
-- imply
  weightOffV (Function.update p e t) e ω = weightOffV p e ω := by
-- proof
  apply StatMech.Sharpness.weightOffV_update p e t ω

/--
[probV_update_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma probV_update_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {e₀ : E}
  {t : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  probV (Function.update p e₀ t) A = ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω) := by
-- proof
  apply StatMech.Sharpness.probV_update_eq p e₀ t A

/--
[hasDerivAt_singleEdgeFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma hasDerivAt_singleEdgeFactor_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace E}
  {e₀ : E}
  {t : ℝ} :
-- imply
  HasDerivAt (fun t => if ω e₀ then t else 1 - t) (if ω e₀ then (1 : ℝ) else -1) t := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_singleEdgeFactor ω e₀ t

/--
[abfd_russo_per_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma abfd_russo_per_eta_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {e₀ : E}
  {ωt ωf : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (hwo : weightOffV p e₀ ωt = weightOffV p e₀ ωf)
  (hto : setOpen e₀ ωt = ωt)
  (htc : setClosed e₀ ωt = ωf)
  (ht : ωt e₀ = true)
  (hf : ωf e₀ = false) :
-- imply
  {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeightV p ωt + {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeightV p ωf = A.indicator (fun _ => (1 : ℝ)) ωt * ((if ωt e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωt) + A.indicator (fun _ => (1 : ℝ)) ωf * ((if ωf e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωf) := by
-- proof
  apply StatMech.Sharpness.abfd_russo_per_eta p A hA e₀ ωt ωf hwo hto htc ht hf

/--
[abfd_russo_per_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma abfd_russo_per_edge_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {e₀ : E}
-- given
  (hA : IsIncreasing A) :
-- imply
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω) = pivotalProbV p A e₀ := by
-- proof
  apply StatMech.Sharpness.abfd_russo_per_edge p A hA e₀

/--
[hasDerivAt_probV_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma hasDerivAt_probV_single_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {e₀ : E}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun t => probV (Function.update p e₀ t) A) (pivotalProbV p A e₀) (p e₀) := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_probV_single p A hA e₀

/--
[configWeightV_paramOn_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma configWeightV_paramOn_factor_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {ω : ConfigSpace E}
  {c : ℝ} :
-- imply
  configWeightV (paramOn s c p) ω = (∏ e ∈ s, (if ω e then c else 1 - c)) * ∏ e ∈ univ \ s, (if ω e then p e else 1 - p e) := by
-- proof
  apply StatMech.Sharpness.configWeightV_paramOn_factor s p ω c

/--
[weightOffV_paramOn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma weightOffV_paramOn_mem_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {ω : ConfigSpace E}
  {c : ℝ}
  {e : E}
-- given
  (he : e ∈ s) :
-- imply
  weightOffV (paramOn s c p) e ω = (∏ j ∈ s.erase e, (if ω j then c else 1 - c)) * ∏ j ∈ univ \ s, (if ω j then p j else 1 - p j) := by
-- proof
  apply StatMech.Sharpness.weightOffV_paramOn_mem s p ω c he

/--
[hasDerivAt_probV_paramOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma hasDerivAt_probV_paramOn_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {c : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun c => probV (paramOn s c p) A) (∑ e ∈ s, pivotalProbV (paramOn s c p) A e) c := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_probV_paramOn s p A hA c

/--
[configWeightV_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma configWeightV_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  0 ≤ configWeightV p ω := by
-- proof
  apply StatMech.Sharpness.configWeightV_nonneg p hp ω

/--
[pivotalProbV_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma pivotalProbV_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  0 ≤ pivotalProbV p A e := by
-- proof
  apply StatMech.Sharpness.pivotalProbV_nonneg p hp A e

/--
[hasDerivAt_qField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma hasDerivAt_qField_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (h : ℝ) :
-- imply
  HasDerivAt qField (Real.exp (-h)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_qField h

/--
[qField_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma qField_mem_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ qField h ∧ qField h ≤ 1 := by
-- proof
  apply StatMech.Sharpness.qField_mem h hh

/--
[hasDerivAt_field_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma hasDerivAt_field_profile_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (h : ℝ) :
-- imply
  HasDerivAt (fun h => probV (paramOn s (qField h) p) A) ((∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e) * Real.exp (-h)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_field_profile s p A hA h

/--
[deriv_field_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma deriv_field_profile_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (h : ℝ) :
-- imply
  deriv (fun h => probV (paramOn s (qField h) p) A) h = ∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h) := by
-- proof
  apply StatMech.Sharpness.deriv_field_profile s p A hA h

/--
[abfd_field_influence_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma abfd_field_influence_sum_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
  (hA : IsIncreasing A)
  (h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  let infl := fun e => pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h) (∑ e ∈ s, infl e = deriv (fun h => probV (paramOn s (qField h) p) A) h) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (0 ≤ deriv (fun h => probV (paramOn s (qField h) p) A) h) := by
-- proof
  apply StatMech.Sharpness.abfd_field_influence_sum s p hp A hA h hh

/--
[abfd_aizenmanBarsky_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma abfd_aizenmanBarsky_of_core_eq
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : ℝ → E → ℝ}
  {A : Set (ConfigSpace E)}
  {J : ℝ}
  {Jcoef : E → ℝ}
  {piv : ℝ → ℝ → E → ℝ}
  {M : ℝ → ℝ → ℝ}
-- given
  (hA : IsIncreasing A)
  (hJ0 : 0 ≤ J)
  (hJnn : ∀ e ∈ s, 0 ≤ Jcoef e)
  (hJle : ∀ e ∈ s, Jcoef e ≤ J)
  (hJsum : ∑ e ∈ s, Jcoef e = J)
  (hM : M = fun β h => probV (paramOn s (qField h) (p β)) A)
  (hMnn : ∀ β h, 0 ≤ M β h)
  (hβrusso : ∀ β h, deriv (fun β => M β h) β = ∑ e ∈ s, piv β h e)
  (hbk : ∀ β h, ∀ e ∈ s, piv β h e ≤ Jcoef e * M β h * (pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)))
  (hfield_nn : ∀ β h, (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)) ∧ (0 ≤ deriv (fun h => M β h) h)) :
-- imply
  AizenmanBarskyInequality M J := by
-- proof
  apply StatMech.Sharpness.abfd_aizenmanBarsky_of_core s p A hA J hJ0 Jcoef hJnn hJle hJsum piv M hM hMnn hβrusso hbk hfield_nn

/--
[abfd_hfield_nn_eq_M2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean)
-/
@[path]
private lemma abfd_hfield_nn_eq_M2_eq
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {s : Finset E}
  {p : ℝ → E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hp : ∀ β e, 0 ≤ p β e ∧ p β e ≤ 1)
  (β h : ℝ)
  (hh : 0 ≤ h) :
-- imply
  (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)) ∧ (0 ≤ deriv (fun h => probV (paramOn s (qField h) (p β)) A) h) := by
-- proof
  apply StatMech.Sharpness.abfd_hfield_nn_eq_M2 s p A hA hp β h hh


-- created on 2026-10-23
