import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.HCTensorLib
open Finset Real Set StatMech StatMech.OSSS StatMech.Probability


/--
[htl_cons_quadform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_cons_quadform_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ u v : ℝ} :
-- imply
  (1 - p) * (ptn_kbit p ρ false false * u + ptn_kbit p ρ false true * v) ^ 2 + p * (ptn_kbit p ρ true false * u + ptn_kbit p ρ true true * v) ^ 2 = ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 := by
-- proof
  apply StatMech.Probability.htl_cons_quadform_eq

/--
[htl_pbiasedHCLib_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_pbiasedHCLib_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {u v : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  ((1 - (1 / 2 : ℝ)) * u + (1 / 2) * v) ^ 2 + ρ ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / 2)) * (u - v) ^ 2 ≤ ((1 - (1 / 2 : ℝ)) * |u| ^ (1 + ρ ^ 2) + (1 / 2) * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.htl_pbiasedHCLib_half h0 h1 u v

/--
[htl_lib_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_lib_half_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  PBiasedHCLib (1 / 2) := by
-- proof
  apply StatMech.Probability.htl_lib_half

/--
[htl_tensorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_tensorStep_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2)
  (ih : ∀ g : (Fin n → Bool) → ℝ, ptn_qnorm p 2 (ptn_kop p ρ g) ≤ ptn_qnorm p q g) :
-- imply
  ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.htl_tensorStep hp0 hp1 h0 h1 hqeq H n ih f

/--
[htl_hypercontractivity_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_hypercontractivity_fin_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2) :
-- imply
  ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
-- proof
  apply StatMech.Probability.htl_hypercontractivity_fin hp0 hp1 h0 h1 hqeq H n f

/--
[htl_lowDegreeWeight_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_lowDegreeWeight_fin_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2) :
-- imply
  (∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) ≤ (ptn_qnorm p q f) ^ 2 := by
-- proof
  apply StatMech.Probability.htl_lowDegreeWeight_fin hp0 hp1 h0 h1 hqeq H n f

/--
[htl_lowDegreeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_lowDegreeWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {f : ConfigSpace ι → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2) :
-- imply
  (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) ≤ (ptn_qnorm p q f) ^ 2 := by
-- proof
  apply StatMech.Probability.htl_lowDegreeWeight hp0 hp1 h0 h1 hqeq H f

/--
[htl_perCoord_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_perCoord_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {φ : ConfigSpace ι → Bool}
  {e : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2) ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.htl_perCoord_hc hp0 hp1 h0 h1 hqeq H φ e

/--
[htl_summed_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_summed_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2) :
-- imply
  (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.htl_summed_hc hp0 hp1 h0 h1 hqeq H φ

/--
[htl_capped_hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_capped_hc_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p ρ q : ℝ}
  {H : PBiasedHCLib p}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1)
  (hqeq : q = 1 + ρ ^ 2)
  (hq2 : q ≤ 2) :
-- imply
  (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.htl_capped_hc hp0 hp1 h0 h1 hqeq hq2 H φ

/--
[htl_master_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_master_open_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {H : PBiasedHCLib p}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.htl_master_open hp0 hp1 H φ hu0 hu1

/--
[htl_openResidue_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_openResidue_of_lib_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
-- imply
  frh_openResidue q := by
-- proof
  apply StatMech.Probability.htl_openResidue_of_lib H

/--
[htl_kkl_logGain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_kkl_logGain_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.htl_kkl_logGain H hp hp1 φ

/--
[htl_rhoOptimise_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_rhoOptimise_of_lib_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.htl_rhoOptimise_of_lib H

/--
[htl_kklHC_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_kklHC_of_lib_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {p : ℝ}
-- given
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.htl_kklHC_of_lib H hp hp1

/--
[htl_PBiasedHC_of_lib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_PBiasedHC_of_lib_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : q ≤ 1)
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.htl_PBiasedHC_of_lib hq H

/--
[htl_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_sharpThreshold_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {v₀ L : ℝ}
-- given
  (hq1 : q ≤ 1)
  (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.Probability.htl_sharpThreshold hq1 H A hA hq hv0 hL hhalf hvar hLL'

/--
[htl_kkl_logGain_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_kkl_logGain_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {ι : Type}
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.htl_kkl_logGain_half φ

/--
[htl_lib_rho_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_lib_rho_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + (0 : ℝ) ^ 2 * (p * (1 - p)) * (u - v) ^ 2 ≤ ((1 - p) * |u| ^ (1 + (0:ℝ) ^ 2) + p * |v| ^ (1 + (0:ℝ) ^ 2)) ^ (2 / (1 + (0:ℝ) ^ 2)) := by
-- proof
  apply StatMech.Probability.htl_lib_rho_zero hp0 hp1 u v

/--
[htl_lib_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HCTensorLib.lean)
-/
@[path]
private lemma htl_lib_noncirc_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {H : PBiasedHCLib p}
  {ρ : ℝ}
  {u v : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 ≤ ((1 - p) * |u| ^ (1 + ρ ^ 2) + p * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.htl_lib_noncirc H h0 h1 u v


-- created on 2026-10-23
