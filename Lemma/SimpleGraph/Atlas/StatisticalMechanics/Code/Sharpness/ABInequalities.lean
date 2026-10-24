import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABInequalities
open MeasureTheory Set Finset StatMech StatMech.Sharpness


/--
[pivotalProb_le_of_disjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma pivotalProb_le_of_disjointOccurrence_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B C : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hpiv : {ω | IsPivotal e A ω} ⊆ disjointOccurrence B C) :
-- imply
  pivotalProb (p : ℝ) A e ≤ prob (p : ℝ) B * prob (p : ℝ) C := by
-- proof
  apply StatMech.Sharpness.pivotalProb_le_of_disjointOccurrence hp hA hB hC hpiv

/--
[deriv_prob_le_sum_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma deriv_prob_le_sum_bk_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A : Set (ConfigSpace E)}
  {B C : E → Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : ∀ e, IsIncreasing (B e))
  (hC : ∀ e, IsIncreasing (C e))
  (hpiv : ∀ e, {ω | IsPivotal e A ω} ⊆ disjointOccurrence (B e) (C e)) :
-- imply
  deriv (fun q => prob q A) (p : ℝ) ≤ ∑ e, prob (p : ℝ) (B e) * prob (p : ℝ) (C e) := by
-- proof
  apply StatMech.Sharpness.deriv_prob_le_sum_bk hp hA B C hB hC hpiv

/--
[ab_hu_of_russo_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma ab_hu_of_russo_bk_eq
  [Fintype E]
  [DecidableEq E]
  {s : Finset ι}
  {dMdβ dMdh M J : ℝ}
  {Jcoef infl piv : ι → ℝ}
-- given
  (hMnn : 0 ≤ M)
  (hJnn : ∀ e ∈ s, 0 ≤ Jcoef e)
  (hinflnn : ∀ e ∈ s, 0 ≤ infl e)
  (hrusso : dMdβ = ∑ e ∈ s, piv e)
  (hbk : ∀ e ∈ s, piv e ≤ Jcoef e * M * infl e)
  (hJsum : ∑ e ∈ s, Jcoef e = J)
  (hinfl_eq : ∑ e ∈ s, infl e = dMdh)
  (hJle : ∀ e ∈ s, Jcoef e ≤ J)
  (hJ0 : 0 ≤ J)
  (hdMdh_nn : 0 ≤ dMdh) :
-- imply
  dMdβ ≤ J * (M * dMdh) := by
-- proof
  apply StatMech.Sharpness.ab_hu_of_russo_bk s dMdβ dMdh M J Jcoef infl piv hMnn hJnn hinflnn hrusso hbk hJsum hinfl_eq hJle hJ0 hdMdh_nn

/--
[ab_eq6_of_russo_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma ab_eq6_of_russo_meanfield_eq
  [Fintype E]
  [DecidableEq E]
  {β dMdβ M pivsum : ℝ}
-- given
  (hβ : 0 < β)
  (hrusso : dMdβ = pivsum)
  (hlb : (1 / β) * (1 - M) ≤ pivsum) :
-- imply
  1 - M ≤ β * dMdβ := by
-- proof
  apply StatMech.Sharpness.ab_eq6_of_russo_meanfield β dMdβ M pivsum hβ hrusso hlb

/--
[aizenmanBarskyInequality_of_russo_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma aizenmanBarskyInequality_of_russo_bk_eq
  [Fintype E]
  [DecidableEq E]
  {M : ℝ → ℝ → ℝ}
  {J : ℝ}
-- given
  (hJ0 : 0 ≤ J)
  (hbuild : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ), (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧ (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧ (∑ e ∈ s, Jcoef e = J) ∧ (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧ (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h)) :
-- imply
  AizenmanBarskyInequality M J := by
-- proof
  apply StatMech.Sharpness.aizenmanBarskyInequality_of_russo_bk M J hJ0 hbuild

/--
[eq6_of_russo_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma eq6_of_russo_meanfield_eq
  [Fintype E]
  [DecidableEq E]
  {M : ℝ → ℝ → ℝ}
  {βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hbuild : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ, (deriv (fun β => M β h) βc = pivsum) ∧ ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
-- imply
  ∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc := by
-- proof
  apply StatMech.Sharpness.eq6_of_russo_meanfield M βc hβc hbuild

/--
[ab_inequalities_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalities.lean)
-/
@[path]
private lemma ab_inequalities_discharged_eq
  [Fintype E]
  [DecidableEq E]
  {M : ℝ → ℝ → ℝ}
  {J βc : ℝ}
-- given
  (hJ0 : 0 ≤ J)
  (hβc : 0 < βc)
  (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ), (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧ (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧ (∑ e ∈ s, Jcoef e = J) ∧ (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧ (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
  (h6 : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ, (deriv (fun β => M β h) βc = pivsum) ∧ ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
-- imply
  AizenmanBarskyInequality M J ∧ (∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc) := by
-- proof
  apply StatMech.Sharpness.ab_inequalities_discharged M J βc hJ0 hβc hhu h6


-- created on 2026-10-23
