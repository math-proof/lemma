import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
open MeasureTheory Set Finset StatMech StatMech.Sharpness


/--
[pivotalProb_le_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma pivotalProb_le_union_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B₁ C₁ B₂ C₂ : Set (ConfigSpace E)}
  {e : E}
-- given
  (hp : p ≤ 1)
  (hB₁ : IsIncreasing B₁)
  (hC₁ : IsIncreasing C₁)
  (hB₂ : IsIncreasing B₂)
  (hC₂ : IsIncreasing C₂)
  (hpiv : {ω | IsPivotal e A ω} ⊆ disjointOccurrence B₁ C₁ ∪ disjointOccurrence B₂ C₂) :
-- imply
  pivotalProb (p : ℝ) A e ≤ prob (p : ℝ) B₁ * prob (p : ℝ) C₁ + prob (p : ℝ) B₂ * prob (p : ℝ) C₂ := by
-- proof
  apply StatMech.Sharpness.pivotalProb_le_union hp hB₁ hC₁ hB₂ hC₂ hpiv

/--
[pivotalProb_connEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma pivotalProb_connEvent_le_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {p : ℝ≥0}
  {G : SimpleGraph V}
  {A : Set V}
  {u : V}
  {B : Set V}
  {x y : V}
-- given
  (hp : p ≤ 1)
  (hu : u ∈ A)
  (hx : x ∈ A)
  (hy : y ∈ A) :
-- imply
  pivotalProb (p : ℝ) (connEvent G A u B) s(x, y) ≤ prob (p : ℝ) (connEvent G A u {x}) * prob (p : ℝ) (connEvent G A y B) + prob (p : ℝ) (connEvent G A u {y}) * prob (p : ℝ) (connEvent G A x B) := by
-- proof
  apply StatMech.Sharpness.pivotalProb_connEvent_le hp G A u B x y hu hx hy

/--
[deriv_prob_connEvent_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma deriv_prob_connEvent_le_sum_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {p : ℝ≥0}
  {G : SimpleGraph V}
  {A : Set V}
  {u : V}
  {B : Set V}
  {bnd : Sym2 V → ℝ}
-- given
  (hp : p ≤ 1)
  (hbnd : ∀ e, pivotalProb (p : ℝ) (connEvent G A u B) e ≤ bnd e) :
-- imply
  deriv (fun q => prob q (connEvent G A u B)) (p : ℝ) ≤ ∑ e, bnd e := by
-- proof
  apply StatMech.Sharpness.deriv_prob_connEvent_le_sum hp G A u B bnd hbnd

/--
[aizenmanBarsky_of_geometricCore_and_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma aizenmanBarsky_of_geometricCore_and_inputs_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {M : ℝ → ℝ → ℝ}
  {J : ℝ}
-- given
  (hJ0 : 0 ≤ J)
  (hbuild : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ), (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧ (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧ (∑ e ∈ s, Jcoef e = J) ∧ (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧ (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h)) :
-- imply
  AizenmanBarskyInequality M J := by
-- proof
  apply StatMech.Sharpness.aizenmanBarsky_of_geometricCore_and_inputs M J hJ0 hbuild

/--
[ab_perco_meanfield_sqrt_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma ab_perco_meanfield_sqrt_of_core_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {M : ℝ → ℝ → ℝ}
  {J βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hJ : 0 < J)
  (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ), (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧ (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧ (∑ e ∈ s, Jcoef e = J) ∧ (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧ (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun h => M βc h) h)
  (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv (fun h => M βc h) h)
  (hmnn : ∀ h, 0 ≤ M βc h)
  (hm0 : M βc 0 = 0)
  (h6 : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ, (deriv (fun β => M β h) βc = pivsum) ∧ ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4), c * Real.sqrt h ≤ M βc h := by
-- proof
  apply StatMech.Sharpness.ab_perco_meanfield_sqrt_of_core M J βc hβc hJ hhu hdiff hmono hmnn hm0 h6

/--
[ab_perco_meanfield_sqrt_of_core_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarskyUncond.lean)
-/
@[path]
private lemma ab_perco_meanfield_sqrt_of_core_physical_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {M : ℝ → ℝ → ℝ}
  {J βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hJ : 0 < J)
  (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ), (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧ (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧ (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧ (∑ e ∈ s, Jcoef e = J) ∧ (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧ (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
  (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ (fun t => M βc t) h)
  (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv (fun t => M βc t) h)
  (hcont0 : ContinuousWithinAt (fun t => M βc t) (Ici (0 : ℝ)) 0)
  (hmnn : ∀ h, 0 ≤ M βc h)
  (hm0 : M βc 0 = 0)
  (h6 : ∀ h ∈ Ioi (0 : ℝ), ∃ pivsum : ℝ, (deriv (fun β => M β h) βc = pivsum) ∧ ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4), c * Real.sqrt h ≤ M βc h := by
-- proof
  apply StatMech.Sharpness.ab_perco_meanfield_sqrt_of_core_physical M J βc hβc hJ hhu hdiff hmono hcont0 hmnn hm0 h6


-- created on 2026-10-23
