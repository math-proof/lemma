import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
open Real Set Finset Filter Topology StatMech StatMech.OSSS StatMech.OSSS.Integration


/--
[slope_ge_of_deriv_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma slope_ge_of_deriv_ge_eq
  {a b m : ℝ}
  {T T' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt T (T' x) x)
  (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
-- imply
  m * (b - a) ≤ T b - T a := by
-- proof
  apply StatMech.OSSS.Integration.slope_ge_of_deriv_ge a b m hab T T' hd hbound

/--
[logStep_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma logStep_le_eq
  {S f : ℝ}
-- given
  (hS : 0 < S)
  (hf : 0 ≤ f) :
-- imply
  Real.log (S + f) - Real.log S ≤ f / S := by
-- proof
  apply StatMech.OSSS.Integration.logStep_le S f hS hf

/--
[logStep_sum_le_sum_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma logStep_sum_le_sum_deriv_eq
  {fseq fpseq Sig : ℕ → ℝ}
  {n : ℕ}
-- given
  (hSrec : ∀ i, Sig (i + 1) = Sig i + fseq i)
  (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i)
  (hSpos : ∀ i, 1 ≤ i → 0 < Sig i)
  (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i) * fseq i ≤ fpseq i) :
-- imply
  Real.log (Sig (n + 1)) - Real.log (Sig 1) ≤ ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i / (i : ℝ) := by
-- proof
  apply StatMech.OSSS.Integration.logStep_sum_le_sum_deriv fseq fpseq Sig n hSrec hfnn hSpos hdiff

/--
[hasDerivAt_meanLogTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma hasDerivAt_meanLogTerm_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hf : ∀ i, HasDerivAt (fun x => fseq i x) (fpseq i x) x) :
-- imply
  HasDerivAt (fun x => meanLogTerm fseq n x) ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ)) x := by
-- proof
  apply StatMech.OSSS.Integration.hasDerivAt_meanLogTerm fseq fpseq n x hf

/--
[deriv_meanLogTerm_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma deriv_meanLogTerm_lower_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {Sig : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hlogn : 0 < Real.log n)
  (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
  (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
  (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
  (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
-- imply
  (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n ≤ (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ) := by
-- proof
  apply StatMech.OSSS.Integration.deriv_meanLogTerm_lower fseq fpseq Sig n x hlogn hSrec hfnn hSpos hdiff

/--
[integrated_meanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma integrated_meanField_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {Sig : ℕ → ℝ → ℝ}
  {n : ℕ}
  {β' β m : ℝ}
-- given
  (hββ : β' ≤ β)
  (hlogn : 0 < Real.log n)
  (hf : ∀ i x, x ∈ Icc β' β → HasDerivAt (fun x => fseq i x) (fpseq i x) x)
  (hSrec : ∀ i x, Sig (i + 1) x = Sig i x + fseq i x)
  (hfnn : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 ≤ fseq i x)
  (hSpos : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 < Sig i x)
  (hdiff : ∀ i : ℕ, ∀ x, 1 ≤ i → x ∈ Icc β' β → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x)
  (hm : ∀ x ∈ Icc β' β, m ≤ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n) :
-- imply
  (β - β') * m ≤ meanLogTerm fseq n β - meanLogTerm fseq n β' := by
-- proof
  apply StatMech.OSSS.Integration.integrated_meanField fseq fpseq Sig n β' β m hββ hlogn hf hSrec hfnn hSpos hdiff hm

/--
[meanField_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma meanField_limit_eq
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
-- given
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hm : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
-- imply
  (β - β') * m ≤ fβ - fβ' := by
-- proof
  apply StatMech.OSSS.Integration.meanField_limit T mseq β' β fβ fβ' m hTβ hTβ' hm hbound

/--
[meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean)
-/
@[path]
private lemma meanField_lower_eq
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
-- given
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
-- imply
  β - β' ≤ fβ - fβ' := by
-- proof
  apply StatMech.OSSS.Integration.meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound


-- created on 2026-10-23
