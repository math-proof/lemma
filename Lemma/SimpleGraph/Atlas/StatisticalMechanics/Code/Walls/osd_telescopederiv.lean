import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.osd_telescopederiv
open Real Set Finset StatMech StatMech.Walls


/--
[osd_logStep_sum_le_sum_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_telescopederiv.lean)
-/
@[path]
private lemma osd_logStep_sum_le_sum_deriv_eq
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
  apply StatMech.Walls.osd_logStep_sum_le_sum_deriv fseq fpseq Sig n hSrec hfnn hSpos hdiff

/--
[osd_hasDerivAt_meanLogTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_telescopederiv.lean)
-/
@[path]
private lemma osd_hasDerivAt_meanLogTerm_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hf : ∀ i x, HasDerivAt (fun x => fseq i x) (fpseq i x) x) :
-- imply
  HasDerivAt (fun x => osd_meanLogTerm fseq n x) ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ)) x := by
-- proof
  apply StatMech.Walls.osd_hasDerivAt_meanLogTerm fseq fpseq n x hf

/--
[osd_telescope_deriv_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_telescopederiv.lean)
-/
@[path]
private lemma osd_telescope_deriv_value_eq
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
  apply StatMech.Walls.osd_telescope_deriv_value fseq fpseq Sig n x hlogn hSrec hfnn hSpos hdiff

/--
[osd_telescope_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_telescopederiv.lean)
-/
@[path]
private lemma osd_telescope_deriv_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {Sig : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hlogn : 0 < Real.log n)
  (hf : ∀ i x, HasDerivAt (fun x => fseq i x) (fpseq i x) x)
  (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
  (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
  (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
  (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
-- imply
  ∃ Tn' : ℝ, HasDerivAt (fun y => osd_meanLogTerm fseq n y) Tn' x ∧ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n ≤ Tn' := by
-- proof
  apply StatMech.Walls.osd_telescope_deriv fseq fpseq Sig n x hlogn hf hSrec hfnn hSpos hdiff


-- created on 2026-10-23
