import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry9Zetaeven
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry10Zetaviabernoulli (chapter7Admissible chapter7PowerDifferenceTerm)
open Entry8Bernoullibound (chapter7BernoulliPolynomial chapter7IntegerPhi)
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry9Zetaeven


/--
[ramanujan_part1_ch7_entry9_zetaeven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry9Zetaeven.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry9_zetaeven_eq
  {phi psi : ℂ → ℂ → ℂ}
-- given
  (hphi_entire : ∀ x, chapter7Admissible x → Differentiable ℂ (fun r : ℂ => phi r x))
  (hpsi_entire : ∀ x, chapter7Admissible x → Differentiable ℂ (fun r : ℂ => psi r x))
  (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
  (hpsi_series : ∀ r x, r.re < 0 → chapter7Admissible x → HasSum (chapter7PowerDifferenceTerm r x) (psi r x)) :
-- imply
  (∀ x, chapter7Admissible x → ∀ r, phi r x = psi r x) ∧
    (∀ m : ℕ, ∀ x, chapter7Admissible x →
    phi m x = chapter7IntegerPhi m x ∧
    psi m x = chapter7IntegerPhi m x) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry9Zetaeven.ramanujan_part1_ch7_entry9_zetaeven phi psi hphi_entire hpsi_entire hphi_series hpsi_series


-- created on 2026-10-20
