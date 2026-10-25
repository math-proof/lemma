import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.IntegrationSubcritical
open Real Filter Topology Set Finset Asymptotics StatMech StatMech.OSSS StatMech.OSSS.IntegrationSubcritical


/--
[isc_gronwall_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean)
-/
@[path]
private lemma isc_gronwall_lower_eq
  {a b lam : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
-- imply
  Real.exp (lam * (b - a)) * f a ≤ f b := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_gronwall_lower a b lam hab f f' hd hineq

/--
[isc_gronwall_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean)
-/
@[path]
private lemma isc_gronwall_decay_eq
  {a b lam M : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x)
  (hfb : f b ≤ M) :
-- imply
  f a ≤ M * Real.exp (-(lam * (b - a))) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_gronwall_decay a b lam M hab f f' hd hineq hfb

/--
[isc_summable_stretched_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean)
-/
@[path]
private lemma isc_summable_stretched_exp_eq
  {α δ : ℝ}
-- given
  (hα : 0 < α)
  (hδ : 0 < δ) :
-- imply
  Summable (fun n : ℕ => Real.exp (-(δ * (n : ℝ) ^ α))) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_summable_stretched_exp α δ hα hδ

/--
[isc_partial_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean)
-/
@[path]
private lemma isc_partial_sum_le_eq
  {g b : ℕ → ℝ}
  {M : ℝ}
  {N n : ℕ}
-- given
  (hgM : ∀ k, g k ≤ M)
  (hMnn : 0 ≤ M)
  (hbnn : ∀ k, 0 ≤ b k)
  (hbsum : Summable b)
  (hgb : ∀ k, N ≤ k → g k ≤ b k) :
-- imply
  ∑ k ∈ Finset.range n, g k ≤ (N : ℝ) * M + ∑' k, b k := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_partial_sum_le g b M N n hgM hMnn hbnn hbsum hgb

/--
[isc_rate_weaken](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcritical.lean)
-/
@[path]
private lemma isc_rate_weaken_eq
  {n : ℕ}
  {Sig fp fnx Q : ℝ}
-- given
  (hSig : 0 < Sig)
  (hSigle : Sig ≤ Q)
  (hfnn : 0 ≤ fnx)
  (hdi : ((n : ℝ) / Sig) * fnx ≤ fp) :
-- imply
  ((n : ℝ) / Q) * fnx ≤ fp := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_rate_weaken n Sig fp fnx Q hSig hSigle hfnn hdi


-- created on 2026-10-23
