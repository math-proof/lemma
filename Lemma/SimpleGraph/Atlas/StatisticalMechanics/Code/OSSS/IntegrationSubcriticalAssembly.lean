import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.IntegrationSubcriticalAssembly
open Real Filter Topology Set Finset StatMech StatMech.OSSS StatMech.OSSS.IntegrationSubcritical


/--
[isc_Sig_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_Sig_succ_eq
  {f : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ} :
-- imply
  Sig f (n + 1) x = Sig f n x + f n x := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_Sig_succ f n x

/--
[isc_Sig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_Sig_mono_eq
  {f : ℕ → ℝ → ℝ}
  {n : ℕ}
  {y x : ℝ}
-- given
  (hyx : y ≤ x)
  (hf : ∀ k, f k y ≤ f k x) :
-- imply
  Sig f n y ≤ Sig f n x := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_Sig_mono f n hyx hf

/--
[isc_rate_weaken_stretched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_rate_weaken_stretched_eq
  {n : ℕ}
  {α Sigx fp fnx : ℝ}
-- given
  (hn : 1 ≤ n)
  (hSig : 0 < Sigx)
  (hSigle : Sigx ≤ (n : ℝ) ^ (1 - α))
  (hfnn : 0 ≤ fnx)
  (hdi : ((n : ℝ) / Sigx) * fnx ≤ fp) :
-- imply
  ((n : ℝ) ^ α) * fnx ≤ fp := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_rate_weaken_stretched n α Sigx fp fnx hn hSig hSigle hfnn hdi

/--
[isc_stretched_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_stretched_decay_eq
  {f f' : ℕ → ℝ → ℝ}
  {n : ℕ}
  {α δ β M : ℝ}
-- given
  (hn : 1 ≤ n)
  (hδ : 0 < δ)
  (hd : ∀ x ∈ Icc (β - δ) β, HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ x ∈ Icc (β - δ) β, 0 ≤ f n x)
  (hSpos : ∀ x ∈ Icc (β - δ) β, 0 < Sig f n x)
  (hSpoly : ∀ x ∈ Icc (β - δ) β, Sig f n x ≤ (n : ℝ) ^ (1 - α))
  (hdiff : ∀ x ∈ Icc (β - δ) β, ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
  (hfb : f n β ≤ M) :
-- imply
  f n (β - δ) ≤ M * Real.exp (-(δ * (n : ℝ) ^ α)) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_stretched_decay f f' n α δ β M hn hδ hd hfnn hSpos hSpoly hdiff hfb

/--
[isc_Sigma_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_Sigma_bound_eq
  {f : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N n : ℕ}
-- given
  (hMnn : 0 ≤ M)
  (hα : 0 < α)
  (hδ : 0 < δ)
  (hfM : ∀ k, f k (β - δ) ≤ M)
  (hstretch : ∀ k, N ≤ k → f k (β - δ) ≤ M * Real.exp (-(δ * (k : ℝ) ^ α))) :
-- imply
  Sig f n (β - δ) ≤ (N : ℝ) * M + ∑' k : ℕ, M * Real.exp (-(δ * (k : ℝ) ^ α)) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_Sigma_bound f α δ β M N n hMnn hα hδ hfM hstretch

/--
[isc_stage2_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_stage2_decay_eq
  {f f' : ℕ → ℝ → ℝ}
  {n : ℕ}
  {δ Q β M : ℝ}
-- given
  (hδ : 0 < δ)
  (hQ : 0 < Q)
  (hd : ∀ x ∈ Icc (β - 2 * δ) (β - δ), HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 ≤ f n x)
  (hSpos : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 < Sig f n x)
  (hSle : ∀ x ∈ Icc (β - 2 * δ) (β - δ), Sig f n x ≤ Q)
  (hdiff : ∀ x ∈ Icc (β - 2 * δ) (β - δ), ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
  (hfb : f n (β - δ) ≤ M) :
-- imply
  f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_stage2_decay f f' n δ Q β M hδ hQ hd hfnn hSpos hSle hdiff hfb

/--
[isc_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/IntegrationSubcriticalAssembly.lean)
-/
@[path]
private lemma isc_subcritical_decay_eq
  {f f' : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ f n x)
  (hfM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, f n x ≤ M)
  (hfmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → f k y ≤ f k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig f n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / Sig f n x) * f n x ≤ f' n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig f n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.OSSS.IntegrationSubcritical.isc_subcritical_decay f f' α δ β M N hδ hα hα1 hMnn hN hd hfnn hfM hfmono hSpos hdiff hSpoly


-- created on 2026-10-23
