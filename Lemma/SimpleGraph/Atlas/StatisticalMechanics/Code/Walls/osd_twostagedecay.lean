import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.osd_twostagedecay
open Real Filter Topology Set Finset StatMech StatMech.Walls


/--
[osd_Sigma_eq_Sig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean)
-/
@[path]
private lemma osd_Sigma_eq_Sig_eq
  {f : ℕ → ℝ → ℝ}
  {n : ℕ}
  {x : ℝ} :
-- imply
  osd_Sigma f n x = StatMech.OSSS.IntegrationSubcritical.Sig f n x := by
-- proof
  apply StatMech.Walls.osd_Sigma_eq_Sig f n x

/--
[osd_two_stage_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean)
-/
@[path]
private lemma osd_two_stage_decay_eq
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
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < osd_Sigma f n x)
  (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
  (hSpoly : ∀ n : ℕ, N ≤ n → osd_Sigma f n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.Walls.osd_two_stage_decay f f' α δ β M N hδ hα hα1 hMnn hN hd hfnn hfM hfmono hSpos hdiff hSpoly

/--
[osd_gronwall_lower_is_dep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean)
-/
@[path]
private lemma osd_gronwall_lower_is_dep_eq
  {a b lam : ℝ}
  {g g' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * g x ≤ g' x) :
-- imply
  Real.exp (lam * (b - a)) * g a ≤ g b := by
-- proof
  apply StatMech.Walls.osd_gronwall_lower_is_dep a b lam hab g g' hd hineq

/--
[osd_stage1_stretched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean)
-/
@[path]
private lemma osd_stage1_stretched_eq
  {f f' : ℕ → ℝ → ℝ}
  {n : ℕ}
  {α δ β M : ℝ}
-- given
  (hn : 1 ≤ n)
  (hδ : 0 < δ)
  (hd : ∀ x ∈ Icc (β - δ) β, HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ x ∈ Icc (β - δ) β, 0 ≤ f n x)
  (hSpos : ∀ x ∈ Icc (β - δ) β, 0 < osd_Sigma f n x)
  (hSpoly : ∀ x ∈ Icc (β - δ) β, osd_Sigma f n x ≤ (n : ℝ) ^ (1 - α))
  (hdiff : ∀ x ∈ Icc (β - δ) β, ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
  (hfb : f n β ≤ M) :
-- imply
  f n (β - δ) ≤ M * Real.exp (-(δ * (n : ℝ) ^ α)) := by
-- proof
  apply StatMech.Walls.osd_stage1_stretched f f' n α δ β M hn hδ hd hfnn hSpos hSpoly hdiff hfb

/--
[osd_stage2_exponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_twostagedecay.lean)
-/
@[path]
private lemma osd_stage2_exponential_eq
  {f f' : ℕ → ℝ → ℝ}
  {n : ℕ}
  {δ Q β M : ℝ}
-- given
  (hδ : 0 < δ)
  (hQ : 0 < Q)
  (hd : ∀ x ∈ Icc (β - 2 * δ) (β - δ), HasDerivAt (f n) (f' n x) x)
  (hfnn : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 ≤ f n x)
  (hSpos : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 < osd_Sigma f n x)
  (hSle : ∀ x ∈ Icc (β - 2 * δ) (β - δ), osd_Sigma f n x ≤ Q)
  (hdiff : ∀ x ∈ Icc (β - 2 * δ) (β - δ), ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
  (hfb : f n (β - δ) ≤ M) :
-- imply
  f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.Walls.osd_stage2_exponential f f' n δ Q β M hδ hQ hd hfnn hSpos hSle hdiff hfb


-- created on 2026-10-23
