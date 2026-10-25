import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[isingExp3_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f g k : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b c => f a * g b * k c) = isingExpectation G β h f * isingExpectation G β h g * isingExpectation G β h k := by
-- proof
  apply StatMech.Ising.isingExp3_factor G β h f g k

/--
[isingExp3_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun _ _ _ => (1 : ℝ)) = 1 := by
-- proof
  apply StatMech.Ising.isingExp3_one G β h

/--
[isingExp3_factor_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_c_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun _ _ c => k c) = isingExpectation G β h k := by
-- proof
  apply StatMech.Ising.isingExp3_factor_c G β h k

/--
[isingExp3_factor_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_b_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {g : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun _ b _ => g b) = isingExpectation G β h g := by
-- proof
  apply StatMech.Ising.isingExp3_factor_b G β h g

/--
[isingExp3_factor_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_a_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a _ _ => f a) = isingExpectation G β h f := by
-- proof
  apply StatMech.Ising.isingExp3_factor_a G β h f

/--
[isingExp3_factor_ab](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_ab_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f g : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b _ => f a * g b) = isingExpectation G β h f * isingExpectation G β h g := by
-- proof
  apply StatMech.Ising.isingExp3_factor_ab G β h f g

/--
[isingExp3_factor_ac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_ac_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f k : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a _ c => f a * k c) = isingExpectation G β h f * isingExpectation G β h k := by
-- proof
  apply StatMech.Ising.isingExp3_factor_ac G β h f k

/--
[isingExp3_factor_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_factor_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {g k : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun _ b c => g b * k c) = isingExpectation G β h g * isingExpectation G β h k := by
-- proof
  apply StatMech.Ising.isingExp3_factor_bc G β h g k

/--
[isingExp3_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F₁ F₂ : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b c => F₁ a b c + F₂ a b c) = isingExp3 G β h F₁ + isingExp3 G β h F₂ := by
-- proof
  apply StatMech.Ising.isingExp3_add G β h F₁ F₂

/--
[isingExp3_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : ℝ}
  {F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b c => r * F a b c) = r * isingExp3 G β h F := by
-- proof
  apply StatMech.Ising.isingExp3_const_mul G β h r F

/--
[dvar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma dvar_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c : ConfigSpace V}
  {w : V} :
-- imply
  dvar a b c w = spin b w + spin c w - 2 * spin a w := by
-- proof
  apply StatMech.Ising.dvar_apply G a b c w

/--
[isingExp3_eq_iterated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_eq_iterated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h F = isingExpectation G β h (fun a => isingExpectation G β h (fun b => isingExpectation G β h (fun c => F a b c))) := by
-- proof
  apply StatMech.Ising.isingExp3_eq_iterated G β h F

/--
[isingExp3_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp3_finset_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : Finset ι}
  {F : ι → ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b c => ∑ i ∈ s, F i a b c) = ∑ i ∈ s, isingExp3 G β h (F i) := by
-- proof
  apply StatMech.Ising.isingExp3_finset_sum G β h s F

/--
[ghsDV_three_replica_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_three_replica_expand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) = (-6) * (isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x * spin s y) - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h (fun s => spin s y) - isingExpectation G β h (fun s => spin s o * spin s y) * isingExpectation G β h (fun s => spin s x) + 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y)) := by
-- proof
  apply StatMech.Ising.ghsDV_three_replica_expand G β h o x y

/--
[ghsDV_ursell_eq_three_replica](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_ursell_eq_three_replica_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) = (-(1/6)) * isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
-- proof
  apply StatMech.Ising.ghsDV_ursell_eq_three_replica G β h o x y

/--
[ghsDV_ghs_iff_three_replica_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_ghs_iff_three_replica_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) ↔ 0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
-- proof
  apply StatMech.Ising.ghsDV_ghs_iff_three_replica_nonneg G β h o x y

/--
[isingExp2_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp2_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f g : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h (fun a b => f a * g b) = isingExpectation G β h f * isingExpectation G β h g := by
-- proof
  apply StatMech.Ising.isingExp2_factor G β h f g

/--
[isingExp2_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp2_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F₁ F₂ : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h (fun a b => F₁ a b + F₂ a b) = isingExp2 G β h F₁ + isingExp2 G β h F₂ := by
-- proof
  apply StatMech.Ising.isingExp2_add G β h F₁ F₂

/--
[isingExp2_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp2_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : ℝ}
  {F : ConfigSpace V → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h (fun a b => r * F a b) = r * isingExp2 G β h F := by
-- proof
  apply StatMech.Ising.isingExp2_const_mul G β h r F

/--
[isingExp2_factor_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp2_factor_a_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h (fun a _ => f a) = isingExpectation G β h f := by
-- proof
  apply StatMech.Ising.isingExp2_factor_a G β h f

/--
[isingExp2_factor_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma isingExp2_factor_b_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {g : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExp2 G β h (fun _ b => g b) = isingExpectation G β h g := by
-- proof
  apply StatMech.Ising.isingExp2_factor_b G β h g

/--
[ghsDV_cov2_eq_two_uu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_cov2_eq_two_uu_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ) :
-- imply
  cov2 G β h o x = 2 * isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
-- proof
  apply StatMech.Ising.ghsDV_cov2_eq_two_uu G β h o x

/--
[ghsDV_uu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_uu_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x) :
-- imply
  0 ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
-- proof
  apply StatMech.Ising.ghsDV_uu_nonneg G β h hβ hh o x hox

/--
[ghsDV_onePt_eq_tt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_onePt_eq_tt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  onePt G β h o = isingExp2 G β h (fun a b => tvar a b o) := by
-- proof
  apply StatMech.Ising.ghsDV_onePt_eq_tt G β h o

/--
[ghsDV_tt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_tt_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExp2 G β h (fun a b => tvar a b o) := by
-- proof
  apply StatMech.Ising.ghsDV_tt_nonneg G β h hβ hh o

/--
[ghsDV_of_three_replica_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean)
-/
@[path]
private lemma ghsDV_of_three_replica_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hsign : ∀ e ∈ G.edgeFinset, ∀ x y : V, e = s(x, y) → 0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Ising.ghsDV_of_three_replica_nonneg G β h o hsign


-- created on 2026-10-23
