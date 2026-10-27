import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[ghsThreePoint_eq_ursell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma ghsThreePoint_eq_ursell_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x * spin s y) - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h (fun s => spin s y) - isingExpectation G β h (fun s => spin s o * spin s y) * isingExpectation G β h (fun s => spin s x) + 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Ising.ghsThreePoint_eq_ursell G β h o x y

/--
[expectation_spin_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma expectation_spin_mul_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s x * spin s x) = 1 := by
-- proof
  apply StatMech.Ising.expectation_spin_mul_self G β h x

/--
[expectation_spin_self_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma expectation_spin_self_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s x * (spin s x * spin s y)) = isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Ising.expectation_spin_self_mul G β h x y

/--
[cov2_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma cov2_nonneg_eq
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
  0 ≤ cov2 G β h o x := by
-- proof
  apply StatMech.Ising.cov2_nonneg G β h hβ hh o x hox

/--
[ghs_degenerate_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma ghs_degenerate_diff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h x s(x, y) - ghsBoundSym G β h x s(x, y) = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
-- proof
  apply StatMech.Ising.ghs_degenerate_diff G β h x y

/--
[ghs_degenerate_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma ghs_degenerate_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  cov3sym G β h x s(x, y) ≤ ghsBoundSym G β h x s(x, y) := by
-- proof
  apply StatMech.Ising.ghs_degenerate_left G β h hβ hh x y hxy

/--
[ghs_degenerate_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma ghs_degenerate_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  cov3sym G β h y s(x, y) ≤ ghsBoundSym G β h y s(x, y) := by
-- proof
  apply StatMech.Ising.ghs_degenerate_right G β h hβ hh x y hxy

/--
[ghsThreePoint_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSThreePoint.lean)
-/
@[path]
private lemma ghsThreePoint_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (he : e ∈ G.edgeFinset)
  (hoe : o ∈ e) :
-- imply
  cov3sym G β h o e ≤ ghsBoundSym G β h o e := by
-- proof
  apply StatMech.Ising.ghsThreePoint_of_mem G β h hβ hh o e he hoe


-- created on 2026-10-23
