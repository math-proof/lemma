import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry26Ramanujanpi
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry26Ramanujanpi


/--
[chapter9BoundaryLog_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean)
-/
@[path]
private lemma chapter9BoundaryLog_eq_log_eq
  {x : ℝ} :
-- imply
  chapter9BoundaryLog x = Real.log x := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi.chapter9BoundaryLog_eq_log x

/--
[chapter9DilogCosTerm_eq_entry24](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean)
-/
@[path]
private lemma chapter9DilogCosTerm_eq_entry24_eq
  {rho angle : ℝ}
  {j : ℕ} :
-- imply
  chapter9DilogCosTerm rho angle j =
    Entry24Dougall.chapter9DilogCosTerm rho angle j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi.chapter9DilogCosTerm_eq_entry24 rho angle j

/--
[chapter9DilogSinTerm_eq_entry24](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean)
-/
@[path]
private lemma chapter9DilogSinTerm_eq_entry24_eq
  {rho angle : ℝ}
  {j : ℕ} :
-- imply
  chapter9DilogSinTerm rho angle j =
    Entry24Dougall.chapter9DilogSinTerm rho angle j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi.chapter9DilogSinTerm_eq_entry24 rho angle j

/--
[ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms_eq
  {x y theta phi : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (htheta0 : -Real.pi < theta)
  (htheta1 : theta ≤ Real.pi)
  (hphi0 : -Real.pi < phi)
  (hphi1 : phi ≤ Real.pi)
  (hrelation : (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) + (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) + ((x * y : ℝ) : ℂ) * Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
-- imply
  Summable (fun j : ℕ => Entry24Dougall.chapter9DilogCosTerm x theta (2 * j)) ∧
    Summable (fun j : ℕ => Entry24Dougall.chapter9DilogCosTerm y phi (2 * j)) ∧
    Summable (fun j : ℕ => Entry24Dougall.chapter9DilogSinTerm x theta (2 * j)) ∧
    Summable (fun j : ℕ => Entry24Dougall.chapter9DilogSinTerm y phi (2 * j)) ∧
    (∑' j : ℕ, Entry24Dougall.chapter9DilogCosTerm x theta (2 * j)) +
    (∑' j : ℕ, Entry24Dougall.chapter9DilogCosTerm y phi (2 * j)) =
    Real.pi ^ 2 / 8 - (1 / 2 : ℝ) * Real.log x * Real.log y +
    (1 / 2 : ℝ) * theta * phi ∧
    (∑' j : ℕ, Entry24Dougall.chapter9DilogSinTerm x theta (2 * j)) +
    (∑' j : ℕ, Entry24Dougall.chapter9DilogSinTerm y phi (2 * j)) =
    -(1 / 2 : ℝ) * phi * Real.log x - (1 / 2 : ℝ) * theta * Real.log y := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi.ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms x y theta phi hx0 hx1 hy0 hy1 htheta0 htheta1 hphi0 hphi1 hrelation

/--
[ramanujan_part1_ch9_entry26_ramanujanpi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry26_ramanujanpi_eq
  {x y theta phi : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (htheta0 : -Real.pi < theta)
  (htheta1 : theta ≤ Real.pi)
  (hphi0 : -Real.pi < phi)
  (hphi1 : phi ≤ Real.pi)
  (hrelation : (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) + (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) + ((x * y : ℝ) : ℂ) * Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
-- imply
  Summable (fun j : ℕ => chapter9DilogCosTerm x theta (2 * j)) ∧
    Summable (fun j : ℕ => chapter9DilogCosTerm y phi (2 * j)) ∧
    Summable (fun j : ℕ => chapter9DilogSinTerm x theta (2 * j)) ∧
    Summable (fun j : ℕ => chapter9DilogSinTerm y phi (2 * j)) ∧
    (∑' j : ℕ, chapter9DilogCosTerm x theta (2 * j)) +
    (∑' j : ℕ, chapter9DilogCosTerm y phi (2 * j)) =
    Real.pi ^ 2 / 8 -
    (1 / 2 : ℝ) * chapter9BoundaryLog x * chapter9BoundaryLog y +
    (1 / 2 : ℝ) * theta * phi ∧
    (∑' j : ℕ, chapter9DilogSinTerm x theta (2 * j)) +
    (∑' j : ℕ, chapter9DilogSinTerm y phi (2 * j)) =
    -(1 / 2 : ℝ) * phi * chapter9BoundaryLog x -
    (1 / 2 : ℝ) * theta * chapter9BoundaryLog y := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi.ramanujan_part1_ch9_entry26_ramanujanpi x y theta phi hx0 hx1 hy0 hy1 htheta0 htheta1 hphi0 hphi1 hrelation


-- created on 2026-10-20
