import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.Chebyshev
open scoped Asymptotics
open Chebyshev


/--
[primeCounting_sub_theta_div_log_isLittleO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
private lemma primeCounting_sub_theta_div_log_isLittleO_eq
  :
-- imply
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x)
    =o[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
-- proof
  apply Chebyshev.primeCounting_sub_theta_div_log_isLittleO

/--
[primeCounting_isEquivalent_of_theta_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
private lemma primeCounting_isEquivalent_of_theta_isEquivalent_eq
-- given
  (h : Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :
-- imply
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
-- proof
  apply Chebyshev.primeCounting_isEquivalent_of_theta_isEquivalent h

/--
[theta_isEquivalent_of_primeCounting_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
private lemma theta_isEquivalent_of_primeCounting_isEquivalent_eq
-- given
  (h : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[Filter.atTop] (fun x : ℝ => x / Real.log x)) :
-- imply
  Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x := by
-- proof
  apply Chebyshev.theta_isEquivalent_of_primeCounting_isEquivalent h

/--
[primeCounting_isEquivalent_iff_theta_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
private lemma primeCounting_isEquivalent_iff_theta_isEquivalent_eq
  :
-- imply
  ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x))
    ↔ (Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) := by
-- proof
  apply Chebyshev.primeCounting_isEquivalent_iff_theta_isEquivalent


-- created on 2026-10-20
