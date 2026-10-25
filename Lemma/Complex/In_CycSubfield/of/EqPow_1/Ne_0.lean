import Mathlib
import sympy.Basic
import Instance.GroupTheory.BurnsidePaqb.CyclotomicField
open Polynomial
open BurnsidePaqb


/--
[mem_cycSubfield_of_pow_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean)
-/
@[path]
private lemma mem_cycSubfield_of_pow_eq_one_eq
  {m : ℕ}
  {ζ : ℂ}
-- given
  (hm : m ≠ 0)
  (h : ζ ^ m = 1) :
-- imply
  ζ ∈ cycSubfield m := by
-- proof
  apply BurnsidePaqb.mem_cycSubfield_of_pow_eq_one m hm ζ h

/--
[map_X_pow_sub_C_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean)
-/
@[path]
private lemma map_X_pow_sub_C_rat_eq
  {m : ℕ} :
-- imply
  ((X ^ m - C 1 : ℚ[X]).map (algebraMap ℚ ℂ)) = (X ^ m - C 1 : ℂ[X]) := by
-- proof
  apply BurnsidePaqb.map_X_pow_sub_C_rat m

/--
[cyc_rootSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean)
-/
@[path]
private lemma cyc_rootSet_eq
  {m : ℕ}
-- given
  (hm : m ≠ 0) :
-- imply
  (X ^ m - C 1 : ℚ[X]).rootSet ℂ =
      ↑(Polynomial.nthRootsFinset m (1 : ℂ)) := by
-- proof
  apply BurnsidePaqb.cyc_rootSet m hm

/--
[cyc_isSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean)
-/
@[path]
private lemma cyc_isSplitting_eq
  {m : ℕ}
-- given
  (hm : m ≠ 0) :
-- imply
  (X ^ m - C 1 : ℚ[X]).IsSplittingField ℚ (cycSubfield m) := by
-- proof
  apply BurnsidePaqb.cyc_isSplitting m hm

/--
[cycSubfield_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean)
-/
@[path]
private lemma cycSubfield_zero_eq
  :
-- imply
  cycSubfield 0 = ⊥ := by
-- proof
  apply BurnsidePaqb.cycSubfield_zero


-- created on 2026-10-20
