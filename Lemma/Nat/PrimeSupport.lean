import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeSupport
open Nat


/--
[samePrimeSupport_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
@[path]
private lemma samePrimeSupport_refl_eq
  {a : ℕ} :
-- imply
  SamePrimeSupport a a := by
-- proof
  apply Nat.samePrimeSupport_refl a

/--
[SamePrimeSupport.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
@[path]
private lemma SamePrimeSupport_symm_eq
  {a b : ℕ}
-- given
  (h : SamePrimeSupport a b) :
-- imply
  SamePrimeSupport b a := by
-- proof
  apply Nat.SamePrimeSupport.symm h

/--
[SamePrimeSupport.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean)
-/
@[path]
private lemma SamePrimeSupport_trans_eq
  {a b c : ℕ}
-- given
  (h0 : SamePrimeSupport a b)
  (h1 : SamePrimeSupport b c) :
-- imply
  SamePrimeSupport a c := by
-- proof
  apply Nat.SamePrimeSupport.trans h0 h1


-- created on 2026-10-20
