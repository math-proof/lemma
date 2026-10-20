import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Finite.PermutationPolynomial
open Polynomial


/--
[isKComplete_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
private lemma isKComplete_iff_eq
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ} :
-- imply
  IsKComplete f k ↔ ∀ i : ℕ, i ≤ k →
      Function.Bijective fun x =>
        (f + Polynomial.C (i : F) * Polynomial.X).eval x := by
-- proof
  apply Polynomial.isKComplete_iff f k

/--
[isKComplete_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
private lemma isKComplete_mono_eq
  [Field F] [Finite F]
  {f : Polynomial F}
  {j k : ℕ}
-- given
  (h : IsKComplete f k)
  (hle : j ≤ k) :
-- imply
  IsKComplete f j := by
-- proof
  apply Polynomial.isKComplete_mono h hle

/--
[isKComplete_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
private lemma isKComplete_zero_eq
  [Field F] [Finite F]
  {f : Polynomial F} :
-- imply
  IsKComplete f 0 ↔ IsPermutationPolynomial f := by
-- proof
  apply Polynomial.isKComplete_zero f

/--
[isKComplete_succ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
private lemma isKComplete_succ_iff_eq
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ} :
-- imply
  IsKComplete f (k + 1) ↔ IsKComplete f k ∧
      IsPermutationPolynomial
        (f + Polynomial.C ((k + 1 : ℕ) : F) * Polynomial.X) := by
-- proof
  apply Polynomial.isKComplete_succ_iff f k

/--
[isKComplete_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
private lemma isKComplete_self_eq
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ}
-- given
  (h : IsKComplete f k) :
-- imply
  IsPermutationPolynomial f := by
-- proof
  apply Polynomial.isKComplete_self h


-- created on 2026-10-20
