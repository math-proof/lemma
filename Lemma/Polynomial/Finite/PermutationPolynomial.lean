import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FieldTheory.Finite.PermutationPolynomial
open Polynomial


namespace Polynomial

/--
[isKComplete_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
lemma isKComplete_iff
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ} :
-- imply
  IsKComplete f k ↔ ∀ i : ℕ, i ≤ k →
      Function.Bijective fun x =>
        (f + Polynomial.C (i : F) * Polynomial.X).eval x :=
-- proof
  Iff.rfl

end Polynomial

namespace Polynomial

/--
[isKComplete_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
lemma isKComplete_mono
  [Field F] [Finite F]
  {f : Polynomial F}
  {j k : ℕ}
-- given
  (h : IsKComplete f k)
  (hle : j ≤ k) :
-- imply
  IsKComplete f j :=
-- proof
  fun i hi => h i (le_trans hi hle)

end Polynomial

namespace Polynomial

/--
[isKComplete_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
lemma isKComplete_zero
  [Field F] [Finite F]
  {f : Polynomial F} :
-- imply
  IsKComplete f 0 ↔ IsPermutationPolynomial f := by
-- proof
  constructor
  · intro h
    have h0 := h 0 le_rfl
    simpa using h0
  · intro h i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    simpa using h

end Polynomial

namespace Polynomial

/--
[isKComplete_succ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
lemma isKComplete_succ_iff
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ} :
-- imply
  IsKComplete f (k + 1) ↔ IsKComplete f k ∧
      IsPermutationPolynomial
        (f + Polynomial.C ((k + 1 : ℕ) : F) * Polynomial.X) := by
-- proof
  constructor
  · intro h
    exact ⟨fun i hi => h i (le_trans hi (Nat.le_succ k)), h (k + 1) le_rfl⟩
  · intro h i hi
    obtain rfl | hlt := eq_or_lt_of_le hi
    · exact h.2
    · exact h.1 i (Nat.le_of_lt_add_one hlt)

end Polynomial

namespace Polynomial

/--
[isKComplete_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean)
-/
@[path]
lemma isKComplete_self
  [Field F] [Finite F]
  {f : Polynomial F}
  {k : ℕ}
-- given
  (h : IsKComplete f k) :
-- imply
  IsPermutationPolynomial f := by
-- proof
  have h0 := h 0 (Nat.zero_le k)
  simpa using h0

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-26
