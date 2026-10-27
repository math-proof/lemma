import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.SulankeNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[sulankeB_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeB_zero
  :
-- imply
  sulankeB 0 0 = 1 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeB_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeB_zero_succ
  {i : ℕ} :
-- imply
  sulankeB 0 (i + 1) = 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeA_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeA_zero
  {i : ℕ} :
-- imply
  sulankeA 0 i = 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeA_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeA_succ_zero
  {k : ℕ} :
-- imply
  sulankeA (k + 1) 0 = sulankeB k 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeA_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeA_succ_succ
  {k n : ℕ} :
-- imply
  sulankeA (k + 1) (n + 1) = sulankeB k (n + 1) + 2 * sulankeB k n :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeB_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeB_succ_zero
  {k : ℕ} :
-- imply
  sulankeB (k + 1) 0 = sulankeA (k + 1) 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeB_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeB_succ_succ
  {k n : ℕ} :
-- imply
  sulankeB (k + 1) (n + 1) = sulankeA (k + 1) (n + 1) + sulankeA (k + 1) n := by
-- proof
  cases n with
  | zero => simp [sulankeA, sulankeB]
  | succ m => rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeB_eq_zero_of_two_mul_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeB_eq_zero_of_two_mul_lt
  {k : ℕ} :
-- imply
  ∀ i : ℕ, 2 * k < i → sulankeB k i = 0 := by
-- proof
  induction k with
  | zero =>
    intro i h
    cases i with
    | zero => omega
    | succ n => rfl
  | succ k ih =>
    intro i h
    cases i with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        have h1 : sulankeB k (0 + 1) = 0 := ih (0 + 1) (by omega)
        have h2 : sulankeB k 0 = 0 := ih 0 (by omega)
        have e : sulankeB (k + 1) (0 + 1) =
          (sulankeB k (0 + 1) + 2 * sulankeB k 0) +
            (sulankeB k 0 + 2 * (0 : ℕ)) := rfl
        simp [e, h1, h2]
      | succ m =>
        have h1 : sulankeB k (m + 1 + 1) = 0 := ih (m + 1 + 1) (by omega)
        have h2 : sulankeB k (m + 1) = 0 := ih (m + 1) (by omega)
        have h3 : sulankeB k m = 0 := ih m (by omega)
        have e : sulankeB (k + 1) (m + 1 + 1) =
          (sulankeB k (m + 1 + 1) + 2 * sulankeB k (m + 1)) +
            (sulankeB k (m + 1) + 2 * sulankeB k m) := rfl
        simp only [e, h1, h2, h3, Nat.mul_zero, Nat.add_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sulankeA_eq_zero_of_two_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
lemma sulankeA_eq_zero_of_two_mul_le
  {k : ℕ} :
-- imply
  ∀ i : ℕ, 2 * k ≤ i → sulankeA k i = 0 := by
-- proof
  cases k with
  | zero =>
    intro i _
    rfl
  | succ k =>
    intro i h
    cases i with
    | zero => omega
    | succ n =>
      have h1 : sulankeB k (n + 1) = 0 :=
        sulankeB_eq_zero_of_two_mul_lt k (n + 1) (by omega)
      have h2 : sulankeB k n = 0 := sulankeB_eq_zero_of_two_mul_lt k n (by omega)
      have e : sulankeA (k + 1) (n + 1) =
        sulankeB k (n + 1) + 2 * sulankeB k n := rfl
      rw [e, h1, h2]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
