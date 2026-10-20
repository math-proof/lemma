import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.YoungReverseMultipleCarryPath
open scoped BigOperators
open MetaMathlibExt


/--
[young_reverse_multiple_carry_path_iff_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultipleCarryPath.lean)
-/
@[path]
private lemma young_reverse_multiple_carry_path_iff_general_eq
  {g k n : ℕ}
  {a : Fin n → ℕ}
-- given
  (hgk : 2 ≤ k)
  (hkg : k < g)
  (hdigit : ∀ i, a i < g) :
-- imply
  k * (∑ i, a i * g ^ i.val) = ∑ i, a (Fin.rev i) * g ^ i.val ↔
    ∃! r : Fin (n + 1) → ℕ,
    r ⟨0, Nat.succ_pos n⟩ = 0 ∧ r (Fin.last n) = 0 ∧
    ∀ i : Fin n, r i.succ < k ∧
    k * a i + r i.castSucc = a (Fin.rev i) + r i.succ * g := by
-- proof
  apply MetaMathlibExt.young_reverse_multiple_carry_path_iff_general g k n hgk hkg a hdigit

/--
[young_reverse_multiple_carry_path_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultipleCarryPath.lean)
-/
@[path]
private lemma young_reverse_multiple_carry_path_iff_eq
  {g k n : ℕ}
  {a : Fin n → ℕ}
-- given
  (hgk : 2 ≤ k)
  (hkg : k < g)
  (hn : 0 < n)
  (hdigit : ∀ i, a i < g)
  (hfirst : a (Fin.rev ⟨0, hn⟩) ≠ 0)
  (hlast : a ⟨0, hn⟩ ≠ 0) :
-- imply
  k * (∑ i, a i * g ^ i.val) = ∑ i, a (Fin.rev i) * g ^ i.val ↔
    ∃! r : Fin (n + 1) → ℕ,
    r ⟨0, Nat.succ_pos n⟩ = 0 ∧ r (Fin.last n) = 0 ∧
    ∀ i : Fin n, r i.succ < k ∧
    k * a i + r i.castSucc = a (Fin.rev i) + r i.succ * g := by
-- proof
  apply MetaMathlibExt.young_reverse_multiple_carry_path_iff g k n hgk hkg hn a hdigit hfirst hlast


-- created on 2026-10-20
