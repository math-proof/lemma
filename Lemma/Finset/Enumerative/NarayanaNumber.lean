import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.NarayanaNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[narayana_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaNumber.lean)
-/
@[path]
lemma narayana_eq
  {n k : {n : ℕ // 0 < n}} :
-- imply
  narayana n k
    = (Nat.choose n.val k.val * Nat.choose n.val (k.val - 1)) / n.val :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[narayana_eq_second](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaNumber.lean)
-/
@[path]
lemma narayana_eq_second
  {n k : {n : ℕ // 0 < n}} :
-- imply
  narayana n k
    = (Nat.choose (n.val - 1) (k.val - 1) * Nat.choose n.val (k.val - 1))
    / k.val := by
-- proof
  unfold narayana
  have hn : 0 < n.val := n.property
  have hk : 0 < k.val := k.property
  obtain ⟨m, hm⟩ : ∃ m, n.val = m + 1 := ⟨n.val - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, k.val = j + 1 := ⟨k.val - 1, by omega⟩
  rw [hm, hj]
  simp only [Nat.add_sub_cancel]
  have key : ∀ a b : ℕ,
    (b + 1) * Nat.choose (a + 1) (b + 1) = (a + 1) * Nat.choose a b := by
    intro a
    induction a with
    | zero =>
      intro b
      cases b with
      | zero => simp
      | succ b =>
        have hlt1 : (0 + 1) < (b + 1) + 1 := by omega
        have hlt2 : (0 : ℕ) < b + 1 := by omega
        rw [Nat.choose_eq_zero_of_lt hlt1, Nat.choose_eq_zero_of_lt hlt2]
        simp
    | succ a ih =>
      intro b
      cases b with
      | zero => simp
      | succ b =>
        have h1 := ih b
        have h2 := ih (b + 1)
        have p1 := Nat.choose_succ_succ (a + 1) (b + 1)
        have p2 := Nat.choose_succ_succ a b
        have eL : ((b + 1) + 1) * Nat.choose (a + 1) (b + 1)
          = Nat.choose (a + 1) (b + 1)
            + (b + 1) * Nat.choose (a + 1) (b + 1) := by
          rw [Nat.add_mul, Nat.one_mul,
            Nat.add_comm ((b + 1) * Nat.choose (a + 1) (b + 1))
              (Nat.choose (a + 1) (b + 1))]
        have eR : ((a + 1) + 1) * Nat.choose (a + 1) (b + 1)
          = Nat.choose (a + 1) (b + 1)
            + (a + 1) * Nat.choose (a + 1) (b + 1) := by
          rw [Nat.add_mul, Nat.one_mul,
            Nat.add_comm ((a + 1) * Nat.choose (a + 1) (b + 1))
              (Nat.choose (a + 1) (b + 1))]
        rw [p1, Nat.mul_add, eL, eR, h1, h2, Nat.add_assoc, ← Nat.mul_add, ← p2]
  have hkey : (j + 1) * Nat.choose (m + 1) (j + 1)
    = (m + 1) * Nat.choose m j :=
    key m j
  have hpos1 : 0 < m + 1 := by omega
  have hpos2 : 0 < j + 1 := by omega
  have hmul : (Nat.choose (m + 1) (j + 1) * Nat.choose (m + 1) j) * (j + 1)
    = (Nat.choose m j * Nat.choose (m + 1) j) * (m + 1) := by
    calc (Nat.choose (m + 1) (j + 1) * Nat.choose (m + 1) j) * (j + 1)
      = Nat.choose (m + 1) j * ((j + 1) * Nat.choose (m + 1) (j + 1)) := by
        ac_rfl
      _ = Nat.choose (m + 1) j * ((m + 1) * Nat.choose m j) := by rw [hkey]
      _ = (Nat.choose m j * Nat.choose (m + 1) j) * (m + 1) := by ac_rfl
  calc (Nat.choose (m + 1) (j + 1) * Nat.choose (m + 1) j) / (m + 1)
    = ((Nat.choose (m + 1) (j + 1) * Nat.choose (m + 1) j) * (j + 1))
      / ((m + 1) * (j + 1)) := by rw [Nat.mul_div_mul_right _ _ hpos2]
    _ = ((Nat.choose m j * Nat.choose (m + 1) j) * (m + 1))
      / ((m + 1) * (j + 1)) := by rw [hmul]
    _ = ((Nat.choose m j * Nat.choose (m + 1) j) * (m + 1))
      / ((j + 1) * (m + 1)) := by rw [Nat.mul_comm (m + 1) (j + 1)]
    _ = (Nat.choose m j * Nat.choose (m + 1) j) / (j + 1) := by
      rw [Nat.mul_div_mul_right _ _ hpos1]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
