import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams.Part2
open YoungLattice YoungLattice.Lmn


namespace YoungLattice.Lmn

/--
[card_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
lemma card_succ_succ
  {m n : ℕ} :
-- imply
  Fintype.card (Lmn (m + 1) (n + 1)) = Fintype.card (Lmn m (n + 1)) + Fintype.card (Lmn (m + 1) n) := by
-- proof
  classical
  rw [Fintype.card_congr (sumEquiv m n), Fintype.card_sum]

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[card_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
lemma card_zero
  {n : ℕ} :
-- imply
  Fintype.card (Lmn 0 n) = 1 := by
-- proof
  haveI : Unique (Lmn 0 n) :=
    ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun a => by ext i; exact i.elim0⟩
  exact Fintype.card_unique

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[card_right_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
lemma card_right_zero
  {m : ℕ} :
-- imply
  Fintype.card (Lmn m 0) = 1 := by
-- proof
  haveI : Unique (Lmn m 0) :=
    ⟨⟨⟨fun _ => 0, fun _ _ _ => le_refl _⟩⟩,
      fun a => by
        apply Lmn.ext; intro i
        exact Fin.ext (by have := (a.val i).isLt; omega)⟩
  exact Fintype.card_unique

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[card_eq_choose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
lemma card_eq_choose
  {m n : ℕ} :
-- imply
  Fintype.card (Lmn m n) = (m + n).choose m := by
-- proof
  induction m generalizing n with
  | zero => simp [card_zero]
  | succ m ihm =>
    induction n with
    | zero => simp [card_right_zero]
    | succ n ihn =>
      rw [card_succ_succ, ihm (n + 1), ihn]
      have h1 : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
      have h2 : m + (n + 1) = m + n + 1 := by omega
      have h3 : (m + 1) + n = m + n + 1 := by omega
      rw [h1, h2, h3]
      exact Nat.choose_succ_succ (m + n + 1) m

end YoungLattice.Lmn

/--
[extendZero_last](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
private lemma extendZero_last_eq
  {m n : ℕ}
  {q : Lmn m (n + 1)} :
-- imply
  (extendZero q).val (Fin.last m) = 0 := by
-- proof
  apply YoungLattice.Lmn.extendZero_last q

/--
[shiftUp_last_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean)
-/
@[path]
private lemma shiftUp_last_ne_zero_eq
  {m n : ℕ}
  {q : Lmn (m + 1) n} :
-- imply
  (shiftUp q).val (Fin.last m) ≠ 0 := by
-- proof
  apply YoungLattice.Lmn.shiftUp_last_ne_zero q


-- created on 2026-10-23
