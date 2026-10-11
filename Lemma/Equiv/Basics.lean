import Mathlib
import sympy.Basic
import sympy.combinatorics.permutations.Basics


/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_card_eq
  (X : Type*)
  [Fintype X]
  [DecidableEq X] :
-- imply
  Fintype.card (Equiv.Perm X) = Nat.factorial (Fintype.card X) := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_card

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_card_eq
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn n) = Nat.factorial n := by
-- proof
  apply AlgebraicCombinatorics.sn_card n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_zero_card_eq :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 0) = 1 := by
-- proof
  apply AlgebraicCombinatorics.sn_zero_card

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_one_card_eq :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 1) = 1 := by
-- proof
  apply AlgebraicCombinatorics.sn_one_card

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_two_card_eq :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 2) = 2 := by
-- proof
  apply AlgebraicCombinatorics.sn_two_card

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_three_card_eq :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 3) = 6 := by
-- proof
  apply AlgebraicCombinatorics.sn_three_card

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma bracket_n_card_eq
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.bracketN n) = n := by
-- proof
  apply AlgebraicCombinatorics.bracketN_card n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_mul_apply_eq
  (X : Type*)
  (α β : Equiv.Perm X)
  (x : X) :
-- imply
  (α * β) x = α (β x) := by
-- proof
  apply AlgebraicCombinatorics.perm_mul_apply α β x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_mul_assoc_eq
  (X : Type*)
  (α β γ : Equiv.Perm X) :
-- imply
  (α * β) * γ = α * (β * γ) := by
-- proof
  apply AlgebraicCombinatorics.perm_mul_assoc α β γ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_one_mul_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  1 * α = α := by
-- proof
  apply AlgebraicCombinatorics.perm_one_mul α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_mul_one_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α * 1 = α := by
-- proof
  apply AlgebraicCombinatorics.perm_mul_one α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_zero_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α ^ (0 : ℕ) = 1 := by
-- proof
  apply AlgebraicCombinatorics.perm_pow_zero α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_zpow_zero_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α ^ (0 : ℤ) = 1 := by
-- proof
  apply AlgebraicCombinatorics.perm_zpow_zero α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_one_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α ^ (1 : ℕ) = α := by
-- proof
  apply AlgebraicCombinatorics.perm_pow_one α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_succ_eq
  (X : Type*)
  (α : Equiv.Perm X)
  (n : ℕ) :
-- imply
  α ^ (n + 1) = α ^ n * α := by
-- proof
  apply AlgebraicCombinatorics.perm_pow_succ α n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_succ'_eq
  (X : Type*)
  (α : Equiv.Perm X)
  (n : ℕ) :
-- imply
  α ^ (n + 1) = α * α ^ n := by
-- proof
  apply AlgebraicCombinatorics.perm_pow_succ' α n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_zpow_neg_one_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α ^ (-1 : ℤ) = α⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.perm_zpow_neg_one α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_mul_inv_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α * α⁻¹ = 1 := by
-- proof
  apply AlgebraicCombinatorics.perm_mul_inv α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_inv_mul_eq
  (X : Type*)
  (α : Equiv.Perm X) :
-- imply
  α⁻¹ * α = 1 := by
-- proof
  apply AlgebraicCombinatorics.perm_inv_mul α

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_apply_eq
  (X : Type*)
  (α : Equiv.Perm X)
  (n : ℕ)
  (x : X) :
-- imply
  (α ^ n) x = (α^[n]) x := by
-- proof
  apply AlgebraicCombinatorics.perm_pow_apply α n x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_zpow_neg_eq
  (X : Type*)
  (α : Equiv.Perm X)
  (n : ℕ) :
-- imply
  α ^ (-(n : ℤ)) = (α⁻¹) ^ n := by
-- proof
  apply AlgebraicCombinatorics.perm_zpow_neg α n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_apply_eq
  (X Y : Type*)
  (f : X ≃ Y)
  (σ : Equiv.Perm X) :
-- imply
  AlgebraicCombinatorics.symmetricGroup_conj_iso f σ = f.permCongr σ := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_apply f σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_is_perm_eq
  (X Y : Type*)
  (f : X ≃ Y)
  (σ : Equiv.Perm X) :
-- imply
  ∃ (τ : Equiv.Perm Y), ∀ y : Y, τ y = f (σ (f.symm y)) := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_isPerm f σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_apply_val_eq
  (X Y : Type*)
  (f : X ≃ Y)
  (σ : Equiv.Perm X)
  (y : Y) :
-- imply
  AlgebraicCombinatorics.symmetricGroup_conj_iso f σ y = f (σ (f.symm y)) := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_apply_val f σ y

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_bijective_eq
  (X Y : Type*)
  (f : X ≃ Y) :
-- imply
  Function.Bijective (AlgebraicCombinatorics.symmetricGroup_conj_iso f) := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_bijective f

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_mul_eq
  (X Y : Type*)
  (f : X ≃ Y)
  (σ τ : Equiv.Perm X) :
-- imply
  AlgebraicCombinatorics.symmetricGroup_conj_iso f (σ * τ) = AlgebraicCombinatorics.symmetricGroup_conj_iso f σ * AlgebraicCombinatorics.symmetricGroup_conj_iso f τ := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_mul f σ τ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_one_eq
  (X Y : Type*)
  (f : X ≃ Y) :
-- imply
  AlgebraicCombinatorics.symmetricGroup_conj_iso f 1 = 1 := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_one f

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_symm_eq
  (X Y : Type*)
  (f : X ≃ Y) :
-- imply
  (AlgebraicCombinatorics.symmetricGroup_conj_iso f).symm = AlgebraicCombinatorics.symmetricGroup_conj_iso f.symm := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_symm f

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_iso_of_equiv_eq
  (X Y : Type*)
  (f : X ≃ Y) :
-- imply
  Nonempty (Equiv.Perm X ≃* Equiv.Perm Y) := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_iso_of_equiv f

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_conj_iso_self_eq
  (X : Type*)
  (f σ : Equiv.Perm X) :
-- imply
  AlgebraicCombinatorics.symmetricGroup_conj_iso f σ = f * σ * f⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.symmetricGroup_conj_iso_self f σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma two_line_notation_length_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  (AlgebraicCombinatorics.twoLineNotation σ).length = n := by
-- proof
  apply AlgebraicCombinatorics.twoLineNotation_length σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma two_line_notation_get_elem_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (i : ℕ)
  (hi : i < n) :
-- imply
  (AlgebraicCombinatorics.twoLineNotation σ)[i]'(by simp [AlgebraicCombinatorics.twoLineNotation]; omega) = (⟨i, hi⟩, σ ⟨i, hi⟩) := by
-- proof
  apply AlgebraicCombinatorics.twoLineNotation_getElem σ i hi

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma two_line_notation_fst_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  (AlgebraicCombinatorics.twoLineNotation σ).map Prod.fst = List.finRange n := by
-- proof
  apply AlgebraicCombinatorics.twoLineNotation_fst σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma two_line_notation_snd_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  (AlgebraicCombinatorics.twoLineNotation σ).map Prod.snd = (List.finRange n).map σ := by
-- proof
  apply AlgebraicCombinatorics.twoLineNotation_snd σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma eq_iff_two_line_notation_eq
  {n : ℕ}
  (σ τ : AlgebraicCombinatorics.Sn n) :
-- imply
  σ = τ ↔ AlgebraicCombinatorics.twoLineNotation σ = AlgebraicCombinatorics.twoLineNotation τ := by
-- proof
  apply AlgebraicCombinatorics.eq_iff_twoLineNotation_eq σ τ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma one_line_notation_length_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  (AlgebraicCombinatorics.oneLineNotation σ).length = n := by
-- proof
  apply AlgebraicCombinatorics.oneLineNotation_length σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma one_line_notation_get_elem_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (i : ℕ)
  (hi : i < n) :
-- imply
  (AlgebraicCombinatorics.oneLineNotation σ)[i]'(by simp [AlgebraicCombinatorics.oneLineNotation]; omega) = σ ⟨i, hi⟩ := by
-- proof
  apply AlgebraicCombinatorics.oneLineNotation_getElem σ i hi

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma one_line_notation_nodup_is
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  (AlgebraicCombinatorics.oneLineNotation σ).Nodup := by
-- proof
  apply AlgebraicCombinatorics.oneLineNotation_nodup σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma eq_iff_one_line_notation_eq
  {n : ℕ}
  (σ τ : AlgebraicCombinatorics.Sn n) :
-- imply
  σ = τ ↔ AlgebraicCombinatorics.oneLineNotation σ = AlgebraicCombinatorics.oneLineNotation τ := by
-- proof
  apply AlgebraicCombinatorics.eq_iff_oneLineNotation_eq σ τ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma one_line_notation_to_perm_one_line_notation_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  AlgebraicCombinatorics.oneLineNotationToPerm (AlgebraicCombinatorics.oneLineNotation σ) (AlgebraicCombinatorics.oneLineNotation_length σ)
    (AlgebraicCombinatorics.oneLineNotation_nodup σ) = σ := by
-- proof
  apply AlgebraicCombinatorics.oneLineNotationToPerm_oneLineNotation σ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_adj_iff
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (i j : Fin n) :
-- imply
  (AlgebraicCombinatorics.cycleDigraph σ).Adj i j ↔ i ≠ j ∧ (σ i = j ∨ σ j = i) := by
-- proof
  apply AlgebraicCombinatorics.cycleDigraph_adj_iff σ i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_adj_of_apply_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  {i j : Fin n}
  (h : σ i = j)
  (hne : i ≠ j) :
-- imply
  (AlgebraicCombinatorics.cycleDigraph σ).Adj i j := by
-- proof
  apply AlgebraicCombinatorics.cycleDigraph_adj_of_apply σ h hne

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_connected_iff
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (i j : Fin n) :
-- imply
  (AlgebraicCombinatorics.cycleDigraph σ).Reachable i j ↔ ∃ k : ℤ, (σ ^ k) i = j := by
-- proof
  apply AlgebraicCombinatorics.cycleDigraph_connected_iff σ i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_one_eq
  {n : ℕ} :
-- imply
  AlgebraicCombinatorics.cycleDigraph (1 : AlgebraicCombinatorics.Sn n) = ⊥ := by
-- proof
  apply AlgebraicCombinatorics.cycleDigraph_one

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_swap_adj_iff
  {n : ℕ}
  (i j : Fin n)
  (hij : i ≠ j)
  (a b : Fin n) :
-- imply
  (AlgebraicCombinatorics.cycleDigraph (Equiv.swap i j)).Adj a b ↔
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
-- proof
  apply AlgebraicCombinatorics.cycleDigraph_swap_adj_iff i j hij a b

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_apply_left_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.transposition i j i = j := by
-- proof
  apply AlgebraicCombinatorics.transposition_apply_left i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_apply_right_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.transposition i j j = i := by
-- proof
  apply AlgebraicCombinatorics.transposition_apply_right i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_apply_of_ne_of_ne_eq
  [DecidableEq X]
  {i j x : X}
  (hi : x ≠ i)
  (hj : x ≠ j) :
-- imply
  AlgebraicCombinatorics.transposition i j x = x := by
-- proof
  apply AlgebraicCombinatorics.transposition_apply_of_ne_of_ne hi hj

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_symm_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.transposition i j = AlgebraicCombinatorics.transposition j i := by
-- proof
  apply AlgebraicCombinatorics.transposition_symm i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_inv_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  (AlgebraicCombinatorics.transposition i j)⁻¹ = AlgebraicCombinatorics.transposition i j := by
-- proof
  apply AlgebraicCombinatorics.transposition_inv i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma transposition_sq_eq_one_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.transposition i j * AlgebraicCombinatorics.transposition i j = 1 := by
-- proof
  apply AlgebraicCombinatorics.transposition_sq_eq_one i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma num_transpositions_is
  (X : Type*)
  [DecidableEq X]
  [Fintype X] :
-- imply
  ∃ (S : Finset (Equiv.Perm X)),
    (∀ σ ∈ S, σ.IsSwap) ∧
    (∀ σ : Equiv.Perm X, σ.IsSwap → σ ∈ S) ∧
    S.card = Nat.choose (Fintype.card X) 2 := by
-- proof
  apply AlgebraicCombinatorics.num_transpositions

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_eq_transposition_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i = AlgebraicCombinatorics.transposition
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
    ⟨i.val + 1, by omega⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_eq_transposition i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_apply_self_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ = ⟨i.val + 1, by omega⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_apply_self i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_apply_succ_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i ⟨i.val + 1, by omega⟩ = ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_apply_succ i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_apply_of_ne_eq
  {n : ℕ}
  (i : Fin (n - 1))
  (k : Fin n)
  (hi : k.val ≠ i.val)
  (hi1 : k.val ≠ i.val + 1) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i k = k := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_apply_of_ne i k hi hi1

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_support_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i).support = {⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩,
                                      ⟨i.val + 1, by omega⟩} := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_support i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_is_swap_is
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i).IsSwap := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_isSwap i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_is_cycle_is
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i).IsCycle := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_isCycle i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_support_card_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i).support.card = 2 := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_support_card i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_ne_one_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i ≠ 1 := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_ne_one i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_sq_eq_one_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i) * (AlgebraicCombinatorics.simpleTransposition i) = 1 := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_sq_eq_one i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_inv_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i)⁻¹ = (AlgebraicCombinatorics.simpleTransposition i) := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_inv i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_comm_eq
  {n : ℕ}
  (i j : Fin (n - 1))
  (h : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
-- imply
  (AlgebraicCombinatorics.simpleTransposition i) * (AlgebraicCombinatorics.simpleTransposition j) = (AlgebraicCombinatorics.simpleTransposition j) * (AlgebraicCombinatorics.simpleTransposition i) := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_comm i j h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_eq_swap_eq
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i = Equiv.swap
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
    ⟨i.val + 1, by omega⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_eq_swap i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_eq_swap_cast_succ_succ_eq
  {n : ℕ}
  (i : Fin (n - 1))
  (hn : n > 0) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i = Equiv.swap
    (Fin.castLE (by omega) i.castSucc)
    (Fin.castLE (by omega) i.succ) := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_eq_swap_castSucc_succ i hn

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_eq_swap_with_proofs_eq
  {N : ℕ}
  (i : Fin (N - 1)) :
-- imply
  AlgebraicCombinatorics.simpleTransposition i = Equiv.swap
    ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
    ⟨i.val + 1, Nat.lt_pred_iff.mp i.isLt⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_eq_swap_with_proofs i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_pair_eq
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.cyc [i, j] = Equiv.swap i j := by
-- proof
  apply AlgebraicCombinatorics.cyc_pair i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_nil_eq
  [DecidableEq X] :
-- imply
  AlgebraicCombinatorics.cyc ([] : List X) = 1 := by
-- proof
  apply AlgebraicCombinatorics.cyc_nil

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_singleton_eq
  [DecidableEq X]
  (x : X) :
-- imply
  AlgebraicCombinatorics.cyc [x] = 1 := by
-- proof
  apply AlgebraicCombinatorics.cyc_singleton x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_apply_of_not_mem_eq
  [DecidableEq X]
  {l : List X}
  {x : X}
  (h : x ∉ l) :
-- imply
  AlgebraicCombinatorics.cyc l x = x := by
-- proof
  apply AlgebraicCombinatorics.cyc_apply_of_not_mem h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_apply_cons_cons_eq
  [DecidableEq X]
  (x y : X)
  (l : List X) :
-- imply
  AlgebraicCombinatorics.cyc (x :: y :: l) = Equiv.swap x y * AlgebraicCombinatorics.cyc (y :: l) := by
-- proof
  apply AlgebraicCombinatorics.cyc_apply_cons_cons x y l

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_is_cycle_is
  [DecidableEq X]
  {l : List X}
  (hl : l.Nodup)
  (hn : 2 ≤ l.length) :
-- imply
  (AlgebraicCombinatorics.cyc l).IsCycle := by
-- proof
  apply AlgebraicCombinatorics.cyc_isCycle hl hn

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_apply_eq_next_eq
  [DecidableEq X]
  {l : List X}
  (hl : l.Nodup)
  {x : X}
  (hx : x ∈ l) :
-- imply
  AlgebraicCombinatorics.cyc l x = l.next x hx := by
-- proof
  apply AlgebraicCombinatorics.cyc_apply_eq_next hl hx

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_support_subset_eq
  [DecidableEq X]
  [Fintype X]
  {l : List X} :
-- imply
  (AlgebraicCombinatorics.cyc l).support ⊆ l.toFinset := by
-- proof
  apply AlgebraicCombinatorics.cyc_support_subset

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_support_eq_to_finset_eq
  [DecidableEq X]
  [Fintype X]
  {l : List X}
  (hl : l.Nodup)
  (hn : 2 ≤ l.length) :
-- imply
  (AlgebraicCombinatorics.cyc l).support = l.toFinset := by
-- proof
  apply AlgebraicCombinatorics.cyc_support_eq_toFinset hl hn

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_rotate_eq
  [DecidableEq X]
  {l : List X}
  (hl : l.Nodup)
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.cyc (l.rotate n) = AlgebraicCombinatorics.cyc l := by
-- proof
  apply AlgebraicCombinatorics.cyc_rotate hl n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_rotate_one_eq
  [DecidableEq X]
  {l : List X}
  (hl : l.Nodup) :
-- imply
  AlgebraicCombinatorics.cyc (l.rotate 1) = AlgebraicCombinatorics.cyc l := by
-- proof
  apply AlgebraicCombinatorics.cyc_rotate_one hl

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_apply_get_elem_eq
  [DecidableEq X]
  {l : List X}
  (hl : l.Nodup)
  (j : ℕ)
  (hj : j < l.length) :
-- imply
  AlgebraicCombinatorics.cyc l (l[j]) = l[(j + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hj)) := by
-- proof
  apply AlgebraicCombinatorics.cyc_apply_getElem hl j hj

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_eq_cyc_iff_is_rotated_iff
  [DecidableEq X]
  {l l' : List X}
  (hl : l.Nodup)
  (hl' : l'.Nodup)
  (hlen : 2 ≤ l.length)
  (hlen' : 2 ≤ l'.length) :
-- imply
  AlgebraicCombinatorics.cyc l = AlgebraicCombinatorics.cyc l' ↔ l ~r l' := by
-- proof
  apply AlgebraicCombinatorics.cyc_eq_cyc_iff_isRotated hl hl' hlen hlen'

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_eq_transposition_eq
  [DecidableEq X]
  [Fintype X]
  {σ : Equiv.Perm X}
  (hσ : σ.IsCycle)
  (hcard : σ.support.card = 2) :
-- imply
  ∃ i j : X, i ≠ j ∧ σ = Equiv.swap i j := by
-- proof
  apply AlgebraicCombinatorics.cycle_eq_transposition hσ hcard

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma num_k_cycles_formula_is
  (n k : ℕ)
  (hk : 1 < k)
  (hkn : k ≤ n) :
-- imply
  -- The number of k-cycles equals C(n,k) * (k-1)!
  -- This is because:
  -- - There are n(n-1)...(n-k+1) ways to choose an ordered k-tuple
  -- - Each k-cycle corresponds to exactly k such tuples (by cyclic rotation)
  -- - So the count is n(n-1)...(n-k+1)/k = C(n,k) * (k-1)!
  ∃ (S : Finset (AlgebraicCombinatorics.Sn n)),
    (∀ σ ∈ S, σ.IsCycle ∧ σ.support.card = k) ∧
    (∀ σ : AlgebraicCombinatorics.Sn n, σ.IsCycle → σ.support.card = k → σ ∈ S) ∧
    S.card = Nat.choose n k * Nat.factorial (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.num_kCycles_formula n k hk hkn

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma no_1cycles_is_cycle_le
  (n : ℕ)
  (σ : AlgebraicCombinatorics.Sn n)
  (hσ : σ.IsCycle) :
-- imply
  2 ≤ σ.support.card := by
-- proof
  apply AlgebraicCombinatorics.no_1Cycles_isCycle n σ hσ

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_eq_inv_eq
  (X : Type*)
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  σ⁻¹ = σ := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.eq_inv h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_iff_eq_inv_iff
  (X : Type*)
  {σ : Equiv.Perm X} :
-- imply
  AlgebraicCombinatorics.IsInvolution σ ↔ σ⁻¹ = σ := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_iff_eq_inv

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_iff_involutive_iff
  (X : Type*)
  {σ : Equiv.Perm X} :
-- imply
  AlgebraicCombinatorics.IsInvolution σ ↔ Function.Involutive σ := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_iff_involutive

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_iff_forall_iff
  (X : Type*)
  {σ : Equiv.Perm X} :
-- imply
  AlgebraicCombinatorics.IsInvolution σ ↔ ∀ x, σ (σ x) = x := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_iff_forall

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_apply_apply_eq
  (X : Type*)
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ)
  (x : X) :
-- imply
  σ (σ x) = x := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.apply_apply h x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_one_is
  (X : Type*) :
-- imply
  AlgebraicCombinatorics.IsInvolution (1 : Equiv.Perm X) := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_one

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_transposition_is
  [DecidableEq X]
  (i j : X) :
-- imply
  AlgebraicCombinatorics.IsInvolution (AlgebraicCombinatorics.transposition i j) := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_transposition i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_simple_transposition_is
  {n : ℕ}
  (i : Fin (n - 1)) :
-- imply
  AlgebraicCombinatorics.IsInvolution (AlgebraicCombinatorics.simpleTransposition i) := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_simpleTransposition i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_order_of_dvd_two_eq
  [Fintype X]
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  orderOf σ ∣ 2 := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.orderOf_dvd_two h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_order_of_le_two_le
  [Fintype X]
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  orderOf σ ≤ 2 := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.orderOf_le_two h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_eq_one_iff_order_of_eq_one_iff
  (X : Type*)
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  σ = 1 ↔ orderOf σ = 1 := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.eq_one_iff_orderOf_eq_one h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_order_of_eq_two_of_ne_one_eq
  [Fintype X]
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ)
  (hne : σ ≠ 1) :
-- imply
  orderOf σ = 2 := by
-- proof
  apply AlgebraicCombinatorics.IsInvolution.orderOf_eq_two_of_ne_one h hne

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma not_is_involution_of_cycle_gt_two_is
  [DecidableEq X]
  [Fintype X]
  {σ : Equiv.Perm X}
  (hσ : σ.IsCycle)
  (hcard : 2 < σ.support.card) :
-- imply
  ¬AlgebraicCombinatorics.IsInvolution σ := by
-- proof
  apply AlgebraicCombinatorics.not_isInvolution_of_cycle_gt_two hσ hcard

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_of_disjoint_transpositions_is
  [DecidableEq X]
  {pairs : List (X × X)}
  (hdisjoint : pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2))
  (hdistinct : ∀ p ∈ pairs, p.1 ≠ p.2) :
-- imply
  AlgebraicCombinatorics.IsInvolution (pairs.map (fun p => AlgebraicCombinatorics.transposition p.1 p.2)).prod := by
-- proof
  apply AlgebraicCombinatorics.isInvolution_of_disjoint_transpositions hdisjoint hdistinct

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma involution_cycle_structure_le
  [DecidableEq X]
  [Fintype X]
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  ∀ c ∈ σ.cycleFactorsFinset, (c : Equiv.Perm X).support.card ≤ 2 := by
-- proof
  apply AlgebraicCombinatorics.involution_cycle_structure h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma involution_is_product_of_disjoint_transpositions_eq
  [DecidableEq X]
  [Fintype X]
  {σ : Equiv.Perm X}
  (h : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  ∃ pairs : List (X × X),
    pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
    (∀ p ∈ pairs, p.1 ≠ p.2) ∧
    σ = (pairs.map (fun p => AlgebraicCombinatorics.transposition p.1 p.2)).prod := by
-- proof
  apply AlgebraicCombinatorics.involution_is_product_of_disjoint_transpositions h

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_braid_eq
  (i : Fin (n - 2)) :
-- imply
  let i' : Fin (n - 1) := ⟨i.val, by omega⟩
  let i1 : Fin (n - 1) := ⟨i.val + 1, by omega⟩
  (AlgebraicCombinatorics.simpleTransposition i') * (AlgebraicCombinatorics.simpleTransposition i1) *
    (AlgebraicCombinatorics.simpleTransposition i') =
    (AlgebraicCombinatorics.simpleTransposition i1) * (AlgebraicCombinatorics.simpleTransposition i') *
    (AlgebraicCombinatorics.simpleTransposition i1) := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_braid i

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_eq_swap_explicit_eq
  (k : Fin N)
  (hk : k.val + 1 < N) :
-- imply
  let i : Fin (N - 1) := ⟨k.val, by omega⟩
  AlgebraicCombinatorics.simpleTransposition i = Equiv.swap k ⟨k.val + 1, hk⟩ := by
-- proof
  apply AlgebraicCombinatorics.simpleTransposition_eq_swap_explicit k hk


-- created on 2026-10-11
