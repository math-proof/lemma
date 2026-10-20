import Mathlib
import sympy.Basic
import sympy.combinatorics.permutations.Basics
open AlgebraicCombinatorics
open Equiv


/-! Private helpers supporting full proofs (also @[path] for run.mjs). -/

@[path]
private lemma zpow_apply_sigma_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (k : ℤ)
  (i : Fin n) :
-- imply
  (σ ^ k) (σ i) = σ ((σ ^ k) i) := by
-- proof
  apply Equiv.Perm.zpow_apply_comm σ k 1 (x := i)

@[path]
private lemma zpow_apply_sigma_inv_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n)
  (k : ℤ)
  (i : Fin n) :
-- imply
  (σ ^ k) (σ⁻¹ i) = σ⁻¹ ((σ ^ k) i) := by
-- proof
  simp only [← zpow_neg_one]
  apply Equiv.Perm.zpow_apply_comm σ k (-1) (x := i)

@[path]
private lemma swap_eq_swap_iff_iff
  [DecidableEq X]
  {x y a b : X}
  (hxy : x ≠ y)
  (_ : a ≠ b) :
-- imply
  Equiv.swap x y = Equiv.swap a b ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
-- proof
  constructor
  ·
    intro h
    have hx : (Equiv.swap x y) x = (Equiv.swap a b) x := congrFun (congrArg DFunLike.coe h) x
    have hy : (Equiv.swap x y) y = (Equiv.swap a b) y := congrFun (congrArg DFunLike.coe h) y
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hx hy
    if hxa : x = a then
      subst hxa
      left
      exact ⟨rfl, by simp only [Equiv.swap_apply_left] at hx; exact hx⟩
    else
      have hxb : x = b := by
        have hswap : Equiv.swap a b x = y := by rw [← h]; simp [Equiv.swap_apply_left]
        rw [Equiv.swap_apply_def] at hswap
        split_ifs at hswap with h1
        · exact h1
        · exact (hxy hswap).elim
      subst hxb
      right
      exact ⟨rfl, by simp only [Equiv.swap_apply_right] at hx; exact hx⟩
  ·
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (Equiv.swap_comm y x).symm

@[path]
private lemma swap_eq_iff_sym2_eq_iff
  [DecidableEq X]
  {x₁ y₁ x₂ y₂ : X}
  (h₁ : x₁ ≠ y₁)
  (h₂ : x₂ ≠ y₂) :
-- imply
  Equiv.swap x₁ y₁ = Equiv.swap x₂ y₂ ↔ Sym2.mk x₁ y₁ = Sym2.mk x₂ y₂ := by
-- proof
  rw [Sym2.eq_iff, swap_eq_swap_iff_iff h₁ h₂]

/--
 Canonical pair extracted from a swap (helper def kept local for proofs). 
-/
private noncomputable def swapToPair {X : Type*} [DecidableEq X] (σ : Equiv.Perm X) (hσ : σ.IsSwap) : X × X :=
  let x := Classical.choose hσ
  let hx := Classical.choose_spec hσ
  let y := Classical.choose hx
  (x, y)

@[path]
private lemma swapToPair_spec_eq
  [DecidableEq X]
  (σ : Equiv.Perm X)
  (hσ : σ.IsSwap) :
-- imply
  (Prod.fst (swapToPair σ hσ)) ≠ (Prod.snd (swapToPair σ hσ)) ∧
    σ = Equiv.swap (Prod.fst (swapToPair σ hσ)) (Prod.snd (swapToPair σ hσ)) := by
-- proof
  unfold swapToPair
  simp only
  exact Classical.choose_spec (Classical.choose_spec hσ)

@[path]
private lemma swapToPair_mem_support_is
  [DecidableEq X]
  [Fintype X]
  (σ : Equiv.Perm X)
  (hσ : σ.IsSwap) :
-- imply
  (Prod.fst (swapToPair σ hσ)) ∈ σ.support ∧ (Prod.snd (swapToPair σ hσ)) ∈ σ.support := by
-- proof
  have hne := (swapToPair_spec_eq σ hσ).1
  have heq := (swapToPair_spec_eq σ hσ).2
  have hsupp : σ.support = {(Prod.fst (swapToPair σ hσ)), (Prod.snd (swapToPair σ hσ))} := by
    conv_lhs => rw [heq]
    exact Equiv.Perm.support_swap hne
  refine ⟨?_, ?_⟩
  · simp [hsupp]
  · simp [hsupp]

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
  apply Fintype.card_perm

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_card_eq
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn n) = Nat.factorial n := by
-- proof
  simp [Sn, symmetric_group_card_eq, Fintype.card_fin]

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_zero_card_eq:
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 0) = 1 := by
-- proof
  native_decide

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_one_card_eq:
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 1) = 1 := by
-- proof
  native_decide

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_two_card_eq:
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 2) = 2 := by
-- proof
  native_decide

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma sn_three_card_eq:
-- imply
  Fintype.card (AlgebraicCombinatorics.Sn 3) = 6 := by
-- proof
  native_decide

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma bracket_n_card_eq
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.bracketN n) = n := by
-- proof
  apply Fintype.card_fin n

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
  rfl

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
  apply mul_assoc α β γ

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
  apply one_mul α

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
  apply mul_one α

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
  apply pow_zero α

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
  apply zpow_zero α

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
  apply pow_one α

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
  apply pow_succ α n

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma perm_pow_succ_eq'_eq_eq
  (X : Type*)
  (α : Equiv.Perm X)
  (n : ℕ) :
-- imply
  α ^ (n + 1) = α * α ^ n := by
-- proof
  apply pow_succ' α n

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
  apply zpow_neg_one α

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
  apply mul_inv_cancel α

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
  apply inv_mul_cancel α

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
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply, ih]
    rw [Function.iterate_succ_apply', Function.Commute.iterate_self _ n x]

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
  apply zpow_neg α n

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
  rfl

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
  use f.permCongr σ
  intro y
  simp [Equiv.permCongr_apply]

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
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom, Equiv.permCongr_apply]

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
  apply (symmetricGroup_conj_iso f).bijective

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
  apply (symmetricGroup_conj_iso f).map_mul σ τ

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
  apply (symmetricGroup_conj_iso f).map_one

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
  ext σ y
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom]

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma symmetric_group_iso_of_equiv_eq
  (X Y : Type*)
  (f : X ≃ Y) :
-- imply
  Nonempty (Equiv.Perm X ≃* Equiv.Perm Y) :=
-- proof
  ⟨symmetricGroup_conj_iso f⟩

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
  ext x
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom]

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
  simp [twoLineNotation]

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
  simp only [twoLineNotation, List.getElem_map, List.getElem_finRange]
  simp only [Fin.cast_mk]

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
  simp only [twoLineNotation, List.map_map, Function.comp_def]
  simp only [List.map_id']

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
  simp only [twoLineNotation, List.map_map, Function.comp_def]

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
  constructor
  ·
    intro h
    rw [h]
  ·
    intro h
    ext i : 1
    have h1 := two_line_notation_get_elem_eq σ i.val i.isLt
    have h2 := two_line_notation_get_elem_eq τ i.val i.isLt
    have hi1 : i.val < (twoLineNotation σ).length := by simp [twoLineNotation]
    have hi2 : i.val < (twoLineNotation τ).length := by simp [twoLineNotation]
    have heq : (twoLineNotation σ)[i.val]'hi1 = (twoLineNotation τ)[i.val]'hi2 := by
      simp only [h]
    rw [h1, h2] at heq
    exact Prod.mk.inj heq |>.2

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
  simp [oneLineNotation]

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
  simp only [oneLineNotation, List.getElem_map, List.getElem_finRange]
  simp only [Fin.cast_mk]

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
  simp only [oneLineNotation]
  apply List.Nodup.map σ.injective
  exact List.nodup_finRange n

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
  constructor
  ·
    intro h
    rw [h]
  ·
    intro h
    ext i : 1
    have h1 := one_line_notation_get_elem_eq σ i.val i.isLt
    have h2 := one_line_notation_get_elem_eq τ i.val i.isLt
    have hi1 : i.val < (oneLineNotation σ).length := by simp [oneLineNotation]
    have hi2 : i.val < (oneLineNotation τ).length := by simp [oneLineNotation]
    have heq : (oneLineNotation σ)[i.val]'hi1 = (oneLineNotation τ)[i.val]'hi2 := by
      simp only [h]
    rw [h1, h2] at heq
    exact heq

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma one_line_notation_to_perm_one_line_notation_eq
  {n : ℕ}
  (σ : AlgebraicCombinatorics.Sn n) :
-- imply
  AlgebraicCombinatorics.oneLineNotationToPerm (AlgebraicCombinatorics.oneLineNotation σ) (one_line_notation_length_eq σ)
    (one_line_notation_nodup_is σ) = σ := by
-- proof
  ext i
  simp only [oneLineNotationToPerm, Equiv.ofBijective_apply, oneLineNotation,
             List.getElem_map, List.getElem_finRange, Fin.cast_mk]

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
  rfl

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
  (AlgebraicCombinatorics.cycleDigraph σ).Adj i j :=
-- proof
  ⟨hne, Or.inl h⟩

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
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  ·
    intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hadj ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨_, h | h⟩ := hadj
      ·
        refine ⟨k + 1, ?_⟩
        rw [zpow_add_one, Equiv.Perm.mul_apply, zpow_apply_sigma_eq, hk, h]
      ·
        refine ⟨k - 1, ?_⟩
        rw [zpow_sub_one, Equiv.Perm.mul_apply, zpow_apply_sigma_inv_eq, hk]
        simp [← h]
  ·
    intro ⟨k, hk⟩
    induction k using Int.induction_on generalizing j with
    | zero =>
      simp only [zpow_zero, Equiv.Perm.coe_one, id_eq] at hk
      subst hk
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, zpow_apply_sigma_eq] at hk
      have h1 : Relation.ReflTransGen (cycleDigraph σ).Adj i ((σ ^ n) i) := ih ((σ ^ n) i) rfl
      by_cases heq : (σ ^ n) i = j
      · exact ih j heq
      ·
        exact h1.trans (Relation.ReflTransGen.single ⟨heq, Or.inl hk⟩)
    | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, zpow_apply_sigma_inv_eq] at hk
      have h1 : Relation.ReflTransGen (cycleDigraph σ).Adj i ((σ ^ (-(n : ℤ))) i) :=
        ih ((σ ^ (-(n : ℤ))) i) rfl
      by_cases heq : (σ ^ (-(n : ℤ))) i = j
      · exact ih j heq
      ·
        refine h1.trans (Relation.ReflTransGen.single ⟨heq, Or.inr ?_⟩)
        simp [← hk]

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cycle_digraph_one_eq
  {n : ℕ} :
-- imply
  AlgebraicCombinatorics.cycleDigraph (1 : AlgebraicCombinatorics.Sn n) = ⊥ := by
-- proof
  ext i j
  simp only [cycle_digraph_adj_iff, Equiv.Perm.coe_one, id_eq, SimpleGraph.bot_adj]
  constructor
  ·
    intro ⟨hne, h⟩
    rcases h with rfl | rfl <;> exact hne rfl
  ·
    intro h
    exact h.elim

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
  (AlgebraicCombinatorics.cycleDigraph (Equiv.swap i j)).Adj a b ↔ (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
-- proof
  simp only [cycle_digraph_adj_iff, Equiv.swap_apply_def]
  constructor
  ·
    intro ⟨hne, h⟩
    rcases h with h | h
    ·
      split_ifs at h with h1 h2
      ·
        left
        exact ⟨h1, h.symm⟩
      ·
        right
        exact ⟨h2, h.symm⟩
      · exact (hne h).elim
    ·
      split_ifs at h with h1 h2
      ·
        right
        exact ⟨h.symm, h1⟩
      ·
        left
        exact ⟨h.symm, h2⟩
      · exact (hne h.symm).elim
  ·
    intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    ·
      rw [ha, hb]
      exact ⟨hij, Or.inl (Equiv.swap_apply_left i j)⟩
    ·
      rw [ha, hb]
      exact ⟨hij.symm, Or.inl (Equiv.swap_apply_right i j)⟩

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
  apply Equiv.swap_apply_left i j

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
  apply Equiv.swap_apply_right i j

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
  apply Equiv.swap_apply_of_ne_of_ne hi hj

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
  apply Equiv.swap_comm i j

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
  apply Equiv.symm_swap i j

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
  ext x
  simp [transposition]

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma num_transpositions_is
  (X : Type*)
  [DecidableEq X]
  [Fintype X] :
-- imply
  ∃ (S : Finset (Equiv.Perm X)),     (∀ σ ∈ S, σ.IsSwap) ∧
    (∀ σ : Equiv.Perm X, σ.IsSwap → σ ∈ S) ∧
    S.card = Nat.choose (Fintype.card X) 2 := by
-- proof
  -- The set of all swaps (using support = 2 as decidable characterization)
  let S := Finset.univ.filter (fun σ : Equiv.Perm X => σ.support.card = 2)
  use S
  constructor
  ·
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact Equiv.Perm.card_support_eq_two.mp hσ.2
  constructor
  ·
    intro σ hσ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ σ, Equiv.Perm.card_support_eq_two.mpr hσ⟩
  ·
    -- We need to show S.card = Nat.choose (Fintype.card X) 2
    -- This follows from a bijection with non-diagonal elements of Sym2 X
    let T := Finset.univ.filter (fun z : Sym2 X => ¬z.IsDiag)
    have hT : T.card = Nat.choose (Fintype.card X) 2 := by
      have h := @Sym2.card_subtype_not_diag X _ _
      simp only [Fintype.card_subtype] at h
      exact h
    rw [← hT]
    -- Define the bijection: σ ↦ Sym2.mk (swapToPair σ)
    let iFun : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm X => σ.support.card = 2), Sym2 X :=
      fun σ hσ =>
        Sym2.mk
          (Prod.fst (swapToPair (X := X) σ
            (Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2)))
          (Prod.snd (swapToPair (X := X) σ
            (Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2)))
    apply Finset.card_bij (s := Finset.univ.filter (fun σ : Equiv.Perm X => σ.support.card = 2))
      (t := Finset.univ.filter (fun z : Sym2 X => ¬z.IsDiag)) iFun
    -- hi : i maps S to T
    ·
      intro σ hσ
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      ·
        let h := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2
        rw [Sym2.mk_isDiag_iff]
        exact (swapToPair_spec_eq σ h).1
    -- i_inj : i is injective
    ·
      intro σ₁ hσ₁ σ₂ hσ₂ heq
      have h₁ : σ₁.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ₁).2
      have h₂ : σ₂.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ₂).2
      have hp₁ := swapToPair_spec_eq σ₁ h₁
      have hp₂ := swapToPair_spec_eq σ₂ h₂
      have hsym : Sym2.mk (Prod.fst (swapToPair σ₁ h₁)) (Prod.snd (swapToPair σ₁ h₁)) = Sym2.mk (Prod.fst (swapToPair σ₂ h₂)) (Prod.snd (swapToPair σ₂ h₂)) := heq
      have hswap : Equiv.swap (Prod.fst (swapToPair σ₁ h₁)) (Prod.snd (swapToPair σ₁ h₁)) = Equiv.swap (Prod.fst (swapToPair σ₂ h₂)) (Prod.snd (swapToPair σ₂ h₂)) :=
        (swap_eq_iff_sym2_eq_iff hp₁.1 hp₂.1).mpr hsym
      calc
        _ = Equiv.swap (Prod.fst (swapToPair σ₁ h₁)) (Prod.snd (swapToPair σ₁ h₁)) := hp₁.2
        _ = Equiv.swap (Prod.fst (swapToPair σ₂ h₂)) (Prod.snd (swapToPair σ₂ h₂)) := hswap
        _ = σ₂ := hp₂.2.symm
    -- i_surj : i is surjective
    ·
      intro z hz
      rw [Finset.mem_filter] at hz
      have hnd : ¬z.IsDiag := hz.2
      let p := z.out
      have hp : z = Sym2.mk (Prod.fst p) (Prod.snd p) := (Quot.out_eq z).symm
      have hne : Prod.fst p ≠ Prod.snd p := by
        intro h
        apply hnd
        rwa [hp, Sym2.mk_isDiag_iff]
      let σ := Equiv.swap (Prod.fst p) (Prod.snd p)
      have hσS : σ ∈ S := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        ·
          rw [Equiv.Perm.card_support_eq_two]
          exact ⟨Prod.fst p, Prod.snd p, hne, rfl⟩
      use σ, hσS
      have h : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσS).2
      have hq := swapToPair_spec_eq σ h
      have heq : Equiv.swap (Prod.fst (swapToPair σ h)) (Prod.snd (swapToPair σ h)) = Equiv.swap (Prod.fst p) (Prod.snd p) := hq.2.symm
      have hsym : Sym2.mk (Prod.fst (swapToPair σ h)) (Prod.snd (swapToPair σ h)) = Sym2.mk (Prod.fst p) (Prod.snd p) :=
        (swap_eq_iff_sym2_eq_iff hq.1 hne).mp heq
      rwa [hp]

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
  rfl

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
  simp [simpleTransposition]

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
  simp [simpleTransposition]

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
  simp only [simpleTransposition]
  rw [Equiv.swap_apply_of_ne_of_ne]
  ·
    intro h
    rw [Fin.ext_iff] at h
    exact hi h
  ·
    intro h
    rw [Fin.ext_iff] at h
    exact hi1 h

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
  simp only [simpleTransposition]
  rw [Equiv.Perm.support_swap]
  intro h
  rw [Fin.ext_iff] at h
  simp at h

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
  use ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
  use ⟨i.val + 1, by omega⟩
  constructor
  ·
    intro h
    rw [Fin.ext_iff] at h
    simp at h
  · rfl

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
  apply Equiv.Perm.IsSwap.isCycle
  exact simple_transposition_is_swap_is i

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
  rw [simple_transposition_support_eq]
  rw [Finset.card_pair]
  intro h
  rw [Fin.ext_iff] at h
  simp at h

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
  intro h
  have := simple_transposition_support_card_eq i
  rw [h] at this
  simp at this

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
  simp only [simpleTransposition]
  ext x
  simp

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
  simp [simpleTransposition]

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
  have hi_lt : i.val < n - 1 := i.isLt
  have hj_lt : j.val < n - 1 := j.isLt
  -- Key fact: when |i - j| > 1, the pairs {i, i+1} and {j, j+1} are disjoint
  have hdisj : Equiv.Perm.Disjoint s[i] s[j] := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    simp only [simpleTransposition]
    by_cases hx1 : x.val = i.val
    ·
      right
      rw [Equiv.swap_apply_of_ne_of_ne] <;>
      ·
        intro heq
        rw [Fin.ext_iff] at heq
        simp at heq
        rcases h with h | h <;> omega
    ·
      by_cases hx2 : x.val = i.val + 1
      ·
        right
        rw [Equiv.swap_apply_of_ne_of_ne] <;>
        ·
          intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          rcases h with h | h <;> omega
      ·
        left
        rw [Equiv.swap_apply_of_ne_of_ne]
        ·
          intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          exact hx1 heq
        ·
          intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          exact hx2 heq
  exact hdisj.commute.eq

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
  rfl

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
  simp only [simpleTransposition, Fin.castSucc, Fin.succ, Fin.castLE, Fin.castAdd]

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
  simp [simpleTransposition]

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
  apply List.formPerm_pair i j

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma cyc_nil_eq
  [DecidableEq X] :
-- imply
  AlgebraicCombinatorics.cyc ([] : List X) = 1 := by
-- proof
  apply List.formPerm_nil

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
  apply List.formPerm_singleton x

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
  apply List.formPerm_apply_of_notMem h

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
  apply List.formPerm_cons_cons x y l

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
  apply List.isCycle_formPerm hl hn

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
  apply List.formPerm_apply_mem_eq_next hl x hx

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
  apply List.support_formPerm_le l

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
  apply List.support_formPerm_of_nodup _ hl
  intro x h
  rw [h] at hn
  simp at hn

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
  apply List.formPerm_rotate l hl n

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
  apply cyc_rotate_eq hl 1

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
  AlgebraicCombinatorics.cyc l l[j] = l[(j + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hj)) := by
-- proof
  apply List.formPerm_apply_getElem l hl j hj

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
  (_ : 2 ≤ l'.length) :
-- imply
  AlgebraicCombinatorics.cyc l = AlgebraicCombinatorics.cyc l' ↔ l ~r l' := by
-- proof
  rw [show cyc l = l.formPerm from rfl, show cyc l' = l'.formPerm from rfl]
  constructor
  ·
    intro h
    have := List.formPerm_eq_formPerm_iff hl hl' |>.mp h
    rcases this with hrot | ⟨h1, _⟩
    · exact hrot
    · omega
  ·
    intro h
    exact List.formPerm_eq_of_isRotated hl h

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
  -- Since σ is a cycle with support of size 2, orderOf σ = 2
  have horder : orderOf σ = 2 := by rw [hσ.orderOf, hcard]
  -- So σ² = 1, meaning σ (σ x) = x for all x
  have hsq : σ * σ = 1 := by rw [← pow_two, ← horder]; exact pow_orderOf_eq_one σ
  -- Get a non-fixed point x from the cycle definition
  obtain ⟨x, hx, hcycle⟩ := hσ
  -- Then σ(σ(x)) = x by the above
  have hffx : σ (σ x) = x := by simpa using congr_fun (congrArg (·.toFun) hsq) x
  -- Reconstruct the IsCycle hypothesis
  have hσ' : σ.IsCycle := ⟨x, hx, hcycle⟩
  -- Use the Mathlib lemma that says σ = swap x (σ x)
  exact ⟨x, σ x, fun h => hx h.symm, hσ'.eq_swap_of_apply_apply_eq_self hx hffx⟩

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
  ∃ (S : Finset (AlgebraicCombinatorics.Sn n)),     (∀ σ ∈ S, σ.IsCycle ∧ σ.support.card = k) ∧
    (∀ σ : AlgebraicCombinatorics.Sn n, σ.IsCycle → σ.support.card = k → σ ∈ S) ∧
    S.card = Nat.choose n k * Nat.factorial (k - 1) := by
-- proof
  classical
  -- Define S as the set of all k-cycles
  let S := Finset.univ.filter (fun σ : Sn n => σ.IsCycle ∧ σ.support.card = k)
  use S
  refine ⟨?_, ?_, ?_⟩
  -- First property: every element of S is a k-cycle
  ·
    intro σ hσ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hσ
  -- Second property: every k-cycle is in S
  ·
    intro σ hσ hcard
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ, hcard⟩
  -- Third property: S.card = C(n,k) * (k-1)!
  -- First show S equals the set {g | g.cycleType = {k}}
  ·
    have hS_eq : S = Finset.univ.filter (fun σ => σ.cycleType = {k}) := by
      ext σ
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      ·
        rintro ⟨hσ, hcard⟩
        rw [hσ.cycleType, hcard]
      ·
        intro h
        constructor
        ·
          have : Multiset.card σ.cycleType = 1 := by simp only [h, Multiset.card_singleton]
          exact Equiv.Perm.card_cycleType_eq_one.mp this
        ·
          have hσ : σ.IsCycle := by
            have : Multiset.card σ.cycleType = 1 := by simp only [h, Multiset.card_singleton]
            exact Equiv.Perm.card_cycleType_eq_one.mp this
          have heq : σ.cycleType = {σ.support.card} := hσ.cycleType
          rw [h] at heq
          simp only [Multiset.singleton_inj] at heq
          exact heq.symm
    rw [hS_eq]
    -- Now use card_of_cycleType_singleton from Mathlib
    have h2k : 2 ≤ k := hk
    have hkn' : k ≤ Fintype.card (Fin n) := by simp [hkn]
    have := Equiv.Perm.card_of_cycleType_singleton h2k hkn'
    simp only [Fintype.card_fin] at this
    convert this using 1
    ring

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
  apply hσ.two_le_card_support

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
  rw [← mul_left_cancel_iff (a := σ)]
  simp only [mul_inv_cancel]
  exact h.symm

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
  constructor
  · apply is_involution_eq_inv_eq
  ·
    intro h
    unfold IsInvolution
    calc
      _ = σ * σ⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel σ

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
  constructor
  ·
    intro h x
    have : (σ * σ) x = x := by rw [h]; rfl
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at this
    exact this
  ·
    intro h
    ext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
    exact h x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_iff_forall_iff
  (X : Type*)
  {σ : Equiv.Perm X} :
-- imply
  AlgebraicCombinatorics.IsInvolution σ ↔ ∀ x, σ (σ x) = x :=
-- proof
  is_involution_iff_involutive_iff (σ := σ)

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
  σ (σ x) = x :=
-- proof
  (is_involution_iff_forall_iff (σ := σ)).mp h x

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_one_is
  (X : Type*) :
-- imply
  AlgebraicCombinatorics.IsInvolution (1 : Equiv.Perm X) := by
-- proof
  simp [IsInvolution]

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
  apply transposition_sq_eq_one_eq i j

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
  apply simple_transposition_sq_eq_one_eq i

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
  have h2 : σ ^ 2 = 1 := by
    rwa [pow_two]
  exact orderOf_dvd_of_pow_eq_one h2

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
  apply Nat.le_of_dvd (by norm_num) (is_involution_order_of_dvd_two_eq h)

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_eq_one_iff_order_of_eq_one_iff
  (X : Type*)
  {σ : Equiv.Perm X}
  (_ : AlgebraicCombinatorics.IsInvolution σ) :
-- imply
  σ = 1 ↔ orderOf σ = 1 := by
-- proof
  constructor
  ·
    intro h'
    subst h'
    exact orderOf_one
  ·
    intro h'
    exact orderOf_eq_one_iff.mp h'

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
  have hdvd := is_involution_order_of_dvd_two_eq h
  rcases Nat.dvd_prime Nat.prime_two |>.mp hdvd with h1 | h2
  · exact (hne (orderOf_eq_one_iff.mp h1)).elim
  · exact h2

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
  intro h
  -- h says σ * σ = 1, i.e., σ² = 1
  -- This means orderOf σ divides 2
  have h2 : σ ^ 2 = 1 := by
    rwa [pow_two]
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  -- For a cycle, orderOf σ = #σ.support
  rw [hσ.orderOf] at hdvd
  -- So #σ.support ∣ 2, which means #σ.support ≤ 2
  have hle : σ.support.card ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  -- But we have 2 < #σ.support, contradiction
  omega

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma is_involution_of_disjoint_transpositions_is
  [DecidableEq X]
  {pairs : List (X × X)}
  (hdisjoint : pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2))
  (hdistinct : ∀ p ∈ pairs, Prod.fst p ≠ Prod.snd p) :
-- imply
  AlgebraicCombinatorics.IsInvolution (pairs.map (fun p => AlgebraicCombinatorics.transposition p.1 p.2)).prod := by
-- proof
  unfold IsInvolution
  induction pairs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    set t := transposition p.1 p.2
    set s := (ps.map (fun p => transposition p.1 p.2)).prod
    -- First show t and s commute (because they are disjoint)
    have hcomm : Commute t s := by
      apply Equiv.Perm.Disjoint.commute
      apply Equiv.Perm.disjoint_prod_right
      intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨q, hq_mem, hq_eq⟩ := hg
      subst hq_eq
      have hdisj := List.rel_of_pairwise_cons hdisjoint hq_mem
      obtain ⟨h1, h2, h3, h4⟩ := hdisj
      intro x
      simp only [transposition, Equiv.swap_apply_def]
      by_cases hxp1 : x = p.1
      ·
        right
        subst hxp1
        simp only [h1, ite_false, h2]
      ·
        by_cases hxp2 : x = p.2
        ·
          right
          subst hxp2
          simp only [h3, ite_false, h4]
        ·
          left
          simp only [t, transposition, Equiv.swap_apply_def, hxp1, hxp2, ite_false]
    -- Now use commutativity to rearrange: (t * s)² = t * s * t * s = t * t * s * s = 1 * 1 = 1
    have ht2 : t * t = 1 := transposition_sq_eq_one_eq p.1 p.2
    have hs2 : s * s = 1 := by
      apply ih
      · exact List.Pairwise.of_cons hdisjoint
      ·
        intro q hq
        exact hdistinct q (List.mem_cons.mpr (Or.inr hq))
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [hcomm.eq]
      _ = (t * t) * (s * s) := by group
      _ = 1 * 1 := by rw [ht2, hs2]
      _ = 1 := by group

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
  intro c hc
  -- c is a cycle in the factorization of σ
  have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  have hca := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  -- Since c agrees with σ on its support, and σ² = 1, we have c² = 1
  have hc_sq : c * c = 1 := by
    ext x
    by_cases hx : x ∈ c.support
    ·
      -- x is in the support of c, so c x = σ x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
      have hcx : c x = σ x := hca x hx
      -- c x is also in c.support (since c is a bijection on its support)
      have hcx_mem : c x ∈ c.support := by
        rw [Equiv.Perm.mem_support] at hx ⊢
        intro h_eq
        apply hx
        exact c.injective h_eq
      have hccx : c (c x) = σ (c x) := hca (c x) hcx_mem
      -- σ(σ x) = x since σ² = 1
      have hσσ : (σ * σ) x = x := by rw [h]; rfl
      simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hσσ
      -- c (c x) = σ (c x) = σ (σ x) = x
      calc
        _ = σ (c x) := hccx
        _ = σ (σ x) := by rw [hcx]
        _ = x := hσσ
    ·
      -- x is not in c.support, so c x = x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
      rw [Equiv.Perm.notMem_support.mp hx]
      rw [Equiv.Perm.notMem_support.mp hx]
  -- From c² = 1, we get orderOf c | 2
  have h_order_dvd : orderOf c ∣ 2 := by
    rw [← sq] at hc_sq
    exact orderOf_dvd_of_pow_eq_one hc_sq
  -- For a cycle, orderOf c = c.support.card
  have h_order_eq : orderOf c = c.support.card := hcycle.orderOf
  -- So c.support.card | 2, meaning c.support.card ∈ {1, 2}
  rw [h_order_eq] at h_order_dvd
  -- c.support.card divides 2, so it's 1 or 2
  rcases Nat.dvd_prime Nat.prime_two |>.mp h_order_dvd with h1 | h2
  · omega
  · omega

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
  ∃ pairs : List (X × X),     pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
    (∀ p ∈ pairs, Prod.fst p ≠ Prod.snd p) ∧
    σ = (pairs.map (fun p => AlgebraicCombinatorics.transposition p.1 p.2)).prod := by
-- proof
  -- Get the cycle factors of σ
  obtain ⟨l, hl_nodup, hl_eq⟩ := σ.cycleFactorsFinset.exists_list_nodup_eq
  -- Each cycle in l has support card = 2 (since it's a cycle with support ≤ 2)
  have h_support_eq_two : ∀ c ∈ l, c.support.card = 2 := by
    intro c hc
    have hc' : c ∈ σ.cycleFactorsFinset := by rw [← hl_eq]; exact List.mem_toFinset.mpr hc
    have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc').1
    have hle := involution_cycle_structure_le h c hc'
    have hge := hcycle.two_le_card_support
    omega
  -- Each cycle is a swap
  have h_is_swap : ∀ c ∈ l, c.IsSwap := by
    intro c hc
    exact Equiv.Perm.card_support_eq_two.mp (h_support_eq_two c hc)
  -- Cycles are pairwise disjoint
  have h_disjoint : l.Pairwise Equiv.Perm.Disjoint := by
    have hpw := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ
    rw [← hl_eq] at hpw
    rw [Set.Pairwise, List.coe_toFinset] at hpw
    exact hl_nodup.pairwise_of_forall_ne (fun a ha b hb hab => hpw ha hb hab)
  -- Construct pairs using swapToPair
  let pairs : List (X × X) := l.pmap (fun c hc => swapToPair c (h_is_swap c hc)) (fun _ hc => hc)
  use pairs
  constructor
  ·
    -- Pairwise disjointness of pairs
    rw [List.pairwise_pmap]
    apply List.Pairwise.imp _ h_disjoint
    intro c₁ c₂ hdisj hc₁ hc₂
    have hp₁ := swapToPair_mem_support_is c₁ (h_is_swap c₁ hc₁)
    have hp₂ := swapToPair_mem_support_is c₂ (h_is_swap c₂ hc₂)
    have hdisj_supp : Disjoint c₁.support c₂.support := hdisj.disjoint_support
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj_supp
    constructor
    ·
      intro heq
      have hmem : (Prod.fst (swapToPair c₁ (h_is_swap c₁ hc₁))) ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.1, heq ▸ hp₂.1⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    constructor
    ·
      intro heq
      have hmem : (Prod.fst (swapToPair c₁ (h_is_swap c₁ hc₁))) ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.1, heq ▸ hp₂.2⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    constructor
    ·
      intro heq
      have hmem : (Prod.snd (swapToPair c₁ (h_is_swap c₁ hc₁))) ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.2, heq ▸ hp₂.1⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    ·
      intro heq
      have hmem : (Prod.snd (swapToPair c₁ (h_is_swap c₁ hc₁))) ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.2, heq ▸ hp₂.2⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
  constructor
  ·
    -- Each pair has distinct elements
    intro p hp
    simp only [pairs, List.mem_pmap] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact (swapToPair_spec_eq c (h_is_swap c hc)).1
  ·
    -- Product equals σ
    have h_map : pairs.map (fun p => Equiv.swap (Prod.fst p) (Prod.snd p)) = l := by
      simp only [pairs]
      rw [List.map_pmap]
      have h_eq : ∀ c (hc : c ∈ l),
          Equiv.swap (Prod.fst (swapToPair c (h_is_swap c hc))) (Prod.snd (swapToPair c (h_is_swap c hc))) = c := by
        intro c hc
        exact (swapToPair_spec_eq c (h_is_swap c hc)).2.symm
      rw [show (fun c hc => Equiv.swap (Prod.fst (swapToPair c (h_is_swap c hc)))
          (Prod.snd (swapToPair c (h_is_swap c hc)))) = (fun c _ => c) from funext₂ h_eq]
      simp
    have h_prod : l.prod = σ := by
      have hcomm : (l.toFinset : Set (Equiv.Perm X)).Pairwise Commute := by
        rw [hl_eq]; exact Equiv.Perm.cycleFactorsFinset_mem_commute σ
      have := Equiv.Perm.cycleFactorsFinset_noncommProd (f := σ)
        (Equiv.Perm.cycleFactorsFinset_mem_commute σ)
      have h1 : l.toFinset.noncommProd id hcomm = σ := by simp only [hl_eq]; exact this
      rw [Finset.noncommProd_toFinset l id hcomm hl_nodup] at h1
      simp at h1; exact h1
    rw [← h_prod, ← h_map]

/--
[Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean)
-/
@[path]
private lemma simple_transposition_braid_eq
  (i : Fin (n - 2)) :
-- imply
  let i' : Fin (n - 1) := ⟨i.val, by omega⟩
  let i1 : Fin (n - 1) := ⟨i.val + 1, by omega⟩
  (AlgebraicCombinatorics.simpleTransposition i') * (AlgebraicCombinatorics.simpleTransposition i1) * (AlgebraicCombinatorics.simpleTransposition i') = (AlgebraicCombinatorics.simpleTransposition i1) * (AlgebraicCombinatorics.simpleTransposition i') * (AlgebraicCombinatorics.simpleTransposition i1) := by
-- proof
  ext x
  simp only [simpleTransposition, Equiv.Perm.mul_apply]
  -- Define the three key elements involved in the swaps
  set a : Fin n := ⟨i.val, by omega⟩ with ha
  set b : Fin n := ⟨i.val + 1, by omega⟩ with hb
  set c : Fin n := ⟨i.val + 2, by omega⟩ with hc
  -- Establish that a, b, c are all distinct
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  -- Case analysis on x: either x ∈ {a, b, c} or x is fixed by both sides
  if hxa : x = a then
    subst hxa
    -- x = a: both sides map a ↦ c
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]
    rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left, Equiv.swap_apply_left]
  else if hxb : x = b then
    subst hxb
    -- x = b: both sides fix b
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
  else if hxc : x = c then
    subst hxc
    -- x = c: both sides map c ↦ a
    simp only [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right,
               Equiv.swap_apply_of_ne_of_ne hab hac]
  else
    -- x ∉ {a, b, c}: both sides fix x
    simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne hxb hxc]

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
  simp [simpleTransposition]


-- created on 2026-10-11
