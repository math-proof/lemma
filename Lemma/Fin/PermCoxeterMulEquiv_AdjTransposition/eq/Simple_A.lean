import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism
open Equiv Equiv.Perm Function Set SymmetricCoxeter


/--
[permCoxeterMulEquiv_adjTransposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {i : Fin n} :
-- imply
  permCoxeterMulEquiv n (adjTransposition n i) = CoxeterMatrix.simple (CoxeterMatrix.A n) i := by
-- proof
  simp only [permCoxeterMulEquiv]
  rw [MulEquiv.symm_apply_eq]
  simp [MulEquiv.ofBijective_apply, coxeterToPermHom_generator]


/--
[swap_mul_swap_common_first_pow_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma swap_mul_swap_common_first_pow_three_eq
  [Fintype α]
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c) :
-- imply
  (Equiv.swap a b * Equiv.swap a c) ^ 3 = 1 := by
-- proof
  apply SymmetricCoxeter.swap_mul_swap_common_first_pow_three hab hac hbc

/--
[swap_mul_swap_adjacent_pow_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma swap_mul_swap_adjacent_pow_three_eq
  [Fintype α]
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
-- proof
  apply SymmetricCoxeter.swap_mul_swap_adjacent_pow_three hab hbc hac

/--
[succ_eq_castSucc_of_val_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma succ_eq_castSucc_of_val_succ_eq
  {n : ℕ}
  {i j : Fin n}
-- given
  (h : (i : ℕ) + 1 = (j : ℕ)) :
-- imply
  Fin.succ i = Fin.castSucc j := by
-- proof
  apply SymmetricCoxeter.succ_eq_castSucc_of_val_succ h

/--
[adjTransposition_coxeter_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma adjTransposition_coxeter_rel_eq
  {n : ℕ}
  {i j : Fin n} :
-- imply
  (adjTransposition n i * adjTransposition n j) ^ (CoxeterMatrix.A n i j) = 1 := by
-- proof
  apply SymmetricCoxeter.adjTransposition_coxeter_rel n i j

/--
[adjTransposition_lift_rels](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma adjTransposition_lift_rels_eq
  {n : ℕ} :
-- imply
  ∀ r ∈ (CoxeterMatrix.A n).relationsSet, FreeGroup.lift (adjTransposition n) r = 1 := by
-- proof
  apply SymmetricCoxeter.adjTransposition_lift_rels n

/--
[coxeterToPermHom_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma coxeterToPermHom_generator_eq
  {n : ℕ}
  {i : Fin n} :
-- imply
  coxeterToPermHom n (CoxeterMatrix.simple (CoxeterMatrix.A n) i) = adjTransposition n i := by
-- proof
  apply SymmetricCoxeter.coxeterToPermHom_generator n i

/--
[coxeterToPermHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma coxeterToPermHom_surjective_eq
  {n : ℕ} :
-- imply
  Function.Surjective (coxeterToPermHom n) := by
-- proof
  apply SymmetricCoxeter.coxeterToPermHom_surjective n

/--
[coxeterToPermHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean)
-/
private lemma coxeterToPermHom_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (coxeterToPermHom n) := by
-- proof
  apply SymmetricCoxeter.coxeterToPermHom_injective n


-- created on 2026-10-23
-- updated on 2026-10-24
