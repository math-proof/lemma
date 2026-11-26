import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.HigherDerivation
open TensorCategories


/--
[HigherDerivationSystem.χ_one_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_one_mul
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  {a b : A}
-- given
  (hds : HigherDerivationSystem k A ε) :
-- imply
  hds.χ 1 (a * b) = hds.χ 1 a * ε b + ε a * hds.χ 1 b := by
-- proof
  have h := hds.χ_mul 1 a b
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
    zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply] at h
  rw [h]; ring


/--
[χ_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_apply_zero
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  (hds : HigherDerivationSystem k A ε)
  (a : A) :
  hds.χ 0 a = ε a := by
  rw [hds.χ_zero, AlgHom.toLinearMap_apply]


/--
[χ_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_one_one
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  (hds : HigherDerivationSystem k A ε) :
  hds.χ 1 1 = 0 := by
  have h := hds.χ_mul 1 1 1
  simp only [mul_one, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply, map_one, one_mul, mul_one] at h
  have := sub_eq_zero.mpr h; simp at this; exact this


/--
[χ_one_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_one_algebraMap
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  (hds : HigherDerivationSystem k A ε)
  (r : k) :
  hds.χ 1 (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower, χ_one_one hds, smul_zero]


/--
[χ_pow_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_pow_vanish
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  (hds : HigherDerivationSystem k A ε)
  {a : A} (ha : ε a = 0) (m n : ℕ) (hmn : m < n) :
  hds.χ m (a ^ n) = 0 := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', hds.χ_mul m a (a ^ n)]
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_range] at hj
    by_cases hj0 : j = 0
    · subst hj0; simp [χ_apply_zero hds, ha]
    · rw [ih (m - j) (by omega)]; ring


/--
[χ_pow_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_pow_diagonal
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  (hds : HigherDerivationSystem k A ε)
  {a : A} (ha : ε a = 0) (n : ℕ) :
  hds.χ n (a ^ n) = (n.factorial : k) * (hds.χ 1 a) ^ n := by
  induction n with
  | zero => simp [χ_apply_zero hds, map_one]
  | succ n ih =>
    rw [pow_succ', hds.χ_mul (n + 1) a (a ^ n)]
    have hsum : ∀ j < (n + 2),
      ((n + 1).choose j : k) * hds.χ j a * hds.χ ((n + 1) - j) (a ^ n) =
      if j = 1 then (↑(n + 1) : k) * hds.χ 1 a * ((↑n.factorial : k) * (hds.χ 1 a) ^ n)
      else 0 := by
      intro j hj
      by_cases hj1 : j = 1
      · subst hj1; simp [Nat.choose_one_right, ih]
      · simp only [hj1, ite_false]
        by_cases hj0 : j = 0
        · subst hj0; simp [χ_apply_zero hds, ha]
        · rw [χ_pow_vanish hds ha _ n (by omega)]; ring
    rw [Finset.sum_congr rfl (fun j hj => hsum j (Finset.mem_range.mp hj)), Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [ite_eq_left (by omega : 1 < n + 2), Nat.factorial_succ, Nat.cast_mul, pow_succ]; ring


/--
[coeff_zero_of_sum_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma coeff_zero_of_sum_pow_eq_zero
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  {a : A}
  {s : Finset ℕ}
  {g : ℕ → k}
  {i : ℕ}
-- given
  (hds : HigherDerivationSystem k A ε)
  (ha : ε a = 0)
  (hne : hds.χ 1 a ≠ 0)
  (hzero : ∑ j ∈ s, g j • a ^ j = 0)
  (hi : i ∈ s) :
-- imply
  g i = 0 := by
-- proof
  suffices key : ∀ n, ∀ j ∈ s, j < n → g j = 0 by
    exact key (i + 1) i hi (Nat.lt_succ_iff.mpr le_rfl)
  intro n
  induction n with
  | zero => intro j _ hjn; omega
  | succ n ih =>
    intro j hj hjn
    by_cases hjn' : j < n
    · exact ih j hj hjn'
    · replace hjn : j = n := by omega
      subst hjn
      have heval : ∑ j' ∈ s, g j' • hds.χ j (a ^ j') = 0 := by
        have := congr_arg (hds.χ j) hzero
        simp only [map_sum, LinearMap.map_smul_of_tower, map_zero] at this; exact this
      rw [← Finset.add_sum_erase s _ hj] at heval
      have : ∑ j' ∈ s.erase j, g j' • hds.χ j (a ^ j') = 0 := by
        apply Finset.sum_eq_zero; intro j' hj'
        have hne' := Finset.ne_of_mem_erase hj'
        have hj'_mem := Finset.mem_of_mem_erase hj'
        by_cases hjlt' : j' < j
        · rw [ih j' hj'_mem hjlt', zero_smul]
        · rw [χ_pow_vanish hds ha j j' (by omega), smul_zero]
      rw [this, add_zero, χ_pow_diagonal hds ha, smul_eq_mul] at heval
      exact (mul_eq_zero.mp heval).resolve_right
        (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ hne))


/--
[powers_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma powers_linearIndependent
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  {a : A}
-- given
  (hds : HigherDerivationSystem k A ε)
  (ha : ε a = 0)
  (hne : hds.χ 1 a ≠ 0) :
-- imply
  LinearIndependent k (fun n : ℕ => a ^ n) :=
-- proof
  linearIndependent_iff'.mpr fun _s _g hsum _i hi =>
    coeff_zero_of_sum_pow_eq_zero hds ha hne hsum hi


/--
[higher_derivation_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
private lemma higher_derivation_vanishes_eq
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  [FiniteDimensional k A]
-- given
  (hds : HigherDerivationSystem k A ε) :
-- imply
  hds.χ 1 = 0 := by
-- proof
  by_contra hne
  have hne' : ∃ a₀ : A, hds.χ 1 a₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (LinearMap.ext h)
  obtain ⟨a₀, ha₀⟩ := hne'
  set a := a₀ - algebraMap k A (ε a₀)
  have ha_ker : ε a = 0 := by
    show ε (a₀ - algebraMap k A (ε a₀)) = 0
    rw [map_sub, AlgHom.commutes]; exact sub_self _
  have hχ₁a : hds.χ 1 a ≠ 0 := by
    show hds.χ 1 (a₀ - algebraMap k A (ε a₀)) ≠ 0
    rw [map_sub, χ_one_algebraMap hds, sub_zero]; exact ha₀
  have hli := powers_linearIndependent hds ha_ker hχ₁a
  set N := Module.finrank k A + 1
  have hli_fin : LinearIndependent k ((fun n : ℕ => a ^ n) ∘ (Fin.val : Fin N → ℕ)) :=
    hli.comp Fin.val Fin.val_injective
  have hcard := hli_fin.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega


-- created on 2026-10-23
-- updated on 2026-11-26
