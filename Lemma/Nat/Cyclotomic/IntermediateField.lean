import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.IntermediateField
open scoped IntermediateField IsMulCommutative
open CyclotomicField


/--
[existsUnique_intermediateField_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
private lemma existsUnique_intermediateField_finrank_eq
  {p s : ℕ}
-- given
  (hp : p.Prime)
  (hs : s ∣ p - 1) :
-- imply
  ∃! K : IntermediateField ℚ (CyclotomicField p ℚ), Module.finrank ℚ K = s := by
-- proof
  apply CyclotomicField.existsUnique_intermediateField_finrank p s hp hs

/--
[finrank_intermediateFieldOfFinrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
private lemma finrank_intermediateFieldOfFinrank_eq
  {p s : ℕ}
-- given
  (hp : p.Prime)
  (hs : s ∣ p - 1) :
-- imply
  Module.finrank ℚ (intermediateFieldOfFinrank p s hp hs) = s := by
-- proof
  apply CyclotomicField.finrank_intermediateFieldOfFinrank p s hp hs

/--
[eq_intermediateFieldOfFinrank_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
private lemma eq_intermediateFieldOfFinrank_iff_eq
  {p s : ℕ}
  {K : IntermediateField ℚ (CyclotomicField p ℚ)}
-- given
  (hp : p.Prime)
  (hs : s ∣ p - 1) :
-- imply
  K = intermediateFieldOfFinrank p s hp hs ↔ Module.finrank ℚ K = s := by
-- proof
  apply CyclotomicField.eq_intermediateFieldOfFinrank_iff p s hp hs K

/--
[sup_eq_top_of_lcm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
private lemma sup_eq_top_of_lcm_eq_eq
  {n₀ n₁ m : ℕ} [NeZero n₀] [NeZero n₁]
  {E₀ E₁ : IntermediateField ℚ (CyclotomicField m ℚ)} [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
-- given
  (hlcm : Nat.lcm n₀ n₁ = m) :
-- imply
  E₀ ⊔ E₁ = ⊤ := by
-- proof
  apply CyclotomicField.sup_eq_top_of_lcm_eq n₀ n₁ m E₀ E₁ hlcm

/--
[inf_ne_bot_of_lt_of_lcm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
private lemma inf_ne_bot_of_lt_of_lcm_eq_eq
  {n₀ n₁ m : ℕ} [NeZero n₀] [NeZero n₁]
  {E₀ E₁ : IntermediateField ℚ (CyclotomicField m ℚ)} [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
  {F : IntermediateField ℚ (CyclotomicField m ℚ)}
-- given
  (hlcm : Nat.lcm n₀ n₁ = m)
  (hE₀F : E₀ < F) :
-- imply
  F ⊓ E₁ ≠ ⊥ := by
-- proof
  apply CyclotomicField.inf_ne_bot_of_lt_of_lcm_eq n₀ n₁ m E₀ E₁ F hlcm hE₀F


-- created on 2026-10-20
