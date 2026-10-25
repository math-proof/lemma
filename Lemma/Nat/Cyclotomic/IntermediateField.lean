import Mathlib
import sympy.Basic
import Def.NumberTheory.Cyclotomic.IntermediateField
open scoped IntermediateField IsMulCommutative
open CyclotomicField


namespace CyclotomicField

/--
[finrank_intermediateFieldOfFinrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
lemma finrank_intermediateFieldOfFinrank
  {p s : ℕ}
-- given
  (hp : p.Prime)
  (hs : s ∣ p - 1) :
-- imply
  Module.finrank ℚ (intermediateFieldOfFinrank p s hp hs) = s :=
-- proof
  (existsUnique_intermediateField_finrank p s hp hs).choose_spec.1

end CyclotomicField

namespace CyclotomicField

/--
[eq_intermediateFieldOfFinrank_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
lemma eq_intermediateFieldOfFinrank_iff
  {p s : ℕ}
  {K : IntermediateField ℚ (CyclotomicField p ℚ)}
-- given
  (hp : p.Prime)
  (hs : s ∣ p - 1) :
-- imply
  K = intermediateFieldOfFinrank p s hp hs ↔ Module.finrank ℚ K = s := by
-- proof
  constructor
  · rintro rfl
    exact finrank_intermediateFieldOfFinrank p s hp hs
  · intro hK
    exact (existsUnique_intermediateField_finrank p s hp hs).unique hK
      (finrank_intermediateFieldOfFinrank p s hp hs)

end CyclotomicField

namespace CyclotomicField

/--
[sup_eq_top_of_lcm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
lemma sup_eq_top_of_lcm_eq
  {n₀ n₁ m : ℕ} [NeZero n₀] [NeZero n₁]
  {E₀ E₁ : IntermediateField ℚ (CyclotomicField m ℚ)} [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
-- given
  (hlcm : Nat.lcm n₀ n₁ = m) :
-- imply
  E₀ ⊔ E₁ = ⊤ := by
-- proof
  have h_sup_cyc : IsCyclotomicExtension {Nat.lcm n₀ n₁} ℚ ↥(E₀ ⊔ E₁) :=
    @IntermediateField.isCyclotomicExtension_lcm_sup ℚ (CyclotomicField m ℚ) _ _ _
      n₀ n₁ E₀ E₁ ‹IsCyclotomicExtension {n₀} ℚ ↥E₀›
      ‹IsCyclotomicExtension {n₁} ℚ ↥E₁› ‹NeZero n₀› ‹NeZero n₁›
  rw [hlcm] at h_sup_cyc
  have h_top_cyc : IsCyclotomicExtension {m} ℚ
    (⊤ : IntermediateField ℚ (CyclotomicField m ℚ)) := by
    have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
      CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
    exact IsCyclotomicExtension.equiv _ ℚ _ IntermediateField.topEquiv.symm
  exact @IntermediateField.isCyclotomicExtension_eq {m} ℚ _ _ _ _ (E₀ ⊔ E₁) ⊤
    h_sup_cyc h_top_cyc

end CyclotomicField

namespace CyclotomicField

/--
[inf_ne_bot_of_lt_of_lcm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/IntermediateField.lean)
-/
@[path]
lemma inf_ne_bot_of_lt_of_lcm_eq
  {n₀ n₁ m : ℕ} [NeZero n₀] [NeZero n₁]
  {E₀ E₁ : IntermediateField ℚ (CyclotomicField m ℚ)} [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
  {F : IntermediateField ℚ (CyclotomicField m ℚ)}
-- given
  (hlcm : Nat.lcm n₀ n₁ = m)
  (hE₀F : E₀ < F) :
-- imply
  F ⊓ E₁ ≠ ⊥ := by
-- proof
  have hsup := sup_eq_top_of_lcm_eq n₀ n₁ m E₀ E₁ hlcm
  have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  have : NumberField (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.numberField {m} ℚ (CyclotomicField m ℚ)
  have : IsAbelianGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {m} ℚ (CyclotomicField m ℚ)
  let _ : IsModularLattice (IntermediateField ℚ (CyclotomicField m ℚ)) :=
    IsAbelianGalois.isModularLattice_intermediateField
  intro h
  have hle : E₀ ≤ F := le_of_lt hE₀F
  have key := sup_inf_assoc_of_le E₁ hle
  rw [hsup, top_inf_eq] at key
  rw [inf_comm] at h
  rw [h, sup_bot_eq] at key
  exact lt_irrefl F (key ▸ hE₀F)

end CyclotomicField

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


-- created on 2026-10-20
-- updated on 2026-10-23
