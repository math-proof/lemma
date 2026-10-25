/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/PiFieldDecomposition.lean -/

-- MathlibExtTest/RingTheory/PiFieldDecomposition.lean

import Def.RingTheory.PiFieldDecomposition
import Lemma.Int.PiFieldDecomposition
open PiFieldQuotient


/-- Identity on the two-factor product preserves both factors and their multiplicity. -/
example :
    ∃ σ : Fin 2 ≃ Fin 2,
      ∀ i, Nonempty ((fun _ : Fin 2 => ℚ) i ≃ₐ[ℚ] (fun _ : Fin 2 => ℚ) (σ i)) :=
  exists_indexEquiv_algEquiv
    (AlgEquiv.refl : (∀ _ : Fin 2, ℚ) ≃ₐ[ℚ] (∀ _ : Fin 2, ℚ))

/-- Destructure the result and extract the factorwise equivalence at an index. -/
example : ∃ _σ : Fin 2 ≃ Fin 2, Nonempty (ℚ ≃ₐ[ℚ] ℚ) := by
  obtain ⟨σ, hσ⟩ :=
    exists_indexEquiv_algEquiv
      (AlgEquiv.refl : (∀ _ : Fin 2, ℚ) ≃ₐ[ℚ] (∀ _ : Fin 2, ℚ))
  exact ⟨σ, hσ 0⟩

/-- Singleton indices `Unit` and `Fin 1` require only `[Finite]`, without a public
`DecidableEq` assumption. -/
example : ∃ _ : Unit ≃ Fin 1, ∀ _i : Unit, Nonempty (ℚ ≃ₐ[ℚ] ℚ) := by
  let e : (∀ _ : Unit, ℚ) ≃ₐ[ℚ] (∀ _ : Fin 1, ℚ) :=
    { toFun := fun f _ => f Unit.unit
      invFun := fun g _ => g 0
      left_inv := fun f => by ext x; cases x; rfl
      right_inv := fun g => by ext x; fin_cases x; rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  simpa using exists_indexEquiv_algEquiv e

