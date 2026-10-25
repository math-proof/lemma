/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part10


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

theorem primesCoprime_eq_range (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    primesCoprime K 𝔪 =
      Set.range (fun (p : CoprimePrimes K 𝔪) => primeCoprime K 𝔪 p.1 p.2) := by
  ext I
  simp only [primesCoprime, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨𝔭, h𝔭, rfl⟩
    exact ⟨⟨𝔭, h𝔭⟩, rfl⟩
  · rintro ⟨⟨𝔭, h𝔭⟩, rfl⟩
    exact ⟨𝔭, h𝔭, rfl⟩

theorem freeGroupToCoprime_surjective (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    Function.Surjective (freeGroupToCoprime K 𝔪) := by
  rw [← MonoidHom.range_eq_top]
  rw [show freeGroupToCoprime K 𝔪 = FreeGroup.lift
    (fun p => primeCoprime K 𝔪 p.1 p.2) from rfl]
  rw [FreeGroup.range_lift_eq_closure]
  rw [← primesCoprime_eq_range]
  exact fracIdealsCoprime_closure_primes K 𝔪

theorem fractionalIdeal_mulEquiv_finsupp_primeAsUnit (K : Type u) [Field K] [NumberField K]
    (p : FinitePlace K) :
    fractionalIdeal_mulEquiv_finsupp K (primeAsUnitFracIdeal K p) =
      Multiplicative.ofAdd (Finsupp.single p 1) := by
  rw [← ofAdd_toAdd (fractionalIdeal_mulEquiv_finsupp K (primeAsUnitFracIdeal K p))]
  congr 1
  ext v
  classical
  rw [fractionalIdeal_mulEquiv_finsupp_apply, Finsupp.single_apply, primeAsUnitFracIdeal_val]
  by_cases h : p = v
  · rw [if_pos h, h]; exact FractionalIdeal.count_self K v
  · rw [if_neg h]; exact FractionalIdeal.count_maximal_coprime K v h

theorem freeGroupToCoprime_ker_le_commutator (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    (freeGroupToCoprime K 𝔪).ker ≤ commutator (FreeGroup (CoprimePrimes K 𝔪)) := by


  set α := CoprimePrimes K 𝔪


  let r : FracIdealsCoprime K 𝔪 →* Abelianization (FreeGroup α) :=
    { toFun := fun I =>
        let exps := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I.val)

        let exps_restricted : α →₀ ℤ :=
          Finsupp.comapDomain Subtype.val exps (Subtype.val_injective.injOn)

        Additive.toMul (Finsupp.toFreeAbelianGroup exps_restricted)
      map_one' := by
        dsimp only
        conv_lhs => rw [show (1 : FracIdealsCoprime K 𝔪).val = 1 from rfl]
        rw [map_one, toAdd_one, Finsupp.comapDomain_zero, map_zero]
        exact toMul_zero
      map_mul' := fun a b => by
        dsimp only
        conv_lhs => rw [show (a * b : FracIdealsCoprime K 𝔪).val = a.val * b.val from rfl]
        rw [map_mul, toAdd_mul, Finsupp.comapDomain_add, map_add]
        exact toMul_add _ _ }


  have hretract : r.comp (freeGroupToCoprime K 𝔪) = Abelianization.of := by


    ext p


    simp only [MonoidHom.comp_apply, freeGroupToCoprime, FreeGroup.lift_apply_of]


    change (fun I =>
      let exps := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I.val)
      let exps_restricted : α →₀ ℤ :=
        Finsupp.comapDomain Subtype.val exps (Subtype.val_injective.injOn)
      Additive.toMul (Finsupp.toFreeAbelianGroup exps_restricted))
      (primeCoprime K 𝔪 p.1 p.2) = _

    simp only [primeCoprime_val, fractionalIdeal_mulEquiv_finsupp_primeAsUnit, toAdd_ofAdd]

    rw [Finsupp.comapDomain_single]

    simp [Finsupp.toFreeAbelianGroup]

    rfl

  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hx
  have := congr_fun (congr_arg DFunLike.coe hretract) x
  simp only [MonoidHom.comp_apply] at this
  rw [hx, map_one] at this
  exact this.symm

theorem artinMap_ker_condition (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) :
    (freeGroupToCoprime K 𝔪).ker ≤ (freeGroupToGal K L 𝔪).ker := by
  haveI : IsGalois K L := KroneckerWeber.IsAbelianExtension.isGalois


  letI galCommGroup : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with
      mul_comm := KroneckerWeber.IsAbelianExtension.comm }


  have hcomm_gal : commutator (FreeGroup (CoprimePrimes K 𝔪)) ≤ (freeGroupToGal K L 𝔪).ker :=
    Abelianization.commutator_subset_ker _


  have hker_le_comm : (freeGroupToCoprime K 𝔪).ker ≤ commutator (FreeGroup (CoprimePrimes K 𝔪)) :=
    freeGroupToCoprime_ker_le_commutator K 𝔪
  exact le_trans hker_le_comm hcomm_gal

theorem artinMapExists (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) :
    ∃ (ψ : FracIdealsCoprime K 𝔪 →* (L ≃ₐ[K] L)),
      ∀ (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0),
        ψ (primeCoprime K 𝔪 𝔭 h𝔭) = FrobeniusAutomorphism K L 𝔭 := by

  let ψ := (MonoidHom.liftOfSurjective (freeGroupToCoprime K 𝔪)
    (freeGroupToCoprime_surjective K 𝔪))
    ⟨freeGroupToGal K L 𝔪, artinMap_ker_condition K L 𝔪⟩
  refine ⟨ψ, fun 𝔭 h𝔭 => ?_⟩


  show ψ ((fun (p : CoprimePrimes K 𝔪) => primeCoprime K 𝔪 p.1 p.2) ⟨𝔭, h𝔭⟩) = FrobeniusAutomorphism K L 𝔭

  have h1 : (fun p => primeCoprime K 𝔪 p.1 p.2) (⟨𝔭, h𝔭⟩ : CoprimePrimes K 𝔪) =
    freeGroupToCoprime K 𝔪 (FreeGroup.of ⟨𝔭, h𝔭⟩) := by
    simp [freeGroupToCoprime]
  rw [h1]
  simp only [ψ, MonoidHom.liftOfRightInverse_comp_apply]
  simp [freeGroupToGal]

end RayClassField
end
