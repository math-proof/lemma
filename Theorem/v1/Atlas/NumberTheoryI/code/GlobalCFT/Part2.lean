/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part2


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

lemma IsRayGenerator_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (I : FracIdealsCoprime K 𝔫) (hI : IsRayGenerator 𝔫 I) :
    IsRayGenerator 𝔪 (Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h) I) := by
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  ·
    simp only [Subgroup.coe_inclusion]
    exact hprinc
  ·
    intro v hv
    have hv_n : 𝔫 (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪 (Place.finite v) : ℤ) ≤ (𝔫 (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
        ≤ ↑(Multiplicative.ofAdd (-(𝔫 (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
          simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
          linarith
  ·
    intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

theorem RayGroup.inclusion_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    ∀ x : FracIdealsCoprime K 𝔫,
      x ∈ RayGroup K 𝔫 → (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) x ∈ RayGroup K 𝔪 := by

  intro x hx
  let f := FracIdealsCoprime.inclusion K 𝔪 𝔫 h

  have hmem : f x ∈ Subgroup.map f (RayGroup K 𝔫) := ⟨x, hx, rfl⟩

  rw [show RayGroup K 𝔫 = Subgroup.closure {I | IsRayGenerator 𝔫 I} from rfl,
      MonoidHom.map_closure] at hmem

  have himg_sub : f '' {I | IsRayGenerator 𝔫 I} ⊆ {I | IsRayGenerator 𝔪 I} := by
    rintro _ ⟨I, hI, rfl⟩
    exact IsRayGenerator_inclusion K 𝔪 𝔫 h I hI
  exact Subgroup.closure_mono himg_sub hmem

end ArtinSymbol
end
