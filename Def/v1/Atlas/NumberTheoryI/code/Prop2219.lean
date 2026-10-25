/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AnalyticClassNumber
import Instance.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor1838


noncomputable section

open scoped NumberField

open Complex Finset Section19

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def halfPlane (K : Type u) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}

noncomputable def nonzeroIdealToFracIdealCoprime (K : Type*) [Field K] [NumberField K]
    (𝔪 : Modulus K) (I : Ideal (𝓞 K)) (_hI : I ≠ ⊥)
    (hcop : IsCoprime I 𝔪.finitePartIdeal) : FracIdealsCoprime K 𝔪 :=
  toFracIdealsCoprime I hcop

def idealInRayClass (𝔪 : Modulus K) (I : Ideal (𝓞 K)) : RayClassGroup K 𝔪 := by
  classical
  exact if h : I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal then
    toRayClass K 𝔪 (nonzeroIdealToFracIdealCoprime K 𝔪 I h.1 h.2)
  else 1

def rayClassPartialZeta_coeffs {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℕ → ℂ :=
  fun n => if n = 0 then 0
    else (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ} : ℂ)

def rayClassPartialZeta {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  LSeries (rayClassPartialZeta_coeffs γ)

def rayClassPartialZeta_residue_val {𝔪 : Modulus K}
    (_γ : RayClassGroup K 𝔪) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)

def rayClassPartialZeta_ext {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  dirichletSeriesContinuation (rayClassPartialZeta_coeffs γ) (rayClassPartialZeta_residue_val γ)

def rayClassPartialZeta_residue (𝔪 : Modulus K) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)

def rayClassPartialZeta_regularPart {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  dirichletSeriesAbel
    (fun n => rayClassPartialZeta_coeffs γ n - rayClassPartialZeta_residue_val γ)

def weberLFunction_combinedCoeffs {𝔪 : Modulus K}
    (χ : RayClassChar K 𝔪) : ℕ → ℂ :=
  fun n => ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) • (rayClassPartialZeta_coeffs γ n)

end RayClassField
end
