/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SL2Representations
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK

def IsOddInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ) + 1

def IsEvenInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ)

inductive SL2SimpleModule where
  | finiteDim (m : ℕ)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | principalSeriesEven (s : ℂ) (hs : ¬ IsOddInteger s)
  | principalSeriesOdd (s : ℂ) (hs : ¬ IsEvenInteger s)

namespace SL2SimpleModule

def kTypes : SL2SimpleModule → Set ℤ
  | finiteDim m => { n : ℤ | n.natAbs ≤ m ∧ (n : ℤ) % 2 = (m : ℤ) % 2 }
  | discreteSeriesMinus m _ => { n : ℤ | n ≥ (m : ℤ) ∧ (n - (m : ℤ)) % 2 = 0 }
  | discreteSeriesPlus m _ => { n : ℤ | n ≤ -(m : ℤ) ∧ (n + (m : ℤ)) % 2 = 0 }
  | principalSeriesEven _ _ => { n : ℤ | n % 2 = 0 }
  | principalSeriesOdd _ _ => { n : ℤ | n % 2 = 1 ∨ n % 2 = -1 }

noncomputable def casimirEigenvalue : SL2SimpleModule → ℂ
  | finiteDim m => ((m : ℂ) * ((m : ℂ) + 2)) / 4
  | discreteSeriesMinus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | discreteSeriesPlus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | principalSeriesEven s _ => (s ^ 2 - 1) / 4
  | principalSeriesOdd s _ => (s ^ 2 - 1) / 4

def IsIsomorphic : SL2SimpleModule → SL2SimpleModule → Prop
  | finiteDim m₁, finiteDim m₂ => m₁ = m₂
  | discreteSeriesMinus m₁ _, discreteSeriesMinus m₂ _ => m₁ = m₂
  | discreteSeriesPlus m₁ _, discreteSeriesPlus m₂ _ => m₁ = m₂
  | principalSeriesEven s₁ _, principalSeriesEven s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | principalSeriesOdd s₁ _, principalSeriesOdd s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | _, _ => False

end SL2SimpleModule
open SL2SimpleModule

noncomputable def SL2SimpleModule.toIrredGK : SL2SimpleModule → SL2IrredGKModule
  | .finiteDim m => .finiteDim m
  | .discreteSeriesMinus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
  | .discreteSeriesPlus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
  | .principalSeriesEven s _ => .principalSeries s 0
  | .principalSeriesOdd s _ => .principalSeries s 1

/-- Every SL2 irreducible label admits some realization. -/
theorem sl2IrredGKModule_realization_exists
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) :
    Nonempty (SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) := by
  sorry

/-- Classification of irreducible admissible (sl2,K)-modules. -/
theorem sl2_gk_classification
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by
  sorry

/-- Principal series s iso principal series -s (same parity). -/
theorem principalSeries_neg_iso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (ε : ZMod 2)
    (R₁ : SL2IrredGKModule.Realization (.principalSeries s ε) 𝔤 K 𝔨 Ad)
    (R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) ε) 𝔤 K 𝔨 Ad) :
    R₁.gkmod.IsIsomorphicGK R₂.gkmod := by
  sorry

/-- Isomorphic realizations force equal labels, or principal-series negation. -/
theorem sl2_iso_implies_label_match
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ ν : SL2IrredGKModule)
    (Rμ : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad)
    (Rν : SL2IrredGKModule.Realization ν 𝔤 K 𝔨 Ad)
    (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
    μ = ν ∨ (∃ s ε, μ = .principalSeries s ε ∧ ν = .principalSeries (-s) ε) := by
  sorry

/-- Even principal series reducible at odd-integer parameters. -/
theorem principalSeries_even_reducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : IsOddInteger s)
    (R : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad) :
    ¬ R.gkmod.IsIrreducibleGKModule := by
  sorry

/-- Odd principal series reducible at even-integer parameters. -/
theorem principalSeries_odd_reducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : IsEvenInteger s)
    (R : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad) :
    ¬ R.gkmod.IsIrreducibleGKModule := by
  sorry

