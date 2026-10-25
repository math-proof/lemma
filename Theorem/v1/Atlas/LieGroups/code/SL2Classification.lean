/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK
import Def.v1.Atlas.LieGroups.code.SL2Classification.Part2
open SL2SimpleModule


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

