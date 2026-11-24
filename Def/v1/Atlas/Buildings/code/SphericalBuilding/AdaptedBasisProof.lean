module
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
public import Theorem.Fin.EqLinesFrameOfBasis
public import Theorem.Fin.All_Eq_Val.of.Eq.Eq_0.StrictMono
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisFromFlagProof
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.CompleteLattice.Finset
public import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


/-- Combine the two-chamber frame hypothesis with flag completion to deduce the
common-apartment property: any two flags $\sigma, \tau$ lie in a common apartment, by first
completing each to a chamber and then applying `TwoChamberFrameHyp`. -/
noncomputable def commonApartmentFromHyps (n : ℕ) (hn : n ≥ 2)
    (h : TwoChamberFrameHyp k n) : CommonApartmentHyp k n where
  refine_flags := fun σ τ => by

    obtain ⟨σ_chain, hσ_len, hσ_chain, hσ_proper, hσ_contains⟩ :=
      flag_completion n hn σ.chain σ.chain_nonempty
        σ.chain_strictly_increasing σ.chain_proper
    let σ' : SubspaceFlag k n :=
      { chain := σ_chain
        chain_nonempty := by intro h; simp [h] at hσ_len; omega
        chain_strictly_increasing := hσ_chain
        chain_proper := hσ_proper }
    have hσ_chamber : IsChamber k n σ' := hσ_len

    obtain ⟨τ_chain, hτ_len, hτ_chain, hτ_proper, hτ_contains⟩ :=
      flag_completion n hn τ.chain τ.chain_nonempty
        τ.chain_strictly_increasing τ.chain_proper
    let τ' : SubspaceFlag k n :=
      { chain := τ_chain
        chain_nonempty := by intro h; simp [h] at hτ_len; omega
        chain_strictly_increasing := hτ_chain
        chain_proper := hτ_proper }
    have hτ_chamber : IsChamber k n τ' := hτ_len

    obtain ⟨F, hF_σ, hF_τ⟩ := h.frame_of_two_chambers σ' τ' hσ_chamber hτ_chamber
    exact ⟨F, fun V hV => hF_σ V (hσ_contains V hV),
               fun V hV => hF_τ V (hτ_contains V hV)⟩

end GLnBuilding
