/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
public import Theorem.Fin.EqLinesFrameOfBasis
public import Lemma.Fin.All_Eq_Val.of.Eq.Eq_0.StrictMono
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisFromFlagProof
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.CompleteLattice.Finset


public section

namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


/-- Hypothesis: any two chambers $\sigma, \tau$ admit a common adapted frame $F$ — i.e.\ a
frame compatible with every subspace appearing in either chamber's chain. -/
structure TwoChamberFrameHyp (k : Type*) [Field k] (n : ℕ) where
  frame_of_two_chambers : ∀ (σ τ : SubspaceFlag k n),
    IsChamber k n σ →
    IsChamber k n τ →
    ∃ F : Frame k n, (∀ V ∈ σ.chain, F.IsCompatible k n V) ∧
                      (∀ V ∈ τ.chain, F.IsCompatible k n V)


end GLnBuilding
