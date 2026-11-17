/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.CompleteLattice.Finset

@[expose] public section

namespace GLnBuilding

open Submodule Module

variable (k : Type*) [Field k] (n : ℕ)

/-- Convert a basis $b$ of $k^n$ into a frame by taking lines $L_i = k \cdot b_i$. -/
noncomputable def frameOfBasis (b : Basis (Fin n) k (Vec k n)) : Frame k n where
  lines i := k ∙ b i
  one_dim i := finrank_span_singleton (b.ne_zero i)
  indep := b.linearIndependent.iSupIndep_span_singleton
  spanning := by
    rw [← span_range_eq_iSup]
    exact b.span_eq

end GLnBuilding
