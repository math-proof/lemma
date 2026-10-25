/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3
import Lemma.Nat.TypeA_CoxeterMatrixA
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompleteLattice.Finset


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
