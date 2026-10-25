/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Def.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- A homomorphism of fusion rings, represented combinatorially by an integer matrix `M`
on the bases satisfying unit-preservation and a fusion-multiplication identity. -/
structure FusionRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (R : FusionRing ι) (S : FusionRing κ) where
  M : ι → κ → ℤ
  map_unit : ∀ l, M R.unit l = if l = S.unit then 1 else 0
  map_mul : ∀ i j l,
    (Finset.univ.sum fun k => (R.N i j k : ℤ) * M k l) =
    (Finset.univ.sum fun p => Finset.univ.sum fun q => M i p * M j q * (S.N p q l : ℤ))

end FusionRing
