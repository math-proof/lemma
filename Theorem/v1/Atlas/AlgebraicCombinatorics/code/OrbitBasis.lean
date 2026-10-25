/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis
set_option autoImplicit false


noncomputable section

open scoped Classical

open Finset Finsupp MulAction Function Module

namespace OrbitBasis

variable (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α] [MulAction G α]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

lemma rep_mem_orbit (O : orbitRel.Quotient G α) :
    rep G α O ∈ orbitRel.Quotient.orbit O :=
  (orbitRel.Quotient.nonempty_orbit O).choose_spec

lemma mk_rep (O : orbitRel.Quotient G α) :
    (Quotient.mk'' (rep G α O) : orbitRel.Quotient G α) = O :=
  orbitRel.Quotient.mem_orbit.mp (rep_mem_orbit G α O)

end OrbitBasis
end
