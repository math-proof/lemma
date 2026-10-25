/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part7


noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

instance instNormOneClass_Completion (w : InfinitePlace K) : NormOneClass w.Completion where
  norm_one := by
    have : (1 : w.Completion) = algebraMap K w.Completion 1 := (map_one _).symm
    rw [this, show algebraMap K w.Completion 1 =
      (↑((WithAbs.equiv w.1).symm 1) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]; simp

instance instNontrivNormedField_InfCompl (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion := by
  refine { InfinitePlace.Completion.instNormedField w with non_trivial := ?_ }
  use algebraMap K w.Completion 2
  rw [show algebraMap K w.Completion 2 =
    (↑((WithAbs.equiv w.1).symm 2) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]
  show 1 < w 2
  rw [(w.norm_embedding_eq 2).symm]; simp only [map_ofNat]; norm_num

end RestrictedProductDirectLimit
end NumberField.Adeles
end
