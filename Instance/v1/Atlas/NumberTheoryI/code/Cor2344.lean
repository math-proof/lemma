/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2344.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.TateCohomology.Part4
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.TateCohomology
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

instance tateH0.inhabited (A : Rep k G) : Inhabited (tateH0 A) := ⟨0⟩

instance tateMinus1.inhabited (A : Rep k G) : Inhabited (tateMinus1 A) := ⟨0⟩

instance tateH0.finite (A : Rep k G) [Finite A] : Finite (tateH0 A) := by
  unfold tateH0
  haveI : Finite A.ρ.invariants :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := normImageInInvariants A))
    (Submodule.Quotient.mk_surjective _)

instance tateMinus1.finite (A : Rep k G) [Finite A] : Finite (tateMinus1 A) := by
  unfold tateMinus1
  haveI : Finite (LinearMap.ker (normMap k G A)) :=
    Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  exact Finite.of_surjective (Submodule.Quotient.mk (p := augInKerNorm A))
    (Submodule.Quotient.mk_surjective _)

end TateCohomology
end
