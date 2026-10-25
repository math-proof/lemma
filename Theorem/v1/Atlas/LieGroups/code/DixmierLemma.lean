/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DixmierLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic


noncomputable section

open Polynomial Finset Classical Finsupp Cardinal

universe u


theorem endomorphism_bijective_of_ne_zero
    {A : Type u} [Ring A] {M : Type u} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] (f : Module.End A M) (hf : f ≠ 0) :
    Function.Bijective f :=
  ⟨LinearMap.ker_eq_bot.mp ((IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker f)).resolve_right
      (fun h => hf (LinearMap.ext (fun x => LinearMap.mem_ker.mp (h ▸ Submodule.mem_top))))),
   LinearMap.range_eq_top.mp ((IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f)).resolve_left
      (fun h => hf (LinearMap.ext (fun x => by
        have : f x ∈ LinearMap.range f := ⟨x, rfl⟩
        rw [h] at this; exact (Submodule.mem_bot _).mp this))))⟩

end
