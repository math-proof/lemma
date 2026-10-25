/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
universe u v w


namespace DModules

open scoped TensorProduct

section DifferentialOperators

noncomputable def endBracketMul {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    (L : Module.End k A) (f : A) : Module.End k A :=
  L ∘ₗ (Algebra.lmul k A f) - (Algebra.lmul k A f) ∘ₗ L

noncomputable def diffOpOrder (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A] :
    ℕ → Submodule k (Module.End k A)
  | 0 => LinearMap.range (Algebra.lmul k A).toLinearMap
  | n + 1 =>
    { carrier := { L | ∀ f : A, endBracketMul L f ∈ diffOpOrder k A n }
      add_mem' := fun {a b} ha hb f => by
        have key : endBracketMul (a + b) f = endBracketMul a f + endBracketMul b f := by
          simp only [endBracketMul, LinearMap.add_comp, LinearMap.comp_add]; abel
        rw [key]; exact Submodule.add_mem _ (ha f) (hb f)
      zero_mem' := fun f => by
        have key : endBracketMul (0 : Module.End k A) f = 0 := by
          simp only [endBracketMul, LinearMap.zero_comp, LinearMap.comp_zero, sub_self]
        rw [key]; exact Submodule.zero_mem _
      smul_mem' := fun c L hL f => by
        have key : endBracketMul (c • L) f = c • endBracketMul L f := by
          simp only [endBracketMul, LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]
        rw [key]; exact Submodule.smul_mem _ c (hL f) }

noncomputable def diffOps (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A] :
    Submodule k (Module.End k A) :=
  ⨆ n, diffOpOrder k A n

end DifferentialOperators
end DModules
