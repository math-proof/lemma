/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part21
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The monoid structure on `[S, S]` induced by composition of representatives. -/
instance (S : TopCat.{0}) : Monoid (SelfMapHomotopyClass S) where
  mul := Quotient.lift₂ (fun f g => @Quotient.mk _ (selfMapSetoid S) (f ≫ g))
    (fun _ _ _ _ hf hg => Quotient.sound (ContinuousMap.Homotopic.comp hg hf))
  one := @Quotient.mk _ (selfMapSetoid S) (𝟙 S)
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.assoc]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  one_mul := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.id_comp]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  mul_one := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.comp_id]; exact ⟨ContinuousMap.Homotopy.refl _⟩

end BrouwerFixedPoint
