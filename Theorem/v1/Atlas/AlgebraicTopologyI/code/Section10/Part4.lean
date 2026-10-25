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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part2
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

attribute [instance] subspaceChainInclusion_mono

/-- The short complex `bottomSES X A` is short-exact. -/
lemma bottomSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (bottomSES X A).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

set_option maxHeartbeats 800000 in
/-- Compatibility condition exhibiting the kernel of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` as a span over `𝒳`
via the negated first projection and the second projection. Auxiliary lemma for the
abstract second isomorphism theorem. -/
lemma secondIso_kernel_pullback_cond :
    (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst (X := 𝒜) (Y := ℬ))) ≫ φ =
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ)) ≫ ψ := by
  have h := kernel.condition (biprod.desc φ ψ)
  rw [show kernel.ι (biprod.desc φ ψ) = biprod.lift
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.fst) (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd) from
    by apply biprod.hom_ext <;> simp, biprod.lift_desc] at h
  rw [Preadditive.neg_comp]; exact neg_eq_of_add_eq_zero_right h

set_option linter.unusedSectionVars false in
/-- Vanishing condition needed to factor the cokernel of `pullback.snd` through the
cokernel of `biprod.inl ∘ factorThruImage`. Used in constructing the forward map of the
abstract second isomorphism theorem. -/
lemma secondIso_fwd_cond :
    pullback.snd φ ψ ≫ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) = 0 := by
  have h : pullback.fst φ ψ ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) =
    pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ) := by
    apply (cancel_mono (Limits.image.ι (biprod.desc φ ψ))).mp
    simp only [Category.assoc, image.fac, biprod.inl_desc, biprod.inr_desc]; exact pullback.condition
  have key : (pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ)) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    rw [← h]; simp only [Category.assoc, cokernel.condition, comp_zero]
  simp only [Category.assoc] at key ⊢; exact key

set_option linter.unusedSectionVars false in
/-- Vanishing condition: the kernel of `[φ, ψ]` projected to the `ℬ` factor lands in the
image of `pullback.snd`, hence its image in `coker(pullback.snd)` vanishes. -/
lemma secondIso_kernel_kills_snd_cokernel :
    kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) ≫
    cokernel.π (pullback.snd (f := φ) (g := ψ)) = 0 := by
  rw [reassoc_of% (show kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) =
    (pullback.lift (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst))
      (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd)
      (secondIso_kernel_pullback_cond φ ψ)) ≫ pullback.snd φ ψ from by simp [pullback.lift_snd]),
    cokernel.condition, comp_zero]

end
end Excision
