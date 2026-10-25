/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ValuationRings
import Def.v1.Atlas.ArithmeticGeometry.code.ValuationRings.Part4
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.NoetherianSpace
universe u


namespace AlgebraicGeometry.CompletenessValuationCriterion

structure AlgVariety (k : Type u) [Field k] where
  carrier : Type u
  [topInst : TopologicalSpace carrier]
  functionField : Type u
  [ffField : Field functionField]
  baseEmbed : k →+* functionField
  baseEmbed_inj : Function.Injective baseEmbed
  localRingAt : carrier → Subring functionField
  base_le_localRing : ∀ P x, baseEmbed x ∈ localRingAt P
  noethProduct : ∀ (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y],
    TopologicalSpace.NoetherianSpace (carrier × Y)

attribute [instance] AlgVariety.topInst AlgVariety.ffField

structure SubvarietyOf {k : Type u} [Field k] (X : AlgVariety k) where
  toVariety : AlgVariety k
  inclusion : toVariety.carrier → X.carrier

structure ValRingOver {k : Type u} [Field k] (V : AlgVariety k) where
  valSub : ValuationSubring V.functionField
  contains_base : ∀ x : k, V.baseEmbed x ∈ valSub

end AlgebraicGeometry.CompletenessValuationCriterion
