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
import Structure.v1.Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
universe u


namespace AlgebraicGeometry.CompletenessValuationCriterion

attribute [instance] AlgVariety.topInst AlgVariety.ffField

def localRing_le {k : Type u} [Field k] {V : AlgVariety k}
    (P : V.carrier) (R : ValRingOver V) : Prop :=
  ∀ x : V.functionField, x ∈ V.localRingAt P → x ∈ R.valSub

def SatisfiesValuationCriterion {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    ∃ P : Z.toVariety.carrier, localRing_le P R

end AlgebraicGeometry.CompletenessValuationCriterion
