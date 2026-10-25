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
import Def.v1.Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
universe u


namespace AlgebraicGeometry.CompletenessValuationCriterion

attribute [instance] AlgVariety.topInst AlgVariety.ffField

structure DominantProjectionData {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y)) where
  Z : SubvarietyOf X
  Vvar : AlgVariety k
  embed : Vvar.carrier → X.carrier × Y
  embed_mem : ∀ p, embed p ∈ V
  toZ : Vvar.carrier → Z.toVariety.carrier
  psiStar : Z.toVariety.functionField →+* Vvar.functionField
  psiStar_inj : Function.Injective psiStar
  psiStar_base_compat : ∀ x : k,
    psiStar (Z.toVariety.baseEmbed x) = Vvar.baseEmbed x

structure CoordRingEvalData {k : Type u} [Field k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V) (Q : Y) where
  coordRingY : Subring dpd.Vvar.functionField
  evalAtQ : coordRingY →+* k
  base_le_coordRingY : ∀ x : k, dpd.Vvar.baseEmbed x ∈ coordRingY
  evalAtQ_fixes_base : ∀ (x : k) (hx : dpd.Vvar.baseEmbed x ∈ coordRingY),
    evalAtQ ⟨dpd.Vvar.baseEmbed x, hx⟩ = x
  psiStar_base_compat : ∀ x : k,
    dpd.psiStar (dpd.Z.toVariety.baseEmbed x) = dpd.Vvar.baseEmbed x

end AlgebraicGeometry.CompletenessValuationCriterion
