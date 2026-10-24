/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompleteVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ValuationRings
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ValuationRings
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

def localRing_le {k : Type u} [Field k] {V : AlgVariety k}
    (P : V.carrier) (R : ValRingOver V) : Prop :=
  ∀ x : V.functionField, x ∈ V.localRingAt P → x ∈ R.valSub

def SatisfiesValuationCriterion {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    ∃ P : Z.toVariety.carrier, localRing_le P R

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
