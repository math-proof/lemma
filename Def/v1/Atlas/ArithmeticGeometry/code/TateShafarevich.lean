/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1
import Structure.v1.Atlas.ArithmeticGeometry.code.TateShafarevich


noncomputable section

universe u

open NumberField GaloisCohomology

/-- A *place* of a number field $k$ is either an infinite place (an archimedean valuation) or a
finite place (a nonarchimedean valuation), packaged as a sum type. -/
def NumberFieldPlace (k : Type u) [Field k] [NumberField k] : Type u :=
  NumberField.InfinitePlace k ⊕ NumberField.FinitePlace k

/-- Inject an infinite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.infinite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.InfinitePlace k) : NumberFieldPlace k :=
  Sum.inl v

/-- Inject a finite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.finite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.FinitePlace k) : NumberFieldPlace k :=
  Sum.inr v

end
