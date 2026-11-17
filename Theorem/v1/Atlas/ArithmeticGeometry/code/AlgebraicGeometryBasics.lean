/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AlgebraicGeometryBasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.ENat
open Cardinal

public section

noncomputable section

universe u v w w'

variable {ι : Type*}

example (k : Type*) (L : Type*) [Field k] [Field L] [Algebra k L]
    (x : ι → L) : Prop := AlgebraicIndependent k x

example (k : Type*) (L : Type*) [Field k] [Field L] [Algebra k L]
    (x : ι → L) : Prop := IsTranscendenceBasis k x


end
