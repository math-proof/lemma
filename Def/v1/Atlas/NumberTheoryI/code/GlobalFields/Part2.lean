module
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Artinian.Module
public import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Instance.v1.Atlas.NumberTheoryI.code.GlobalFields


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K]

def Place := Quotient (nontrivialAbsValSetoid K)

end Place

section PlaceExtension

def restrictPlace {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace K :=
  w.comap (algebraMap K L)

def InfinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) : Prop :=
  restrictPlace w = v

def FinitePlace.LiesAbove {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal

end PlaceExtension
end
