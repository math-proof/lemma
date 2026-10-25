/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Def.v1.Atlas.NumberTheoryI.code.GlobalFields.Part2


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

instance instAlgebraBaseOfExtCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    Algebra K w.Completion :=
  ((algebraMap L w.Completion).comp (algebraMap K L)).toAlgebra

instance instAlgebraBaseOfExtAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra K (w.adicCompletion L) := inferInstance

end
