/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.Cor1126


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

set_option synthInstance.maxHeartbeats 80000

instance adicCompletionIntegers_algebra_over_base {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra (𝓞 K) (w.adicCompletionIntegers L) :=
  RingHom.toAlgebra
    ((algebraMap (𝓞 L) (w.adicCompletionIntegers L)).comp (algebraMap (𝓞 K) (𝓞 L)))

instance adicCompletionIntegers_isScalarTower_base {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    IsScalarTower (𝓞 K) (𝓞 L) (w.adicCompletionIntegers L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end
