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


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

theorem algebraMap_valuation_le_one {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.LiesAbove w v)
    (k : K) (hk : v.valuation K k ≤ 1) :
    w.valuation L (algebraMap K L k) ≤ 1 := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  rw [valuation_extends_with_ramificationIdx K L v w k]
  exact pow_le_one₀ (WithZero.zero_le _) hk

end
