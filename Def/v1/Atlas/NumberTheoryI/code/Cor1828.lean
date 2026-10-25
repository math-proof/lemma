/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1828.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.StieltjesIntegral.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.StieltjesIntegral
open scoped BigOperators


namespace RiemannStieltjes

variable {a b : ℝ}

noncomputable def summatoryFunction (g : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊x⌋, g (↑n)

noncomputable def discreteSum (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (↑n) * g (↑n)

def NotBothDiscAtIntegers (f g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ n : ℤ, (↑n : ℝ) ∈ Set.Icc a b →
    (ContinuousWithinAt f (Set.Iio ↑n) ↑n ∨
      ContinuousWithinAt g (Set.Iio ↑n) ↑n) ∧
    (ContinuousWithinAt f (Set.Ioi ↑n) ↑n ∨
      ContinuousWithinAt g (Set.Ioi ↑n) ↑n)

end RiemannStieltjes
