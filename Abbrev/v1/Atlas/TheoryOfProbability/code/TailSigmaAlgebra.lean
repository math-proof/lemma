/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/TailSigmaAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Def.v1.Atlas.TheoryOfProbability.code.TailSigmaAlgebra
open MeasurableSpace

variable {Ω : Type*}


/-- The tail σ-algebra of a sequence of random variables `X : ℕ → Ω → β`, defined as
`𝓣 = ⋂ₙ σ(X n, X (n+1), …)`. This is the standard tail σ-algebra appearing in Kolmogorov's
0-1 law. -/
abbrev tailMeasurableSpaceOfFun {β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) :
    MeasurableSpace Ω :=
  tailMeasurableSpace (fun n => MeasurableSpace.comap (X n) ‹_›)

