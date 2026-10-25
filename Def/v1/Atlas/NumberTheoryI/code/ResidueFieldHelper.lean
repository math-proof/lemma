/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
set_option synthInstance.maxHeartbeats 80000

open IsDedekindDomain


namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

variable (𝔭 : HeightOneSpectrum A)

noncomputable def completionResidueMap :
    A →+* (𝔭.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))).comp
    (algebraMap A (𝔭.adicCompletionIntegers K))

end IsDedekindDomain.HeightOneSpectrum
