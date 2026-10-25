/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Theorem.v1.Atlas.NumberTheoryI.code.CDVRExtensions


noncomputable section

set_option linter.unusedSectionVars false

namespace FiniteDimensionalNormTopology

instance algebraIsAlgebraic : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

end FiniteDimensionalNormTopology
end
