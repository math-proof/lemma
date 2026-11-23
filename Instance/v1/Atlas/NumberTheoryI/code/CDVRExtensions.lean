/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
public import Theorem.v1.Atlas.NumberTheoryI.code.CDVRExtensions
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FiniteDimensionalNormTopology

instance algebraIsAlgebraic : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

end FiniteDimensionalNormTopology
end
