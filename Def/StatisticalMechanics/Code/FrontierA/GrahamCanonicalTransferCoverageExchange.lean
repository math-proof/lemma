/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferNormalization.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskOrbitCoverageSmallerExclusiveJoin
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    #(canonicalMaskOrbitCoverage ends m j k l zero p a) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p b) ->
    ∀ c : leftMaskFiber ends m j k l zero p,
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ->
      c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ->
      canonicalMaskOrbitCoverage ends m j k l zero p c =
        canonicalMaskOrbitCoverageUnion ends m j k l zero p a b


end StatMech.GrahamGHS.FourColor
