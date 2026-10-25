/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskOrbitCoveragePairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    ∃ c d : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
        CanonicalMaskTransferOrbit ends m j k l zero p a d ∧
        canonicalMaskOrbitCoverageUnion ends m j k l zero p c d =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ∧
        canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 >
          canonicalCoveragePairScore ends m k zero a.1.1 b.1.1


def CanonicalMaskOrbitCoveragePairProgress
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    (∃ t : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a t ∧
        canonicalMaskOrbitCoverage ends m j k l zero p t =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p a b) ∨
      ∃ c d : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
          CanonicalMaskTransferOrbit ends m j k l zero p a d ∧
          canonicalMaskOrbitCoverageUnion ends m j k l zero p c d =
            canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ∧
          canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 >
            canonicalCoveragePairScore ends m k zero a.1.1 b.1.1

end StatMech.GrahamGHS.FourColor
