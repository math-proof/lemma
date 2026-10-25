/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageHall
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiberClosure


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskOrbitCoverageNested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      canonicalMaskOrbitCoverage ends m j k l zero p r ⊆
          canonicalMaskOrbitCoverage ends m j k l zero p s ∨
        canonicalMaskOrbitCoverage ends m j k l zero p s ⊆
          canonicalMaskOrbitCoverage ends m j k l zero p r


def CanonicalMaskOrbitCoverageNestedAllMarks
    (ends : I -> Sym2 W) (m : Finset I) : Prop :=
  ∀ j k l zero : W, j ≠ k -> k ≠ l -> k ≠ zero ->
    ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNested ends m j k l zero p


def CanonicalMaskOrbitCoverageNoIncomparablePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      ¬ ∃ c d : leftMaskFiber ends m j k l zero p,
        c ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p s ∧
        d ∈ canonicalMaskOrbitCoverage ends m j k l zero p s ∧
        d ∉ canonicalMaskOrbitCoverage ends m j k l zero p r


end StatMech.GrahamGHS.FourColor
