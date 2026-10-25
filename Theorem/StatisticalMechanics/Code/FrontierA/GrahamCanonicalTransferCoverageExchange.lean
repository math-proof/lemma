/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferNormalization.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exists_coverage_exclusive_witnesses
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (ha : canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b)
    (hb : canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b) :
    (∃ c, c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b) ∧
      ∃ d, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        d ∉ canonicalMaskOrbitCoverage ends m j k l zero p a := by
  classical
  let A := canonicalMaskOrbitCoverage ends m j k l zero p a
  let B := canonicalMaskOrbitCoverage ends m j k l zero p b
  have ha' : A ≠ A ∪ B := by
    simpa only [A, B, canonicalMaskOrbitCoverageUnion] using ha
  have hb' : B ≠ A ∪ B := by
    simpa only [A, B, canonicalMaskOrbitCoverageUnion] using hb
  have hBA : ¬ B ⊆ A := by
    intro hBA
    apply ha'
    exact (Finset.union_eq_left.mpr hBA).symm
  have hAB : ¬ A ⊆ B := by
    intro hAB
    apply hb'
    exact (Finset.union_eq_right.mpr hAB).symm
  constructor
  · by_contra h
    apply hAB
    intro c hcA
    by_contra hcB
    exact h ⟨c, hcA, hcB⟩
  · by_contra h
    apply hBA
    intro d hdB
    by_contra hdA
    exact h ⟨d, hdB, hdA⟩

theorem canonicalMaskOrbitCoverageUnion_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitCoverageUnion ends m j k l zero p a b =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p b a := by
  simp only [canonicalMaskOrbitCoverageUnion, Finset.union_comm]


end StatMech.GrahamGHS.FourColor
