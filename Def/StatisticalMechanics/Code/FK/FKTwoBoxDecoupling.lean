/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKTwoBoxDecoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


def ftb_FarBoxProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d))))
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (m : ℕ) (δ : ℝ), 0 < δ →
    ∃ g : Multiplicative (Site d), ∀ T ∈ P, ∀ T' ∈ P,
      μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T')
        ≤ (μbox m).real (fmu_multiOpen T) * (μbox m).real (fmu_multiOpen T') + δ


def ftb_FiniteBoxDisjointProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      (μbox m).real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T')
        ≤ (μbox N).real (fmu_multiOpen T) * (μbox N).real (fmu_multiOpen T')


end FK
end StatMech
