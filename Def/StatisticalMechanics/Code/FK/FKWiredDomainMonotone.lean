/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKWiredDomainMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


def fwm_WiredDisjointBoxFactorise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    (∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) →
    ∃ (g : Multiplicative (Site d)) (r : ℕ), ∀ T ∈ P, ∀ T' ∈ P,
      (∃ t : Finset (Sym2 (boxVerts d (N + r))),
          T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d (N + r)))
      ∧ (μbox (N + r)).real (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
          ≤ (μbox N).real (fmu_multiOpen T) * (μbox N).real (fmu_multiOpen T')


end FK
end StatMech
