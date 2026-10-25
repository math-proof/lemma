/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyConditionalCapClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.HolleyConditionalCapClose
open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


def hcc_NearBoxFactoriseData {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    (∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) →
    ∃ (g : Multiplicative (Site d)) (r : ℕ), ∀ T ∈ P, ∀ T' ∈ P,
      ∃ (F : Finset (Sym2 (boxVerts d (N + r))))
        (S_A S_B : Set (ConfigSpace (Sym2 (boxVerts d (N + r)))))
        (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj)
        (tcross : Finset (Sym2 (boxVerts d (N + r)))),
        (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') = boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B) ∧
        T ∪ T'.image (fun e => g⁻¹ • e) = tcross.image (edgeIncl d (N + r)) ∧
        MeasurableSet (boxRestrict d (N + r) ⁻¹' (S_A ∩ S_B)) ∧
        MeasurableSet (boxRestrict d (N + r) ⁻¹' S_B) ∧
        IsIncreasing S_A ∧
        DependsOnOutside F S_B ∧
        boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, S_A.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) ∧
        ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d (N + r) ⁻¹' S_B)
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))


end FK
end StatMech
