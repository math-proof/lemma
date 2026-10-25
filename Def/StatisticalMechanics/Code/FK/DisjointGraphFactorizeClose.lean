/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DisjointGraphFactorizeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.DisjointGraphFactorizeClose
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


variable {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
  [DecidableRel G.Adj] [DecidableRel C.Adj]


def dgf_DisjointBoxAnalyticCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    ∃ (g : Multiplicative (Site d)) (r : ℕ), ∀ T ∈ P, ∀ T' ∈ P,
      ∃ (F tT tT' : Finset (Sym2 (boxVerts d (N + r))))
        (C' : SimpleGraph (boxVerts d (N + r))) (_ : DecidableRel C'.Adj),
        
        T = tT.image (edgeIncl d (N + r)) ∧
        T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d (N + r)) ∧
        
        (∀ e ∈ tT', e ∉ F) ∧
        
        boundaryCliqueGraph (boxBoundary d (N + r)) ≤ C' ∧
        
        (∀ ψ ∈ fibreReps F,
          (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1:ℝ)) ρ
              * condBcProb (boxGraph d (N + r)) C' p 2 F ψ ρ)
            ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) ∧
        
        ((wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT'))
          ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))


end FK
end StatMech
