/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V]


def med_wiredPlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb
                (wiredFkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g))
                  (fvs_transBoxBoundary d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
                  (t'.image (innerEdgeLE d hNm)))


def med_freePlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb (fkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))


end FK
end StatMech
