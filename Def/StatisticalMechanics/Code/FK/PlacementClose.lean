/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.FK.PlacementClose
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


def plc_WiredCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
        (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t'.image (innerEdgeLE d hNm))


def plc_FreeCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))


end FK
end StatMech
