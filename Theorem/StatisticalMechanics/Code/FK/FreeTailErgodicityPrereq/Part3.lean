/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailErgodicityPrereq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Abbrev.StatisticalMechanics.Code.FK.FreeTailErgodicityPrereq
open MeasureTheory Set


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


theorem fk_invariant_event_ae_tail (hd : 1 ≤ d)
    {mu : Measure (ConfigSpace (Sym2 (Site d)))} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    ∀ s : Set (ConfigSpace (Sym2 (Site d))), MeasurableSet s →
      (∀ g : Multiplicative (Site d), shift g ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace (Sym2 (Site d))),
        FKIsTailEvent d s' ∧ s =ᵐ[mu] s' :=
  ati_invariant_aeTail (fkTailEdgeWindow d) fkTailEdgeWindow_mono
    (fkTailEdgeWindow_escape hd) hmu

end FK
end StatMech
