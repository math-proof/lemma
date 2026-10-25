/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DecayOfCorrelations
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryInfluenceDecay
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


noncomputable def fbd_offCentreCarrier (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    (p q : ℝ) (k : ℕ) : ℝ :=
  edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) eb')
    - edgeMargProb
        (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q)
        (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))


end FK
end StatMech
