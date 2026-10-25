/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


def ocs_FreeRotationResidue (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) : Prop :=
  ∀ (m : ℕ) (eb : Sym2 (boxVerts d m)), eb ∈ (boxGraph d m).edgeFinset →
    freeEdgeDensity d 2 (edgeIncl d m eb) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)


noncomputable def ocs_unitMarg (d n : ℕ) (p : Fin d × Bool) (t : ℝ) : ℝ :=
  if hR : 1 ≤ Nat.sqrt n then
    edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) 2)
      (ocs_unitEdge d (Nat.sqrt n) hR p)
  else 0


noncomputable def ocs_freeDelta (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ p : Fin d × Bool,
    |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|

end FK
end StatMech
