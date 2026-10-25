/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Instance.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part2
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma measurableSet_blockStateEvent (r : ℕ) (p : Fin (2 * r + 1) → Fin 2) :
    MeasurableSet (blockStateEvent r p) := by
  rw [blockStateEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hcoord : Measurable
      (fun sigma : ConfigSpace (Site 1) => sigma (site1 (-(r : ℤ) + (i.val : ℤ)))) :=
    measurable_pi_apply _
  have hstate : Measurable (fun b : Bool => boolTransferState b) :=
    measurable_of_finite _
  exact (hstate.comp hcoord) (measurableSet_singleton (p i))


end StatMech.FrontierB
