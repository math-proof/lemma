/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFiniteEnergy
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

def PeriodicGraph.infiniteClusters (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = P.cluster omega x}


noncomputable def PeriodicGraph.numInfiniteClusters (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : ℕ∞ :=
  (P.infiniteClusters omega).encard

end StatMech.FK.PeriodicPlanar
