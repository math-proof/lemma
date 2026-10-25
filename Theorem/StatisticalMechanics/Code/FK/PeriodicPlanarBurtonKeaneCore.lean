/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFiniteEnergy
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

theorem periodicVertexIndex_injective :
    Function.Injective (periodicVertexIndex V) :=
  (Countable.exists_injective_nat V).choose_spec

theorem PeriodicGraph.self_mem_cluster (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) : x ∈ P.cluster omega x :=
  by
    change (P.openSubgraph omega).Reachable x x
    exact SimpleGraph.Reachable.refl x

theorem PeriodicGraph.cluster_eq_of_reachable (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : (P.openSubgraph omega).Reachable x y) :
    P.cluster omega x = P.cluster omega y := by
  ext z
  constructor
  · intro hxz
    exact hxy.symm.trans hxz
  · intro hyz
    exact hxy.trans hyz


end StatMech.FK.PeriodicPlanar
