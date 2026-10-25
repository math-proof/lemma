/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

noncomputable instance PeriodicGraph.tailClusterGraphLocallyFinite
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    SimpleGraph.LocallyFinite (P.tailClusterGraph omega x) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  intro v
  let f : (P.tailClusterGraph omega x).neighborSet v ->
      P.graph.neighborSet v.1 := fun w =>
    ⟨w.1.1, w.2.1⟩
  exact Fintype.ofInjective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P.graph.neighborSet v.1 => (z : V)) h)

instance PeriodicGraph.tailClusterGraphPreconnected
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    Fact (P.tailClusterGraph omega x).Preconnected := ⟨by
  intro u v
  have huv : (P.openSubgraph omega).Reachable u.1 v.1 := u.2.symm.trans v.2
  obtain ⟨w⟩ := huv
  exact StatMech.Lattice.walk_induce_reachable (P.openSubgraph omega)
    (P.cluster omega x) w (fun z hz => by
      exact u.2.trans (w.takeUntil z hz).reachable)
    u.2 v.2⟩

end StatMech.FK.PeriodicPlanar
