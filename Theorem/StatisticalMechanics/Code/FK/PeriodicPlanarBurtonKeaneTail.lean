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
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

theorem PeriodicGraph.infiniteCluster_component_after_finset
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) :
    ∃ D : (P.tailClusterGraph omega x).ComponentCompl
        (P.tailClusterCut omega x K), D.supp.Infinite := by
  letI : Infinite (P.TailClusterVertex omega x) := hinf.to_subtype
  let e : (P.tailClusterGraph omega x).end :=
    ⟨(SimpleGraph.nonempty_ends_of_infinite
      (P.tailClusterGraph omega x)).choose,
      (SimpleGraph.nonempty_ends_of_infinite
      (P.tailClusterGraph omega x)).choose_spec⟩
  let D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K) :=
    (e : (j : (Finset (P.TailClusterVertex omega x))ᵒᵖ) ->
      (P.tailClusterGraph omega x).componentComplFunctor.obj j)
      (Opposite.op (P.tailClusterCut omega x K))
  exact ⟨D, SimpleGraph.end_componentCompl_infinite
    (P.tailClusterGraph omega x) e (Opposite.op (P.tailClusterCut omega x K))⟩

end StatMech.FK.PeriodicPlanar
