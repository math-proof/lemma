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
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

abbrev PeriodicGraph.TailClusterVertex (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) :=
  {y : V // y ∈ P.cluster omega x}

abbrev PeriodicGraph.tailClusterGraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    SimpleGraph (P.TailClusterVertex omega x) :=
  (P.openSubgraph omega).induce (P.cluster omega x)

end StatMech.FK.PeriodicPlanar
