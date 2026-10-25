/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part3
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def PeriodicGraph.freeFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.fkPMF (P.orbitGraph n) hp hp1 hq


noncomputable def PeriodicGraph.wiredFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.wiredFkPMF (P.orbitGraph n) (P.orbitBoundary n) hp hp1 hq


def PeriodicGraph.edgeIncl (P : PeriodicGraph V) (n : ℕ) :
    Sym2 (P.OrbitVertex n) → Sym2 V :=
  Sym2.map (Subtype.val : P.OrbitVertex n → V)

end PeriodicPlanar
end FK
end StatMech
