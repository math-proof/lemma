module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
public import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]


theorem PeriodicGraph.bufferedEdgeWindow_mono (P : PeriodicGraph V) :
    Monotone P.bufferedEdgeWindow := by
  intro N M hNM e he
  obtain ⟨eN, rfl⟩ := he
  induction eN using Sym2.inductionOn with
  | _ x y =>
      let xM : P.BufferedVertex M := P.bufferedVertexInclLE hNM x
      let yM : P.BufferedVertex M := P.bufferedVertexInclLE hNM y
      exact ⟨s(xM, yM), rfl⟩


end PeriodicPlanar
end FK
end StatMech
