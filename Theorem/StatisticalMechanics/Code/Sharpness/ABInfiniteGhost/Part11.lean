/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part11
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


theorem abigWindow_incidentCoupling_eq_sum [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (x : S) :
    abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x =
      ∑ y : S, if G.Adj (x : V) (y : V)
        then J s((x : V), (y : V)) else 0 := by
  unfold abcrIncidentCoupling
  calc
    (∑ d : {d : (abigWindowGraph G S).Dart // d.fst = x},
        abigWindowCoupling J S d.1.edge) =
        ∑ y : (abigWindowGraph G S).neighborSet x,
          J s((x : V), (y.1 : V)) := by
      apply Fintype.sum_equiv
        (abigDartFiberEquivNeighbor (abigWindowGraph G S) x)
      intro d
      simp [abigDartFiberEquivNeighbor, abigWindowCoupling,
        SimpleGraph.Dart.edge, d.2]
    _ = ∑ y : S, if G.Adj (x : V) (y : V)
          then J s((x : V), (y : V)) else 0 := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter fun y : S => (abigWindowGraph G S).Adj x y)
        (by intro y; simp) (fun y : S => J s((x : V), (y : V)))]
      rw [Finset.sum_filter]
      rfl


end Sharpness
end StatMech
