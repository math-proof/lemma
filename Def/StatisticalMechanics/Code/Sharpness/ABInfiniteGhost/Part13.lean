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
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part12
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


section Marginals

variable [Countable V]


noncomputable def abigWindowEnvelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real) : Real :=
  (Finset.univ.image (fun x : S =>
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h)).max'
      (by exact Finset.image_nonempty.mpr ⟨o, Finset.mem_univ o⟩)

end Marginals
end Sharpness
end StatMech
