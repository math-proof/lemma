/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part11
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorCyclicNext {n : Nat} (i : Fin n) : Fin n :=
  if hnext : i.val + 1 < n then ⟨i.val + 1, hnext⟩
  else ⟨0, Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i)⟩


def sixVertexSectorAdvance {N n : Nat}
    (x y : SixVertexSector N n) (i : Fin n) : Nat :=
  (sixVertexSectorPosition y i).val - (sixVertexSectorPosition x i).val

end
end StatMech.FrontierD
