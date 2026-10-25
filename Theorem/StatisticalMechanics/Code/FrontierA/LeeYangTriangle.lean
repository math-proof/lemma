/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Instance.StatisticalMechanics.Code.FrontierA.LeeYangTriangle
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem threeVertexTriangle_edgeFinset :
    threeVertexTriangle.edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
      fin_cases x <;> fin_cases y <;>
        simp [threeVertexTriangle, SimpleGraph.mem_edgeFinset]


theorem sum_bond_threeVertexTriangle (s : ConfigSpace (Fin 3)) :
    (∑ e ∈ threeVertexTriangle.edgeFinset, bond s e) =
      bond s s(0, 1) + bond s s(0, 2) + bond s s(1, 2) := by
  rw [threeVertexTriangle_edgeFinset]
  simp
  ring


end StatMech.FrontierA
