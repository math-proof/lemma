/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Def.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part3
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


instance triangleVertexFintype (t : ℕ) : Fintype (TriangleVertex t) := by
  induction t with
  | zero => simp only [TriangleVertex]; infer_instance
  | succ t ih =>
      simp only [TriangleVertex]
      letI := ih
      infer_instance

instance triangleVertexDecidableEq (t : ℕ) : DecidableEq (TriangleVertex t) := by
  induction t with
  | zero => simp only [TriangleVertex]; infer_instance
  | succ t ih =>
      simp only [TriangleVertex]
      letI := ih
      infer_instance


end StatMech.FrontierA
