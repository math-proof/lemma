/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
import Def.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


instance matchingVertexFintype (n : ℕ) : Fintype (MatchingVertex n) := by
  induction n with
  | zero =>
      simp only [MatchingVertex]
      infer_instance
  | succ n ih =>
      simp only [MatchingVertex]
      letI : Fintype (MatchingVertex n) := ih
      infer_instance

instance matchingVertexDecidableEq (n : ℕ) : DecidableEq (MatchingVertex n) := by
  induction n with
  | zero =>
      simp only [MatchingVertex]
      infer_instance
  | succ n ih =>
      simp only [MatchingVertex]
      letI : DecidableEq (MatchingVertex n) := ih
      infer_instance


end StatMech.FrontierA
