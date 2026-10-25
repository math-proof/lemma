/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


noncomputable def hpb_lamS (a : ℂ) (h0 : ℤ) (x : ℝ) (memA : List ℤ → Prop) : ℝ :=
  ∑' d : {ts // memA ts}, hexSAWwt a h0 x d.1


noncomputable def hpb_upsS (a : ℂ) (h0 : ℤ) (x : ℝ) (memB : List ℤ → Prop) : ℝ :=
  ∑' b : {ts // memB ts}, hexSAWwt a h0 x b.1


end StatMech.Universality
