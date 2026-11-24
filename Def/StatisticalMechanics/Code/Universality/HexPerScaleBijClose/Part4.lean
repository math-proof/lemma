module
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


def hpb_emptyHalfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memB : List ℤ → Prop) :
    HexHalfClass a h0 x (fun _ => False) memB where
  lower := fun d => absurd d.2 (by simp)
  upper := fun d => absurd d.2 (by simp)
  hlow := fun d => absurd d.2 (by simp)
  hupp := fun d => absurd d.2 (by simp)
  pair_inj := fun d => absurd d.2 (by simp)


end StatMech.Universality
