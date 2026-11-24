module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
public import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
public import Instance.StatisticalMechanics.Code.Onsager.TorusLoopHomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_xWrapSign {L : ℕ} (d : ons_Dart L) : ℤ :=
  if d.2 = 0 ∧ d.1.1 = -1 then 1
  else if d.2 = 2 ∧ d.1.1 = 0 then -1 else 0

def ons_yWrapSign {L : ℕ} (d : ons_Dart L) : ℤ :=
  if d.2 = 1 ∧ d.1.2 = -1 then 1
  else if d.2 = 3 ∧ d.1.2 = 0 then -1 else 0

end StatMech.Onsager
