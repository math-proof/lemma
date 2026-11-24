module
public import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
public import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
public import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_rotatePoint (c : Fin 4) (p : ℤ × ℤ) : ℤ × ℤ :=
  match c.val with
  | 0 => p
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | _ => (p.2, -p.1)

end StatMech.Onsager
