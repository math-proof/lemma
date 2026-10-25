/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Onsager.CellGaussBonnet.Part2


namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def pinchDelta (e w n s ne nw se sw : Bool) : ℤ :=
  
  (bI (sw && !w && !s) - bI (w && s && !sw))
  
  + (bI (se && !e && !s) - bI (e && s && !se))
  
  + (bI (nw && !n && !w) - bI (n && w && !nw))
  
  + (bI (ne && !n && !e) - bI (n && e && !ne))


def rhsCorrected (e w n s ne nw se sw : Bool) : ℤ :=
  rhsStated e w n s ne nw se sw + 2 * pinchDelta e w n s ne nw se sw


end StatMech.Onsager.CellGaussBonnet
