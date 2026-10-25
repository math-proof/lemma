/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_signedHorizontalBoundary
    {L : ℕ} (P : (ZMod L × ZMod L) → ZMod 2)
    (p : ZMod L × ZMod L) : ℤ :=
  (P p).val - (P (p.1, p.2 - 1)).val

def ons_signedVerticalBoundary
    {L : ℕ} (P : (ZMod L × ZMod L) → ZMod 2)
    (p : ZMod L × ZMod L) : ℤ :=
  (P (p.1 - 1, p.2)).val - (P p).val

def ons_outgoingBoundaryCoeff
    {L : ℕ} (P : (ZMod L × ZMod L) → ZMod 2)
    (p : ZMod L × ZMod L) (mu : Fin 4) : ℤ :=
  match mu.val with
  | 0 => ons_signedHorizontalBoundary P p
  | 1 => ons_signedVerticalBoundary P p
  | 2 => -ons_signedHorizontalBoundary P (p.1 - 1, p.2)
  | _ => -ons_signedVerticalBoundary P (p.1, p.2 - 1)

end StatMech.Onsager
