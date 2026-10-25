/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part4


namespace StatMech.Onsager

open Matrix BigOperators

def ons_maskAfter (L : ℕ) (forbidden : Finset (ons_Dart L)) :
    List (ons_Dart L) → Finset (ons_Dart L)
  | [] => forbidden
  | e :: es => ons_maskAfter L (ons_addDartPair L forbidden e) es

noncomputable def ons_maskEliminationProduct
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) : List (ons_Dart L) → ℂ
  | [] => 1
  | e :: es =>
      (1 - ∑' s, ons_firstReturnWeight
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)))
        e (ons_dartRev L e) s) *
      ons_maskEliminationProduct L x a b
        (ons_addDartPair L forbidden e) es

end StatMech.Onsager
