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
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part3


namespace StatMech.Onsager

open Matrix BigOperators

def ons_addDartPair (L : ℕ) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) : Finset (ons_Dart L) :=
  ({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden

end StatMech.Onsager
