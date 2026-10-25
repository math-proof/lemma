/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix


namespace StatMech.Onsager

def ons_dartRev (L : ℕ) (d : ons_Dart L) : ons_Dart L :=
  (ons_dirStep L d.2 d.1, d.2 + 2)


end StatMech.Onsager
