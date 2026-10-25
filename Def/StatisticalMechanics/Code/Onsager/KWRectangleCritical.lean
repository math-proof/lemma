/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Abbrev.StatisticalMechanics.Code.Onsager.KWRectangleCritical


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


def ons_rectDirStep (M N : Nat) (mu : Fin 4) (p : ons_RectVertex M N) :
    ons_RectVertex M N :=
  match mu with
  | 0 => (p.1 + 1, p.2)
  | 1 => (p.1, p.2 + 1)
  | 2 => (p.1 - 1, p.2)
  | 3 => (p.1, p.2 - 1)


def ons_rectDartValid (M N : Nat) (d : ons_RectDart M N) : Prop :=
  match d.2 with
  | 0 => d.1.1.val < M
  | 1 => d.1.2.val < N
  | 2 => 0 < d.1.1.val
  | 3 => 0 < d.1.2.val

end StatMech.Onsager
