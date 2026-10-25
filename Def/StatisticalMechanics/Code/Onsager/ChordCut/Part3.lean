/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part2


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


def rayX (w : Pt) (k : ℕ) : Pt := (w.1 + (k : ℤ), w.2)


end StatMech.Onsager.ChordCut
