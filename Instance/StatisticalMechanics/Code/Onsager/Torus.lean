/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.Torus


namespace StatMech.Onsager

instance (L : ℕ) : DecidableRel (onsTorusAdj L) := by
  intro u v; unfold onsTorusAdj; infer_instance

end StatMech.Onsager
