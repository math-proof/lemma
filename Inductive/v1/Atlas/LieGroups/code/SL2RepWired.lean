/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.LieGroups.code.SL2Classification
import Lemma.Complex.Nonempty_Realization


inductive KTypeBoundedness' where
  | boundedBoth
  | unboundedBoth
  | boundedBelow
  | boundedAbove
  deriving DecidableEq, Repr

