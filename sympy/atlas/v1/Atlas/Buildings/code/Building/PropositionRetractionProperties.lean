/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/PropositionRetractionProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.FixedPointSubgroups
import Lemma.Set.NonemptyOrbitSetSetGt

set_option linter.unusedSectionVars false

noncomputable section

open Set

namespace PropositionRetractionProperties
