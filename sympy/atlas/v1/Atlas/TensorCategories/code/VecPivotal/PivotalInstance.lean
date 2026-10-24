/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal/PivotalInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence
import sympy.atlas.v1.Atlas.TensorCategories.code.PivotalSpherical
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module Category

universe u

noncomputable section

variable (k : Type u) [Field k]

namespace TensorCategories

/-- `FGModuleCat k` has a pivotal category structure given by the canonical
double-dual evaluation isomorphism together with the tensor-coherence iso
of Section 1.38. -/
end TensorCategories

end
