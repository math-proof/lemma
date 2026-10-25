/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Structure.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- The underlying complex of a resolution has homology objects in every degree. -/
instance (Q : Resolution Z) (i : ℕ) : Q.complex.HasHomology i := Q.hasHomology i

/-- The augmentation map of a resolution is a quasi-isomorphism. -/
instance (Q : Resolution Z) : QuasiIso Q.π := Q.quasiIso

end Resolution
end FundamentalThm
end
