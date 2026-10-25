/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- Every component of the augmentation of a resolution is an epimorphism. -/
instance epi_π_f (Q : Resolution Z) (n : ℕ) : Epi (Q.π.f n) := by
  cases n with
  | zero => exact epi_of_isColimit_cofork Q.isColimitCokernelCofork
  | succ n => rw [π_f_succ]; infer_instance

end Resolution
end FundamentalThm
end
