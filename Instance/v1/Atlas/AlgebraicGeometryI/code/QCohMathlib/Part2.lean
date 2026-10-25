/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohTildeFunctor
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohMathlib


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace QCohMathlib

variable {R : CommRingCat.{u}}

/-- The tilde functor is the left adjoint of the `tilde ⊣ Γ` adjunction. -/
instance tilde_isLeftAdjoint : (tilde.functor R).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

/-- For every module `M`, the sheaf `M̃` is quasi-coherent (Cor 16). -/
instance tilde_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent := inferInstance

/-- The corestriction of tilde to its essential image is an equivalence of
categories, since tilde is fully faithful. -/
instance tilde_toEssImage_isEquivalence :
    (tilde.functor R).toEssImage.IsEquivalence :=
  Functor.IsEquivalence.mk

end QCohMathlib
end
