/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupAtPoint
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The descended scaling action on the associated graded ring. -/
noncomputable def scaleOnGraded (I : Ideal R) (c : R) :
    assocGradedRing I →+* assocGradedRing I :=
  Ideal.Quotient.lift (reesIdealFromBase I)
    ((Ideal.Quotient.mk (reesIdealFromBase I)).comp (scaleOnRees I c))
    (fun x hx => by
      show Ideal.Quotient.mk _ (scaleOnRees I c x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact reesIdealFromBase_le_comap_scaleOnRees I c hx)

end Prop34Blowup
end
