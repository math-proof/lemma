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
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties.Part3
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The scaling action on the Rees algebra fixes elements of `R`. -/
lemma scaleOnRees_algebraMap (I : Ideal R) (c : R) (r : R) :
    scaleOnRees I c (algebraMap R (reesAlgebra I) r) = algebraMap R (reesAlgebra I) r :=
  Subtype.ext ((scaleAlgHom c).commutes r)

/-- The base ideal `I · R[Rt]` is invariant under the scaling map. -/
lemma reesIdealFromBase_le_comap_scaleOnRees (I : Ideal R) (c : R) :
    reesIdealFromBase I ≤ (reesIdealFromBase I).comap (scaleOnRees I c) := by
  unfold reesIdealFromBase
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  show scaleOnRees I c (algebraMap R (reesAlgebra I) r) ∈
    Ideal.map (algebraMap R (reesAlgebra I)) I
  rw [scaleOnRees_algebraMap]
  exact Ideal.mem_map_of_mem _ hr

end Prop34Blowup
end
