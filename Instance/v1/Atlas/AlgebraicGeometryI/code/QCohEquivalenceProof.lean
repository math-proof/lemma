/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohEquivalenceProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
set_option maxHeartbeats 4000000


namespace QCohEquivalenceProof

open Submodule

open CategoryTheory AlgebraicGeometry

/-- `M̃` is quasi-coherent for every `R`-module `M` (Cor 16). -/
instance qcoh_tilde_isQuasicoherent {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

end QCohEquivalenceProof
