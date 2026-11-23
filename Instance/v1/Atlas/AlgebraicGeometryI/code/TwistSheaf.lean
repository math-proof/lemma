/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.QCohProjective.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohProjective
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof
public import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
@[expose] public section

set_option maxHeartbeats 4000000

open MvPolynomial QCohProjective


noncomputable section

namespace TwistSheaf

variable (k : Type*) [Field k] (n : ℕ)


/-- The `k`-module structure on the multivariate polynomial ring `k[X₀,…,Xₙ]`. -/
noncomputable instance mvPolyModule :
    Module k (MvPolynomial (Fin (n + 1)) k) := Algebra.toModule

end TwistSheaf
end
