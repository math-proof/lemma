/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- Abstract data for a Weitzenböck decomposition $\bar\square = D + R$, where
$D$ is a positive second-order operator and $R$ is a $0$-th order curvature
term acting on a vector space of $k$-forms; both are additive. -/
structure WeitzenboeckDecomposition
    (V : Type*) [AddCommGroup V] where
  D : V → V
  R_term : V → V
  k : ℕ
  D_add : ∀ a b, D (a + b) = D a + D b
  R_add : ∀ a b, R_term (a + b) = R_term a + R_term b


