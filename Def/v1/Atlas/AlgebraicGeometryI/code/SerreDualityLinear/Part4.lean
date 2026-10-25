/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part3


namespace SerreDualityP1

open CohomologyP1


/-- `shiftEquiv` restricted to supports on `(n, 0)` is a linear isomorphism
onto supports on `[0, -2 - n]`. -/
noncomputable def shiftEquiv_supported (k : Type*) [Field k] (n : ℤ) :
    ↥(Finsupp.supported k k (Set.Ioo n 0)) ≃ₗ[k]
    ↥(Finsupp.supported k k (Set.Icc 0 (-2 - n))) := by
  have e := (shiftEquiv k).submoduleMap (Finsupp.supported k k (Set.Ioo n 0))
  rwa [shiftEquiv_coe_eq, shiftMap_supported_Ioo] at e


/-- Serre duality on `ℙ¹` as a linear isomorphism: for `n < -1`,
`H¹(O(n)) ≅ H⁰(O(-2 - n))` via the residue shift. -/
noncomputable def serre_duality_P1 (k : Type) [Field k] (n : ℤ) (_hn : n < -1) :
    ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k] ↥(CechH0 k (-2 - n)) :=

  (H1_equiv_supported_complement k n) |>.trans

  (shiftEquiv_supported k n) |>.trans

  (LinearEquiv.ofEq _ _ (cechH0_eq_supported k (-2 - n)).symm)

end SerreDualityP1
