/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Def.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part2
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- `generator3` equals the commutator $[(0,1,0,0), (0,0,0,1)]$ in $\Gamma$. -/
theorem generator3_eq_commutator :
    generator3 = mk 0 1 0 0 * mk 0 0 0 1 * (mk 0 1 0 0)⁻¹ * (mk 0 0 0 1)⁻¹ := by
  ext <;> simp [generator3, mul', inv']

/-- In the abelianization $\Gamma^{\mathrm{ab}}$, the image of `generator3` is trivial. -/
theorem of_generator3_eq_one : Abelianization.of generator3 = 1 := by
  rw [generator3_eq_commutator, map_mul, map_mul, map_mul, map_inv, map_inv]
  simp [mul_assoc, mul_inv_cancel]

/-- The $c$-component of $\Gamma$ is killed in the abelianization for every $c \in \mathbb{Z}$. -/
theorem of_c_component_trivial (c : ℤ) :
    Abelianization.of (mk 0 0 c 0) = (1 : Abelianization KTGamma) := by
  induction c using Int.induction_on with
  | zero => change Abelianization.of 1 = 1; exact map_one _
  | succ n ih =>
    have : mk 0 0 (n + 1) 0 = mk 0 0 n 0 * generator3 := by
      ext <;> simp [mul', generator3]

    rw [this, map_mul, ih, of_generator3_eq_one, mul_one]
  | pred n ih =>
    have : mk 0 0 (-↑n - 1) 0 = mk 0 0 (-↑n) 0 * generator3⁻¹ := by
      ext <;> simp [mul', inv', generator3]; ring

    rw [this, map_mul, ih, map_inv, of_generator3_eq_one, inv_one, mul_one]

/-- In $\Gamma^{\mathrm{ab}}$, the class of $(a,b,c,d)$ equals that of $(a,b,0,d)$. -/
theorem of_eq_of_drop_c (a b c d : ℤ) :
    Abelianization.of (mk a b c d) = Abelianization.of (mk a b 0 d) := by
  have : mk a b c d = mk a b 0 d * mk 0 0 c 0 := by ext <;> simp [mul']
  rw [this, map_mul, of_c_component_trivial, mul_one]

end KTGamma
