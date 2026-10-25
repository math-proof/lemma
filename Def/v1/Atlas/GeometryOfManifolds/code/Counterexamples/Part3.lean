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
import Theorem.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part3
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- The projection homomorphism $\Gamma \to \mathbb{Z}^3$ sending $(a,b,c,d) \mapsto (a,b,d)$. -/
def projHom : KTGamma →* Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ where
  toFun g := (Multiplicative.ofAdd g.a, Multiplicative.ofAdd g.b, Multiplicative.ofAdd g.d)
  map_one' := by simp [one']
  map_mul' g h := by
    simp only [mul_def, mul']
    ext <;> simp [ofAdd_add]

/-- The induced homomorphism $\Gamma^{\mathrm{ab}} \to \mathbb{Z}^3$ from `projHom`. -/
def liftedProj :
    Abelianization KTGamma →* Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ :=
  Abelianization.lift projHom

/-- A section $\mathbb{Z}^3 \to \Gamma^{\mathrm{ab}}$ of `liftedProj`, sending $(x,y,z)$ to the class of $(x,y,0,z)$. -/
def sectionHom :
    Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ →* Abelianization KTGamma where
  toFun p := Abelianization.of
    (mk (Multiplicative.toAdd p.1) (Multiplicative.toAdd p.2.1) 0 (Multiplicative.toAdd p.2.2))
  map_one' := by change Abelianization.of 1 = 1; exact map_one _
  map_mul' p q := by
    show Abelianization.of _ = Abelianization.of _ * Abelianization.of _
    rw [← map_mul, mul_def, mul']
    exact (of_eq_of_drop_c _ _ _ _).symm

end KTGamma
