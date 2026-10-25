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
import Theorem.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part4
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- The abelianization of the Kodaira–Thurston fundamental group is $\Gamma^{\mathrm{ab}} \cong \mathbb{Z}^3$. -/
noncomputable def abelianizationEquiv :
    Abelianization KTGamma ≃*
      Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ :=
  MulEquiv.ofBijective liftedProj
    ⟨fun x y h => by
      have := congr_arg sectionHom h
      simp only [← MonoidHom.comp_apply, sectionHom_liftedProj, MonoidHom.id_apply] at this
      exact this,
     fun z => ⟨sectionHom z, by
      simp only [← MonoidHom.comp_apply, liftedProj_sectionHom, MonoidHom.id_apply]⟩⟩

end KTGamma
