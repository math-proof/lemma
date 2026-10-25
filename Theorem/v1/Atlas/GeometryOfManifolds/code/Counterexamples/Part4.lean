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
import Def.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part3
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- The composite $\mathbb{Z}^3 \xrightarrow{\mathrm{sec}} \Gamma^{\mathrm{ab}} \xrightarrow{\mathrm{proj}} \mathbb{Z}^3$ is the identity. -/
theorem liftedProj_sectionHom : liftedProj.comp sectionHom = MonoidHom.id _ := by
  apply MonoidHom.ext; intro ⟨x, y, z⟩
  simp [liftedProj, sectionHom, projHom]

/-- The composite $\Gamma^{\mathrm{ab}} \xrightarrow{\mathrm{proj}} \mathbb{Z}^3 \xrightarrow{\mathrm{sec}} \Gamma^{\mathrm{ab}}$ is the identity. -/
theorem sectionHom_liftedProj : sectionHom.comp liftedProj = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext; intro ⟨a, b, c, d⟩
  simp [liftedProj, sectionHom, projHom]
  exact (of_eq_of_drop_c a b c d).symm


end KTGamma
