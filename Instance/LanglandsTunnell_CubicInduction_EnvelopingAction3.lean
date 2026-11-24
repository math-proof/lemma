module
public import Theorem.Matrix.CubicInduction_ArchSmoothSpace3
public import Theorem.Matrix.CubicInduction_EnvelopingAction3
public import Def.LanglandsTunnell_CubicInduction_ArchSmoothSpace3
public import Def.LanglandsTunnell_CubicInduction_EnvelopingAction3
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_LanglandsTunnell_CubicInduction_EnvelopingAction3.lean: instance decls only.

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm


namespace LanglandsTunnell.CubicInduction.WhittakerBlock

scoped instance instEnvelopingModule3 : Module envelopingAlgebra3 smoothFunctions3 := envelopingModule3

scoped instance instEnvelopingScalarTower3 : IsScalarTower ℂ envelopingAlgebra3 smoothFunctions3 :=
  ⟨fun c u φ => by
    show envelopingHom3 (c • u) φ = c • envelopingHom3 u φ
    rw [map_smul]
    rfl⟩

end LanglandsTunnell.CubicInduction.WhittakerBlock
end
