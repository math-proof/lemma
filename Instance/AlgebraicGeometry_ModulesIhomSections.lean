-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ModulesIhomSections.lean: instance decls only.
import Mathlib
import Instance.PresheafOfModules_InternalHom
import Instance.SheafOfModules_Monoidal
import Lemma.AlgebraicGeometry.ModulesSectionsTensor
import Lemma.AlgebraicGeometry.ModulesIhomSections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct


noncomputable section

namespace SheafOfModules

open PresheafOfModules PresheafOfModules.InternalHom Functor.Monoidal Functor.LaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}


variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

instance isIso_ihomModelToIhom : IsIso (ihomModelToIhom 𝒪 h𝒪 M N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map (ihomModelToIhom 𝒪 h𝒪 M N)) := by
    rw [ihomModelToIhom, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J (isSheaf_ihomModel 𝒪 h𝒪 M N)
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

variable {M N}

variable (M N)

variable {M N}

variable (M) (P : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

variable {M P}

end SheafOfModules

end

