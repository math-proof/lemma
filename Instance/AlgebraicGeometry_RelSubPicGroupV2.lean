-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelSubPicGroupV2.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Lemma.AlgebraicGeometry.RepresentsRelSubPic
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Lemma.AlgebraicGeometry.RelativeGroupLawGrpObj
import Structure.JacJ1Iface
import Abbrev.SheafOfModules_MonoidalV2
import Lemma.AlgebraicGeometry.RelSubPicGroup
import Lemma.AlgebraicGeometry.RelSubPicGroupV2

section InlinedTheorems


section LinkageInlined_68107509

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace PresheafOfModules.IsMonoidalW

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

private local instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
private local instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full

end PresheafOfModules.IsMonoidalW

end

end LinkageInlined_68107509


section LinkageInlined_23d4f55a

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits


namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}

variable (U : X.Opens)

variable {U} (L : X.Modules)


private local instance isIso_sheafify_map_ev (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    IsIso ((Modules.sheafify X).map (ev (R := X.sheaf.obj) L.val)) := by
  have hW : (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map
      (ev (R := X.sheaf.obj) L.val)) :=
    W_ev (R := X.sheaf.obj) L.val (fun V => ⟨trivSieve L V, trivSieve_mem L Fact.out V,
      fun W i hi => hi⟩)
  have h : ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (ev (R := X.sheaf.obj) L.val) := by
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)]
    exact hW
  exact h

end AlgebraicGeometry.Scheme.Modules

end LinkageInlined_23d4f55a

end InlinedTheorems

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

open scoped CategoryTheory.MonObj

