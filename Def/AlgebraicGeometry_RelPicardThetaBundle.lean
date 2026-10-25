import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Instance.SheafOfModules_Monoidal
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Abbrev.AlgebraicGeometry_ModulesDet

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

def sectionIdeal : (pullback c t).IdealSheafData := (rigSection c t ε).ker

def sectionTwist (r : ℕ) : (pullback c t).Modules := ((sectionIdeal c ε t) ^ r).invModule

def picardBundle (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N)

def thetaBundle (M : RigidifiedLineBundle c ε t) (r n : ℕ) : T.Modules :=
  Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r)))

end AlgebraicGeometry.RelPicard

end
