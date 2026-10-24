import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesDet

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

abbrev fibreModule {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (F : (pullback c t).Modules) : (pullback (pullback.snd c t) s).Modules :=
  (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj F

@[simp] theorem picardBundle_def (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) :
    picardBundle c ε t M N = (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N) := rfl

@[simp] theorem thetaBundle_def (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    thetaBundle c ε t M r n = Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r))) := rfl

end AlgebraicGeometry.RelPicard

end
