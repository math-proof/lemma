import Mathlib
import Lemma.WeierstrassCurve.ProjModel
import Abbrev.AlgebraicGeometry_RelEffCartierDivSum
import Def.ModularCurve_WeierstrassLevelComponents
import Structure.WeierstrassCurve_DrinfeldBasisGlobal

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)


variable {W}


def GroupLawFamily.IsChordTangent {A : Type u} [CommRing A] (𝒢 : GroupLawFamily A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), ∃ ev, IsPointsEval W (𝒢 T W) ev


def drinfeldComponent (A : Type u) [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ) (𝒯 : DrinfeldTransport A 𝒢 q) :
    ModularCurve.LevelComponent A where
  obj T _ _ := RawDrinfeldPair T
  IsLevel W x := IsDrinfeldLevel 𝒢 q W x
  map f x := 𝒯.map f x
  act C x := 𝒯.act C x
  map_id x := 𝒯.map_id x
  map_comp f g x := 𝒯.map_comp f g x
  act_one x := 𝒯.act_one x
  act_mul C C' x := 𝒯.act_mul C C' x
  map_act f C x := 𝒯.map_act f C x
  isLevel_map f W x h := 𝒯.isLevel_map f W x h
  isLevel_act C W x h := 𝒯.isLevel_act C W x h

noncomputable def fullLevelRigidData (A : Type u) [CommRing A] (ℓ N q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (ModularCurve.kernelVariableChangeDeg C ((N - 1) / 2) h))
    (𝒢 : GroupLawFamily A) (𝒯 : DrinfeldTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ModularCurve.weierstrassLevelRigidData A ℓ N hℓ hN (drinfeldComponent A 𝒢 q 𝒯)

end WeierstrassCurve.DrinfeldGlobal

end
