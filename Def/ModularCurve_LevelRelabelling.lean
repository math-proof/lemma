import Mathlib
import Instance.ModularCurve_LevelModuliPackage
import Def.ModularCurve_WeierstrassLevelModuliDatum
import Def.ModularCurve_WeierstrassLevelComponents
import Instance.ModularCurve_KatzLevelP
import Def.WeierstrassCurve_DrinfeldLevelFunctor

set_option autoImplicit false

universe u

noncomputable section

open scoped Classical

namespace ModularCurve.LevelRelabelling

section LevelP

variable {T : Type u} [Field T] (W : WeierstrassCurve T)

def toPoint (x y : T) : W.toAffine.Point :=
  if h : W.toAffine.Nonsingular x y then WeierstrassCurve.Affine.Point.some x y h else 0

def ofPoint : W.toAffine.Point → T × T
  | WeierstrassCurve.Affine.Point.zero => (0, 0)
  | WeierstrassCurve.Affine.Point.some x y _ => (x, y)

def LevelPData.relabel (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T) : ModularCurve.LevelPData T :=
  let P := toPoint W D.xP D.yP
  let Q := toPoint W D.xQ D.yQ
  let P' := ofPoint W (g 0 0 • P + g 1 0 • Q)
  let Q' := ofPoint W (g 0 1 • P + g 1 1 • Q)
  ⟨P'.1, P'.2, Q'.1, Q'.2⟩

end LevelP

section Drinfeld

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}

def zsmulSection (G : RelativeGroupLaw T (projModelStrCR W)) : ℤ → Section W → Section W
  | Int.ofNat k, P => G.nsmul _ k P
  | Int.negSucc k, P => G.inv _ (G.nsmul _ (k + 1) P)

def zlinComb (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (a b : ℤ) : Section W :=
  G.mul _ (zsmulSection G a P) (zsmulSection G b Q)

variable {A : Type u} [CommRing A] [Algebra A T]

def RawDrinfeldPair.relabel (𝒢 : GroupLaws A) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : RawDrinfeldPair T)
    (hΔ : IsUnit x.curve.Δ) : RawDrinfeldPair T :=
  ⟨x.curve,
    zlinComb (𝒢 T x.curve hΔ) x.P x.Q (g 0 0) (g 1 0),
    zlinComb (𝒢 T x.curve hΔ) x.P x.Q (g 0 1) (g 1 1)⟩

end Drinfeld

section Pin

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

def IsModuliRelabelling (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel M' h →
        (C • W).IsCyclicKernel M' (ModularCurve.kernelVariableChangeDeg C ((M' - 1) / 2) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidData A ℓ M' q hℓ hN 𝒢 𝒯).toLevelModuliDatum.ProblemAut) : Prop :=
  ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type u) [Field T] [Algebra A T]
    (x x' : (rigidData A ℓ M' q hℓ hN 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
    x'.curve = x.curve →
    x'.level.1 = x.level.1 →
    x'.level.2.1 = LevelPData.relabel x.curve ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
    x'.level.2.2 = RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
    (ρ γ).act (Quot.mk _ x) = Quot.mk _ x'

end Pin

end ModularCurve.LevelRelabelling

end
