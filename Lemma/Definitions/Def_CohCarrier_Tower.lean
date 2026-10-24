import Lemma.Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Prod

set_option autoImplicit false

namespace CohCarrier

open Polynomial

section Linear

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

noncomputable def heckeTLin (ℓ : ℕ) [NeZero ℓ] : H1 M H A →ₗ[R] H1 M H A where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

theorem heckeTLin_apply (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H A) :
    heckeTLin R A M H ℓ φ = heckeT M H ℓ A φ := rfl

abbrev Car (ℓ₀ : ℕ) [NeZero ℓ₀] : Type _ := Module.AEval' (heckeTLin R A M H ℓ₀)

end Linear

section Leg

variable (R : Type*) [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] {B : Type*} [AddCommGroup B] [Module R B]
variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {M' : ℕ} {H' : Subgroup (ZMod M')ˣ}

noncomputable def legOfComm (ℓ₀ : ℕ) [NeZero ℓ₀] (f : H1 M H A →ₗ[R] H1 M' H' B)
    (hf : ∀ φ, f (heckeT M H ℓ₀ A φ) = heckeT M' H' ℓ₀ B (f φ)) :
    Car R A M H ℓ₀ →ₗ[R[X]] Car R B M' H' ℓ₀ :=
  LinearMap.ofAEval (heckeTLin R A M H ℓ₀)
    ((Module.AEval'.of (heckeTLin R B M' H' ℓ₀)).toLinearMap ∘ₗ f) (fun φ => by
      show Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f (heckeT M H ℓ₀ A φ))
        = (X : R[X]) • Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f φ)
      rw [hf, Module.AEval'.X_smul_of]
      rfl)

theorem legOfComm_of (ℓ₀ : ℕ) [NeZero ℓ₀] (f : H1 M H A →ₗ[R] H1 M' H' B)
    (hf : ∀ φ, f (heckeT M H ℓ₀ A φ) = heckeT M' H' ℓ₀ B (f φ)) (φ : H1 M H A) :
    legOfComm R ℓ₀ f hf (Module.AEval'.of (heckeTLin R A M H ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B M' H' ℓ₀) (f φ) := by
  simp [legOfComm, LinearMap.ofAEval]

end Leg

section Eisenstein

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

noncomputable abbrev tw (ℓ₀ : ℕ) : R[X] := (X : R[X]) - C ((ℓ₀ : R) + 1)

set_option backward.isDefEq.respectTransparency false in

theorem tw_smul_of (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) :
    tw R ℓ₀ • Module.AEval'.of (heckeTLin R A M H ℓ₀) F
      = Module.AEval'.of (heckeTLin R A M H ℓ₀) (heckeT M H ℓ₀ A F - ((ℓ₀ : R) + 1) • F) := by
  rw [sub_smul, Module.AEval'.X_smul_of, map_sub, LinearEquiv.map_smul, Polynomial.C_eq_algebraMap,
    algebraMap_smul]
  rfl

def IsEis (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) : Prop :=
  heckeT M H ℓ₀ A F = ((ℓ₀ : R) + 1) • F

set_option backward.isDefEq.respectTransparency false in

theorem tw_smul_of_eq_zero (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) (hF : IsEis R A M H ℓ₀ F) :
    tw R ℓ₀ • Module.AEval'.of (heckeTLin R A M H ℓ₀) F = 0 := by
  rw [tw_smul_of, hF, sub_self, map_zero]

end Eisenstein

section ThreeCopy

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {L : Type*} [AddCommGroup L] [Module R L]
variable {L2 : Type*} [AddCommGroup L2] [Module R L2]

def threeCopy (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) : (V × V × V) →ₗ[R] L2 :=
  (i ∘ₗ rL) ∘ₗ LinearMap.fst R V (V × V) +
    ((j ∘ₗ rL) ∘ₗ LinearMap.fst R V V + (j ∘ₗ d) ∘ₗ LinearMap.snd R V V) ∘ₗ LinearMap.snd R V (V × V)

theorem threeCopy_apply (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) (f : V × V × V) :
    threeCopy rL d i j f = i (rL f.1) + (j (rL f.2.1) + j (d f.2.2)) := by
  simp [threeCopy]

def embComb (q : R) (T : V →ₗ[R] V) : V →ₗ[R] V × V × V :=
  (q • LinearMap.id).prod ((-T).prod LinearMap.id)

theorem embComb_apply (q : R) (T : V →ₗ[R] V) (v : V) :
    embComb q T v = (q • v, -T v, v) := rfl

theorem embComb_injective (q : R) (T : V →ₗ[R] V) : Function.Injective (embComb q T) :=
  fun v v' h => by simpa [embComb] using congrArg (fun w : V × V × V => w.2.2) h

theorem threeCopy_embComb_apply (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) (q : R) (T : V →ₗ[R] V)
    (v : V) :
    threeCopy rL d i j (embComb q T v) = q • i (rL v) - j (rL (T v)) + j (d v) := by
  rw [embComb_apply, threeCopy_apply, map_smul, map_smul, map_neg, map_neg]
  abel

end ThreeCopy

end CohCarrier
