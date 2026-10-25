import Lemma.QuaternionAlgebra.EichlerOrder
import Lemma.QuaternionAlgebra.ReducedNorm
import Def.ModularCurve_UniformizedHeckeCurve
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Instance.AlgebraicCurve_IsCurveOver
import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
import Lemma.Compat.Mathlib430
import Instance.CerednikDrinfeld_ShimuraCurve
import Structure.CerednikDrinfeld_ShimuraCurve
import Abbrev.CerednikDrinfeld_ShimuraCurve

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve

namespace QuaternionAlgebra

variable (a b : ℚ)

def IsIndefiniteRamifiedExactlyAt (q q' : ℕ) : Prop :=
  (0 < a ∨ 0 < b) ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal)

end QuaternionAlgebra

namespace CerednikDrinfeld

open QuaternionAlgebra ModularCurve

variable {a b : ℚ}


namespace ShimuraCurveModel

variable {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
  {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

def heckeGenJ (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) : Module.End ℤ M.J :=
  (M.heckePic0 ℓ ℓ.prop).toIntLinearMap

@[simp] theorem heckeGenJ_apply (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeGenJ ℓ c = M.heckePic0 ℓ ℓ.prop c := rfl

theorem heckeGenJ_comm (M : ShimuraCurveModel R ι 𝒮) (ℓ ℓ' : Nat.Primes) :
    M.heckeGenJ ℓ * M.heckeGenJ ℓ' = M.heckeGenJ ℓ' * M.heckeGenJ ℓ := by
  apply LinearMap.ext
  intro c
  exact DFunLike.congr_fun (M.heckePic0_comm ℓ ℓ' ℓ.prop ℓ'.prop) c

theorem isMulCommutative_adjoin_heckeGenJ (M : ShimuraCurveModel R ι 𝒮) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range M.heckeGenJ)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact M.heckeGenJ_comm ℓ ℓ')

@[reducible] def commRingAdjoinJ (M : ShimuraCurveModel R ι 𝒮) :
    CommRing ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) :=
  { (inferInstance : Ring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ))) with
    mul_comm := M.isMulCommutative_adjoin_heckeGenJ.is_comm.comm }

def heckeJAux (M : ShimuraCurveModel R ι 𝒮) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range M.heckeGenJ) : Subalgebra ℤ (Module.End ℤ M.J)) :=
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) := M.commRingAdjoinJ.toCommSemiring
  MvPolynomial.aeval fun ℓ =>
    (⟨M.heckeGenJ ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ : Algebra.adjoin ℤ (Set.range M.heckeGenJ))

def heckeJ (M : ShimuraCurveModel R ι 𝒮) : HeckeAlg →+* Module.End ℤ M.J :=
  ((Algebra.adjoin ℤ (Set.range M.heckeGenJ)).val.comp M.heckeJAux).toRingHom

theorem heckeJ_mem_adjoin (M : ShimuraCurveModel R ι 𝒮) (x : HeckeAlg) :
    M.heckeJ x ∈ Algebra.adjoin ℤ (Set.range M.heckeGenJ) :=
  (M.heckeJAux x).2

theorem heckeJ_heckeGen (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) : M.heckeJ (heckeGen ℓ) = M.heckeGenJ ℓ := by
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) := M.commRingAdjoinJ.toCommSemiring
  show ((M.heckeJAux (heckeGen ℓ) : Module.End ℤ M.J)) = _
  rw [heckeJAux, heckeGen, MvPolynomial.aeval_X]

theorem heckeJ_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeJ (heckeGen ℓ) c = M.heckePic0 ℓ ℓ.prop c := by
  rw [heckeJ_heckeGen]
  rfl

def galJ (M : ShimuraCurveModel R ι 𝒮) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut M.J :=
  (DistribMulAction.toAddAut' (SemilinearAut (AlgebraicClosure ℚ) M.Fbar) M.J).comp M.gal

@[simp] theorem galJ_apply (M : ShimuraCurveModel R ι 𝒮) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : M.J) :
    M.galJ σ c = M.gal σ • c := rfl

theorem J_comm (M : ShimuraCurveModel R ι 𝒮) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (c : M.J),
      M.galJ σ (M.heckeJ x c) = M.heckeJ x (M.galJ σ c) := by
  intro σ x c
  let g : Module.End ℤ M.J := (M.galJ σ).toAddMonoidHom.toIntLinearMap
  have hle : Algebra.adjoin ℤ (Set.range M.heckeGenJ) ≤ Subalgebra.centralizer ℤ {g} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨ℓ, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    apply LinearMap.ext
    intro s
    exact M.gal_smul_heckePic0 σ ℓ ℓ.prop s
  have h := (Subalgebra.mem_centralizer_iff ℤ).1 (hle (M.heckeJ_mem_adjoin x)) g (Set.mem_singleton g)
  exact LinearMap.congr_fun h c

def signTwist (ε : Nat.Primes → ℤˣ) : HeckeAlg →+* HeckeAlg :=
  (MvPolynomial.aeval fun ℓ => ((ε ℓ : ℤ) : HeckeAlg) * MvPolynomial.X ℓ).toRingHom

@[simp] theorem signTwist_heckeGen (ε : Nat.Primes → ℤˣ) (ℓ : Nat.Primes) :
    signTwist ε (heckeGen ℓ) = ((ε ℓ : ℤ) : HeckeAlg) * heckeGen ℓ := by
  show (MvPolynomial.aeval fun ℓ => ((ε ℓ : ℤ) : HeckeAlg) * MvPolynomial.X ℓ) (MvPolynomial.X ℓ) = _
  rw [MvPolynomial.aeval_X]
  rfl

abbrev heckeJSigned (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) : HeckeAlg →+* Module.End ℤ M.J :=
  M.heckeJ.comp (signTwist ε)

theorem heckeJSigned_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeJSigned ε (heckeGen ℓ) c = (ε ℓ : ℤ) • M.heckePic0 ℓ ℓ.prop c := by
  rw [heckeJSigned, RingHom.comp_apply, signTwist_heckeGen, map_mul, map_intCast, Module.End.mul_apply,
    heckeJ_heckeGen_apply, Module.End.intCast_apply]

theorem J_comm_signed (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (c : M.J),
      M.galJ σ (M.heckeJSigned ε x c) = M.heckeJSigned ε x (M.galJ σ c) :=
  fun σ x c => M.J_comm σ (signTwist ε x) c

theorem finiteLevel_J (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (hp : 0 < p) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) →
        ∀ t : M.J, p • t = 0 → M.galJ σ t = t := by
  obtain ⟨L, hL, h⟩ := M.finiteLevel_torsion p hp
  refine ⟨L, hL, fun σ hσ t ht => h σ hσ t (Pic0.mem_torsion.2 ?_)⟩
  rw [natCast_zsmul]
  exact ht

def GoodReductionOutside (M : ShimuraCurveModel R ι 𝒮) (p S : ℕ) : Prop :=
  (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ S →
    ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
      ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : M.J, p • t = 0 → M.galJ σ t = t) ∧
  (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ S →
    ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
        ∀ t : M.J, p • t = 0 →
          M.galJ σ (M.galJ σ t) - M.heckeJ (heckeGen ⟨ℓ, hℓ⟩) (M.galJ σ t) + ℓ • t = 0)

theorem torsion_pTorsion (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : ∀ t : M.Tors p, p • t = 0 := by
  intro t
  have h : (p : ℤ) • (t : M.J) = 0 := Pic0.mem_torsion.1 t.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℤ]
  exact h

def restrictTors (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : Module.End ℤ M.J →+* Module.End ℤ (M.Tors p) where
  toFun f := f.restrict (p := (Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).toIntSubmodule)
    (q := (Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).toIntSubmodule) (fun x hx => by
      change x ∈ Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p at hx
      change f x ∈ Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p
      rw [Pic0.mem_torsion] at hx ⊢
      rw [← map_zsmul, hx, map_zero])
  map_one' := by apply LinearMap.ext; intro t; rfl
  map_mul' f g := by apply LinearMap.ext; intro t; rfl
  map_zero' := by apply LinearMap.ext; intro t; rfl
  map_add' f g := by apply LinearMap.ext; intro t; rfl

@[simp] theorem coe_restrictTors_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (f : Module.End ℤ M.J) (t : M.Tors p) :
    ((M.restrictTors p f t : M.Tors p) : M.J) = f t := rfl

def torsionHecke (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : HeckeAlg →+* Module.End ℤ (M.Tors p) :=
  (M.restrictTors p).comp M.heckeJ

@[simp] theorem coe_torsionHecke_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (x : HeckeAlg) (t : M.Tors p) :
    ((M.torsionHecke p x t : M.Tors p) : M.J) = M.heckeJ x t := rfl

theorem coe_torsionHecke_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (ℓ : Nat.Primes) (t : M.Tors p) :
    ((M.torsionHecke p (heckeGen ℓ) t : M.Tors p) : M.J) = M.heckePic0 ℓ ℓ.prop t := by
  rw [coe_torsionHecke_apply, heckeJ_heckeGen_apply]

def torsionGal (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut (M.Tors p) :=
  (DistribMulAction.toAddAut' (SemilinearAut (AlgebraicClosure ℚ) M.Fbar) (M.Tors p)).comp M.gal

@[simp] theorem coe_torsionGal_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : M.Tors p) :
    ((M.torsionGal p σ t : M.Tors p) : M.J) = M.galJ σ (t : M.J) := rfl

theorem torsion_comm (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : M.Tors p),
      M.torsionGal p σ (M.torsionHecke p x t) = M.torsionHecke p x (M.torsionGal p σ t) := by
  intro σ x t
  apply Subtype.ext
  rw [coe_torsionGal_apply, coe_torsionHecke_apply, coe_torsionHecke_apply, coe_torsionGal_apply]
  exact M.J_comm σ x t

theorem torsion_finiteLevel (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) [Fact p.Prime] :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → M.torsionGal p σ = 1 := by
  obtain ⟨L, hL, h⟩ := M.finiteLevel_torsion p (Fact.out : p.Prime).pos
  refine ⟨L, hL, fun σ hσ => AddEquiv.ext fun t => Subtype.ext ?_⟩
  exact h σ hσ t t.2

def IsTorsionOf (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (T : Type) [AddCommGroup T]
    (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Prop :=
  ∃ e : T →+ M.J, Function.Injective e ∧ e.range = Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : T), e (gal σ t) = M.gal σ • e t) ∧
    ∀ (ℓ : Nat.Primes) (t : T), e (hecke (heckeGen ℓ) t) = M.heckePic0 ℓ ℓ.prop (e t)

def RealizesJPrime (M : ShimuraCurveModel R ι 𝒮) {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (Dm : JPrimeTorsionDatum p E V A) : Prop :=
  M.IsTorsionOf p Dm.T Dm.hecke Dm.gal

def RealizesTwoPlace (M : ShimuraCurveModel R ι 𝒮) {p : ℕ} {E₁ V₁ E₂ V₂ : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : Prop :=
  M.IsTorsionOf p 𝒥.T 𝒥.hecke 𝒥.gal

theorem isTorsionOf_self (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    M.IsTorsionOf p (M.Tors p) (M.torsionHecke p) (M.torsionGal p) := by
  refine ⟨(Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).subtype, Subtype.val_injective,
    AddSubgroup.range_subtype _, fun σ t => ?_, fun ℓ t => ?_⟩
  · exact M.coe_torsionGal_apply p σ t
  · exact M.coe_torsionHecke_heckeGen_apply p ℓ t

end ShimuraCurveModel

end CerednikDrinfeld

end
