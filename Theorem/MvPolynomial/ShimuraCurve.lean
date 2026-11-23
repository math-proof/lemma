module

public import Theorem.QuaternionAlgebra.EichlerOrder
public import Theorem.QuaternionAlgebra.ReducedNorm
public import Def.ModularCurve_UniformizedHeckeCurve
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Instance.AlgebraicCurve_IsCurveOver
public import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
public import Theorem.Ideal.Mathlib430
public import Instance.CerednikDrinfeld_ShimuraCurve
public import Structure.CerednikDrinfeld_ShimuraCurve
public import Abbrev.CerednikDrinfeld_ShimuraCurve

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve

namespace QuaternionAlgebra

variable (a b : ℚ)


@[simp] public theorem heckeGenJ_apply (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeGenJ ℓ c = M.heckePic0 ℓ ℓ.prop c := rfl


public theorem heckeGenJ_comm (M : ShimuraCurveModel R ι 𝒮) (ℓ ℓ' : Nat.Primes) :
    M.heckeGenJ ℓ * M.heckeGenJ ℓ' = M.heckeGenJ ℓ' * M.heckeGenJ ℓ := by
  apply LinearMap.ext
  intro c
  exact DFunLike.congr_fun (M.heckePic0_comm ℓ ℓ' ℓ.prop ℓ'.prop) c


public theorem isMulCommutative_adjoin_heckeGenJ (M : ShimuraCurveModel R ι 𝒮) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range M.heckeGenJ)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact M.heckeGenJ_comm ℓ ℓ')


public theorem heckeJ_mem_adjoin (M : ShimuraCurveModel R ι 𝒮) (x : HeckeAlg) :
    M.heckeJ x ∈ Algebra.adjoin ℤ (Set.range M.heckeGenJ) :=
  (M.heckeJAux x).2


public theorem heckeJ_heckeGen (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) : M.heckeJ (heckeGen ℓ) = M.heckeGenJ ℓ := by
  letI : CommSemiring ↥(Algebra.adjoin ℤ (Set.range M.heckeGenJ)) := M.commRingAdjoinJ.toCommSemiring
  show ((M.heckeJAux (heckeGen ℓ) : Module.End ℤ M.J)) = _
  rw [heckeJAux, heckeGen, MvPolynomial.aeval_X]


public theorem heckeJ_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeJ (heckeGen ℓ) c = M.heckePic0 ℓ ℓ.prop c := by
  rw [heckeJ_heckeGen]
  rfl


@[simp] public theorem galJ_apply (M : ShimuraCurveModel R ι 𝒮) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : M.J) :
    M.galJ σ c = M.gal σ • c := rfl


public theorem J_comm (M : ShimuraCurveModel R ι 𝒮) :
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


@[simp] public theorem signTwist_heckeGen (ε : Nat.Primes → ℤˣ) (ℓ : Nat.Primes) :
    signTwist ε (heckeGen ℓ) = ((ε ℓ : ℤ) : HeckeAlg) * heckeGen ℓ := by
  show (MvPolynomial.aeval fun ℓ => ((ε ℓ : ℤ) : HeckeAlg) * MvPolynomial.X ℓ) (MvPolynomial.X ℓ) = _
  rw [MvPolynomial.aeval_X]
  rfl


public theorem heckeJSigned_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) (ℓ : Nat.Primes) (c : M.J) :
    M.heckeJSigned ε (heckeGen ℓ) c = (ε ℓ : ℤ) • M.heckePic0 ℓ ℓ.prop c := by
  rw [heckeJSigned, RingHom.comp_apply, signTwist_heckeGen, map_mul, map_intCast, Module.End.mul_apply,
    heckeJ_heckeGen_apply, Module.End.intCast_apply]


public theorem J_comm_signed (M : ShimuraCurveModel R ι 𝒮) (ε : Nat.Primes → ℤˣ) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (c : M.J),
      M.galJ σ (M.heckeJSigned ε x c) = M.heckeJSigned ε x (M.galJ σ c) :=
  fun σ x c => M.J_comm σ (signTwist ε x) c


public theorem finiteLevel_J (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (hp : 0 < p) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) →
        ∀ t : M.J, p • t = 0 → M.galJ σ t = t := by
  obtain ⟨L, hL, h⟩ := M.finiteLevel_torsion p hp
  refine ⟨L, hL, fun σ hσ t ht => h σ hσ t (Pic0.mem_torsion.2 ?_)⟩
  rw [natCast_zsmul]
  exact ht


public theorem torsion_pTorsion (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : ∀ t : M.Tors p, p • t = 0 := by
  intro t
  have h : (p : ℤ) • (t : M.J) = 0 := Pic0.mem_torsion.1 t.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℤ]
  exact h


@[simp] public theorem coe_restrictTors_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (f : Module.End ℤ M.J) (t : M.Tors p) :
    ((M.restrictTors p f t : M.Tors p) : M.J) = f t := rfl


@[simp] public theorem coe_torsionHecke_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (x : HeckeAlg) (t : M.Tors p) :
    ((M.torsionHecke p x t : M.Tors p) : M.J) = M.heckeJ x t := rfl


public theorem coe_torsionHecke_heckeGen_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) (ℓ : Nat.Primes) (t : M.Tors p) :
    ((M.torsionHecke p (heckeGen ℓ) t : M.Tors p) : M.J) = M.heckePic0 ℓ ℓ.prop t := by
  rw [coe_torsionHecke_apply, heckeJ_heckeGen_apply]


@[simp] public theorem coe_torsionGal_apply (M : ShimuraCurveModel R ι 𝒮) (p : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : M.Tors p) :
    ((M.torsionGal p σ t : M.Tors p) : M.J) = M.galJ σ (t : M.J) := rfl


public theorem torsion_comm (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : M.Tors p),
      M.torsionGal p σ (M.torsionHecke p x t) = M.torsionHecke p x (M.torsionGal p σ t) := by
  intro σ x t
  apply Subtype.ext
  rw [coe_torsionGal_apply, coe_torsionHecke_apply, coe_torsionHecke_apply, coe_torsionGal_apply]
  exact M.J_comm σ x t


public theorem torsion_finiteLevel (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) [Fact p.Prime] :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → M.torsionGal p σ = 1 := by
  obtain ⟨L, hL, h⟩ := M.finiteLevel_torsion p (Fact.out : p.Prime).pos
  refine ⟨L, hL, fun σ hσ => AddEquiv.ext fun t => Subtype.ext ?_⟩
  exact h σ hσ t t.2


public theorem isTorsionOf_self (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) :
    M.IsTorsionOf p (M.Tors p) (M.torsionHecke p) (M.torsionGal p) := by
  refine ⟨(Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p).subtype, Subtype.val_injective,
    AddSubgroup.range_subtype _, fun σ t => ?_, fun ℓ t => ?_⟩
  · exact M.coe_torsionGal_apply p σ t
  · exact M.coe_torsionHecke_heckeGen_apply p ℓ t

end ShimuraCurveModel

end CerednikDrinfeld

end
