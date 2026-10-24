import Lemma.Definitions.Def_ModularCurve_ComponentGroupHecke
import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_CerednikDrinfeld_Ribbon

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def awayIdeal (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) : Ideal HeckeAlg :=
  Ideal.span ({t | ∃ n : ℕ, (n : HeckeAlg) ∈ 𝔪 ∧ t = n} ∪
    {t | ∃ ℓ : Nat.Primes, ℓ ∉ S ∧ ∃ b : ℤ,
      heckeGen ℓ - MvPolynomial.C b ∈ 𝔪 ∧ t = heckeGen ℓ - MvPolynomial.C b})

theorem awayIdeal_le (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) : awayIdeal S 𝔪 ≤ 𝔪 := by
  refine Ideal.span_le.2 ?_
  rintro t (⟨n, hn, rfl⟩ | ⟨ℓ, -, b, hb, rfl⟩)
  · exact hn
  · exact hb

theorem natCast_mem_awayIdeal {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg} {n : ℕ}
    (hn : (n : HeckeAlg) ∈ 𝔪) : (n : HeckeAlg) ∈ awayIdeal S 𝔪 :=
  Ideal.subset_span (Or.inl ⟨n, hn, rfl⟩)

theorem heckeGen_sub_C_mem_awayIdeal {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg} {ℓ : Nat.Primes}
    (hℓ : ℓ ∉ S) {b : ℤ} (hb : heckeGen ℓ - MvPolynomial.C b ∈ 𝔪) :
    heckeGen ℓ - MvPolynomial.C b ∈ awayIdeal S 𝔪 :=
  Ideal.subset_span (Or.inr ⟨ℓ, hℓ, b, hb, rfl⟩)

def HasAwaySupport (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) (M : Type*) [AddCommGroup M]
    [Module HeckeAlg M] : Prop :=
  (awayIdeal S 𝔪 • ⊤ : Submodule HeckeAlg M) ≠ ⊤

def anemicInclusion (S : Finset Nat.Primes) :
    MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ →+* HeckeAlg :=
  (MvPolynomial.rename (Subtype.val : {ℓ : Nat.Primes // ℓ ∉ S} → Nat.Primes)).toRingHom

theorem anemicInclusion_X (S : Finset Nat.Primes) (ℓ : {ℓ : Nat.Primes // ℓ ∉ S}) :
    anemicInclusion S (MvPolynomial.X ℓ) = heckeGen ℓ.1 :=
  MvPolynomial.rename_X _ ℓ

def anemicContraction (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) :
    Ideal (MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ) :=
  𝔪.comap (anemicInclusion S)

theorem mem_anemicContraction {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg}
    {t : MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ} :
    t ∈ anemicContraction S 𝔪 ↔ anemicInclusion S t ∈ 𝔪 :=
  Ideal.mem_comap

end ModularCurve

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}

theorem heckeDivisorAction_transpose (T : Matrix E E ℤ) (x : E → ℤ) :
    heckeDivisorAction T.transpose x = T.mulVec x := by
  ext j
  simp [heckeDivisorAction_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

namespace HeckeData

variable (H : HeckeData D)

structure LatticeHyp (H : HeckeData D) where

  n : Nat.Primes → ℤ

  colSum : ∀ ℓ, HeckeRowSums (H.T ℓ).transpose (n ℓ)

  nV : Nat.Primes → ℤ

  colSumV : ∀ ℓ, HeckeRowSums (H.Tv ℓ).transpose (nV ℓ)

variable (h : H.LatticeHyp)

def latticeOp (ℓ : Nat.Primes) : characterLattice E →ₗ[ℤ] characterLattice E :=
  heckeCharacterAction (H.T ℓ).transpose (h.colSum ℓ)

theorem coe_latticeOp (ℓ : Nat.Primes) (x : characterLattice E) :
    (H.latticeOp h ℓ x : E → ℤ) = (H.T ℓ).mulVec x :=
  heckeDivisorAction_transpose _ _

theorem latticeOp_comm (ℓ ℓ' : Nat.Primes) (x : characterLattice E) :
    H.latticeOp h ℓ (H.latticeOp h ℓ' x) = H.latticeOp h ℓ' (H.latticeOp h ℓ x) := by
  apply Subtype.ext
  simp only [coe_latticeOp, Matrix.mulVec_mulVec, (H.comm ℓ ℓ').eq]

def latticeOpV (ℓ : Nat.Primes) : characterLattice V →ₗ[ℤ] characterLattice V :=
  heckeCharacterAction (H.Tv ℓ).transpose (h.colSumV ℓ)

theorem coe_latticeOpV (ℓ : Nat.Primes) (x : characterLattice V) :
    (H.latticeOpV h ℓ x : V → ℤ) = (H.Tv ℓ).mulVec x :=
  heckeDivisorAction_transpose _ _

theorem latticeOpV_comm (ℓ ℓ' : Nat.Primes) (x : characterLattice V) :
    H.latticeOpV h ℓ (H.latticeOpV h ℓ' x) = H.latticeOpV h ℓ' (H.latticeOpV h ℓ x) := by
  apply Subtype.ext
  simp only [coe_latticeOpV, Matrix.mulVec_mulVec, (H.commv ℓ ℓ').eq]

end HeckeData

end CerednikDrinfeld
