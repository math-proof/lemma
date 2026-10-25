import Lemma.ModularCurve.HeckeModule
import Def.AlgebraicCurve_Differentials
import Def.ModularCurve_QExpansionDiff
import Lemma.ModularCurve.JZeroTateModule

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section OmegaAlong

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

def heckeOmegaAlong :
    Ω[↥(laurentBaseChange L (modularFunctionFieldFull N))⁄L] →ₗ[L]
      Ω[↥(laurentBaseChange L (modularFunctionFieldFull N))⁄L] :=
  letI := algebraAlong (heckeBetaBar L N ℓ)
  haveI := isScalarTower_along (heckeBetaBar L N ℓ)
  haveI : SMulCommClass L ↥(laurentBaseChange L (modularFunctionFieldFull N))
      ↥(laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    ⟨fun k f x => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
  ((traceDiff L ↥(laurentBaseChange L (modularFunctionFieldFull N))
      ↥(laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))).restrictScalars L).comp
    (pullbackDiff (heckeAlphaBar L N ℓ))

end OmegaAlong

section OmegaModule

variable (N : ℕ) [NeZero N]

def heckeOmegaBar (ℓ : Nat.Primes) :
    Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ] →ₗ[AlgebraicClosure ℚ]
      Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ] :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  heckeOmegaAlong (AlgebraicClosure ℚ) N ℓ

def HeckeOmegaPreservesBar : Prop :=
  ∀ (ℓ : Nat.Primes) (ω : Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ]),
    ω ∈ regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) →
      heckeOmegaBar N ℓ ω ∈ regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)

open Classical in

def heckeOmegaRegBar (ℓ : Nat.Primes) :
    Module.End ℤ ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaPreservesBar N then
    ((heckeOmegaBar N ℓ).restrict (fun ω hω => h ℓ ω hω)).toAddMonoidHom.toIntLinearMap
  else 0

def HeckeOmegaCommuteBar : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOmegaRegBar N ℓ * heckeOmegaRegBar N ℓ' = heckeOmegaRegBar N ℓ' * heckeOmegaRegBar N ℓ

theorem isMulCommutative_adjoin_heckeOmegaRegBar (h : HeckeOmegaCommuteBar N) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBar N))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

open scoped IsMulCommutative in

def heckeEvalOmegaBarAux (h : HeckeOmegaCommuteBar N) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBar N)) :
      Subalgebra ℤ (Module.End ℤ
        ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))) :=
  haveI := isMulCommutative_adjoin_heckeOmegaRegBar N h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeOmegaRegBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeOmegaRegBar N)))

def heckeEvalOmegaBar (h : HeckeOmegaCommuteBar N) :
    HeckeAlg →+* Module.End ℤ
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  ((Algebra.adjoin ℤ (Set.range (heckeOmegaRegBar N))).val.comp
    (heckeEvalOmegaBarAux N h)).toRingHom

open Classical in

@[implicit_reducible]
def heckeOmegaModuleBar :
    Module HeckeAlg ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaCommuteBar N then
    Module.compHom _ (heckeEvalOmegaBar N h)
  else
    Module.compHom _ (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

end OmegaModule

section Seam

variable (N : ℕ) [NeZero N]

def heckeKerJ : Ideal HeckeAlg :=
  letI := heckeModuleBar N
  Module.annihilator HeckeAlg (JZero N)


def heckeKerOmega : Ideal HeckeAlg :=
  letI := heckeOmegaModuleBar N
  Module.annihilator HeckeAlg
    ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))

structure HeckeSeam : Prop where
  omega_le_J : heckeKerOmega N ≤ heckeKerJ N
  J_le_omega : heckeKerJ N ≤ heckeKerOmega N
  tate : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (t : Fin n → HeckeAlg),
    letI := heckeModuleBar N
    LinearIndependent ℤ (Ideal.Quotient.mk (heckeKerJ N) ∘ t) →
      LinearIndependent ℚ_[p] (rationalHeckeRep p (JZero N) ∘ t)

end Seam

section OmegaAlong

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]


end OmegaAlong

section OmegaModule

variable (N : ℕ) [NeZero N]


open Classical in


open Classical in


open scoped IsMulCommutative in


open scoped IsMulCommutative in


open Classical in


open Classical in

end OmegaModule

namespace HeckeWord


variable (N : ℕ) [NeZero N]


open Classical in


open Classical in


end HeckeWord

end ModularCurve

end
