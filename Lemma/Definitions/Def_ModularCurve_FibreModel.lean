import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Lemma.Definitions.Def_ModularCurve_PhiGen
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace CharPModel

open AlgebraicCurve

variable (N : ℕ) [NeZero N]

def jBar : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩

def jNBar : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def constantsHom : A →+* laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  (algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))).comp A.subtype

def affineBaseFin : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subring.closure (Set.range (constantsHom N A) ∪ {jBar N})

def affineBaseInf : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subring.closure (Set.range (constantsHom N A) ∪ {(jBar N)⁻¹})

structure FibreModel (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ]
    (red : A →+* k) : Type _ where

  BFin : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

  BInf : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

  constFin_mem : ∀ a : A, constantsHom N A a ∈ BFin

  constInf_mem : ∀ a : A, constantsHom N A a ∈ BInf

  jBar_mem : jBar N ∈ BFin

  jNBar_mem : (jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ BFin

  jInvBar_mem : (jBar N)⁻¹ ∈ BInf

  integralFin : ∀ b : BFin, ∃ p : Polynomial (affineBaseFin N A),
    p.Monic ∧ Polynomial.eval₂ (affineBaseFin N A).subtype (b : laurentBaseChange (AlgebraicClosure
        ℚ) (modularFunctionFieldFull N)) p = 0

  integralInf : ∀ b : BInf, ∃ p : Polynomial (affineBaseInf N A),
    p.Monic ∧ Polynomial.eval₂ (affineBaseInf N A).subtype (b : laurentBaseChange (AlgebraicClosure
        ℚ) (modularFunctionFieldFull N)) p = 0

  piFin : BFin →+* modularFunctionFieldC k N

  piInf : BInf →+* modularFunctionFieldC k N

  piFin_const : ∀ a : A,
    piFin ⟨constantsHom N A a, constFin_mem a⟩ = algebraMap k (modularFunctionFieldC k N) (red a)

  piInf_const : ∀ a : A,
    piInf ⟨constantsHom N A a, constInf_mem a⟩ = algebraMap k (modularFunctionFieldC k N) (red a)

  piFin_j : piFin ⟨jBar N, jBar_mem⟩ = ⟨jqModC k, jqModC_mem k N⟩

  piFin_jN : piFin ⟨jNBar N, jNBar_mem⟩ = ⟨jqNModC k N, jqNModC_mem k N⟩

  piInf_jInv : piInf ⟨(jBar N)⁻¹, jInvBar_mem⟩ =
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹

  ker_piFin : RingHom.ker piFin =
    Ideal.span ((fun a : A => (⟨constantsHom N A a, constFin_mem a⟩ : BFin)) ''
      (IsLocalRing.maximalIdeal A : Set A))

  ker_piInf : RingHom.ker piInf =
    Ideal.span ((fun a : A => (⟨constantsHom N A a, constInf_mem a⟩ : BInf)) ''
      (IsLocalRing.maximalIdeal A : Set A))

  intClosed_piFin : ∀ x : modularFunctionFieldC k N,
    (∃ p : Polynomial piFin.range, p.Monic ∧ Polynomial.eval₂ piFin.range.subtype x p = 0) →
    x ∈ piFin.range

  intClosed_piInf : ∀ x : modularFunctionFieldC k N,
    (∃ p : Polynomial piInf.range, p.Monic ∧ Polynomial.eval₂ piInf.range.subtype x p = 0) →
    x ∈ piInf.range

  frac_piFin : ∀ x : modularFunctionFieldC k N,
    ∃ b c : BFin, piFin c ≠ 0 ∧ x * piFin c = piFin b

  frac_piInf : ∀ x : modularFunctionFieldC k N,
    ∃ b c : BInf, piInf c ≠ 0 ∧ x * piInf c = piInf b

end CharPModel
end ModularCurve
