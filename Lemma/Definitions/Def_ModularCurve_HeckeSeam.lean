import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_AlgebraicCurve_Differentials
import Lemma.Definitions.Def_ModularCurve_QExpansionDiff
import Lemma.Definitions.Def_ModularCurve_JZeroTateModule

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

theorem heckeKerJ_eq_ker (h : HeckeOperatorsCommuteBar N) :
    heckeKerJ N = RingHom.ker (heckeEvalBar h) := by
  letI := heckeModuleBar N
  ext t
  rw [heckeKerJ, RingHom.mem_ker, Module.mem_annihilator]
  constructor
  · intro ht
    ext x
    simpa [heckeModuleBar_smul_def h] using ht x
  · intro ht x
    rw [heckeModuleBar_smul_def h, ht]
    rfl

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

def heckeOmegaAlongT :
    Ω[↥(laurentBaseChange L (modularFunctionFieldFull N))⁄L] →ₗ[L]
      Ω[↥(laurentBaseChange L (modularFunctionFieldFull N))⁄L] :=
  letI := algebraAlong (heckeAlphaBar L N ℓ)
  haveI := isScalarTower_along (heckeAlphaBar L N ℓ)
  haveI : SMulCommClass L ↥(laurentBaseChange L (modularFunctionFieldFull N))
      ↥(laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :=
    ⟨fun k f x => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
  ((traceDiff L ↥(laurentBaseChange L (modularFunctionFieldFull N))
      ↥(laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))).restrictScalars L).comp
    (pullbackDiff (heckeBetaBar L N ℓ))

end OmegaAlong

section OmegaModule

variable (N : ℕ) [NeZero N]

def heckeOmegaBarT (ℓ : Nat.Primes) :
    Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ] →ₗ[AlgebraicClosure ℚ]
      Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ] :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  heckeOmegaAlongT (AlgebraicClosure ℚ) N ℓ

def HeckeOmegaPreservesBarT : Prop :=
  ∀ (ℓ : Nat.Primes) (ω : Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ]),
    ω ∈ regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) →
      heckeOmegaBarT N ℓ ω ∈ regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)

open Classical in

def heckeOmegaRegBarQ (ℓ : Nat.Primes) :
    Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaPreservesBar N then
    (heckeOmegaBar N ℓ).restrict (fun ω hω => h ℓ ω hω)
  else 0

open Classical in

def heckeOmegaRegBarQT (ℓ : Nat.Primes) :
    Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaPreservesBarT N then
    (heckeOmegaBarT N ℓ).restrict (fun ω hω => h ℓ ω hω)
  else 0

def HeckeOmegaCommuteBarQ : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOmegaRegBarQ N ℓ * heckeOmegaRegBarQ N ℓ' = heckeOmegaRegBarQ N ℓ' * heckeOmegaRegBarQ N ℓ

def HeckeOmegaCommuteBarQT : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOmegaRegBarQT N ℓ * heckeOmegaRegBarQT N ℓ' = heckeOmegaRegBarQT N ℓ' * heckeOmegaRegBarQT N ℓ

theorem isMulCommutative_adjoin_heckeOmegaRegBarQ (h : HeckeOmegaCommuteBarQ N) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQ N))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

theorem isMulCommutative_adjoin_heckeOmegaRegBarQT (h : HeckeOmegaCommuteBarQT N) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQT N))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

open scoped IsMulCommutative in

def heckeEvalOmegaBarAuxQ (h : HeckeOmegaCommuteBarQ N) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQ N)) :
      Subalgebra ℤ (Module.End (AlgebraicClosure ℚ)
        ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))) :=
  haveI := isMulCommutative_adjoin_heckeOmegaRegBarQ N h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeOmegaRegBarQ N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQ N)))

def heckeEvalOmegaBarQ (h : HeckeOmegaCommuteBarQ N) :
    HeckeAlg →+* Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  ((Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQ N))).val.comp
    (heckeEvalOmegaBarAuxQ N h)).toRingHom

open scoped IsMulCommutative in

def heckeEvalOmegaBarAuxQT (h : HeckeOmegaCommuteBarQT N) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQT N)) :
      Subalgebra ℤ (Module.End (AlgebraicClosure ℚ)
        ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))) :=
  haveI := isMulCommutative_adjoin_heckeOmegaRegBarQT N h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeOmegaRegBarQT N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQT N)))

def heckeEvalOmegaBarQT (h : HeckeOmegaCommuteBarQT N) :
    HeckeAlg →+* Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  ((Algebra.adjoin ℤ (Set.range (heckeOmegaRegBarQT N))).val.comp
    (heckeEvalOmegaBarAuxQT N h)).toRingHom

open Classical in

def heckeEvalOmegaBarQTotal :
    HeckeAlg →+* Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaCommuteBarQ N then heckeEvalOmegaBarQ N h
  else (Int.castRingHom _).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

open Classical in

def heckeEvalOmegaBarQTTotal :
    HeckeAlg →+* Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  if h : HeckeOmegaCommuteBarQT N then heckeEvalOmegaBarQT N h
  else (Int.castRingHom _).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))
end OmegaModule

namespace HeckeWord

def HeckeInputsAlongT (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N]
    [NeZero ℓ] : Prop :=
  ∃ (hα : HeckeAlphaBarIntegral L N ℓ) (_ : HeckeBetaBarIntegral L N ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))))
    (hfin : FiniteAlong L (heckeBetaBar L N ℓ)),
    FundamentalIdentityAlong L (heckeAlphaBar L N ℓ) hα ∧
      NormFormulaAlong L (heckeBetaBar L N ℓ) hfin

variable (N : ℕ) [NeZero N]

def letterKey (ℓ : Nat.Primes) : Prop :=
  letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ ∧
      HeckeInputsAlongT (AlgebraicClosure ℚ) N ℓ) ∧
    HeckeOmegaPreservesBar N ∧ HeckeOmegaPreservesBarT N

open Classical in

def letterJ : Nat.Primes ⊕ Nat.Primes → Module.End ℤ (JZero N) :=
  Sum.elim
    (fun ℓ =>
      letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      if h : letterKey N ℓ then
        haveI := h.1.1.snd.snd.fst
        (heckePic0Bar h.1.1.fst h.1.1.snd.fst h.1.1.snd.snd.snd.snd.1
          h.1.1.snd.snd.snd.fst h.1.1.snd.snd.snd.snd.2).toIntLinearMap
      else 0)
    (fun ℓ =>
      letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      if h : letterKey N ℓ then
        haveI := h.1.2.snd.snd.fst
        (heckePic0BarTranspose h.1.2.fst h.1.2.snd.fst h.1.2.snd.snd.snd.snd.1
          h.1.2.snd.snd.snd.fst h.1.2.snd.snd.snd.snd.2).toIntLinearMap
      else 0)

open Classical in

def letterO :
    Nat.Primes ⊕ Nat.Primes →
      Module.End (AlgebraicClosure ℚ)
        ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  Sum.elim
    (fun ℓ =>
      if h : letterKey N ℓ then
        (heckeOmegaBar N ℓ).restrict (fun ω hω => h.2.1 ℓ ω hω)
      else 0)
    (fun ℓ =>
      if h : letterKey N ℓ then
        (heckeOmegaBarT N ℓ).restrict (fun ω hω => h.2.2 ℓ ω hω)
      else 0)

def wordJ (w : List (Nat.Primes ⊕ Nat.Primes)) : Module.End ℤ (JZero N) :=
  (w.map (letterJ N)).prod

def wordO (w : List (Nat.Primes ⊕ Nat.Primes)) :
    Module.End (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :=
  (w.reverse.map (letterO N)).prod

def wordTr (w : List (Nat.Primes ⊕ Nat.Primes)) : List (Nat.Primes ⊕ Nat.Primes) :=
  (w.map Sum.swap).reverse

def vpEnd (p : ℕ) [Fact p.Prime] (f : Module.End ℤ (JZero N)) :
    Module.End ℚ_[p] (RationalTateModule p (JZero N)) :=
  Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p (JZero N))
    (TateModule.rep p (JZero N) (Module.End ℤ (JZero N)) f)

end HeckeWord

end ModularCurve

end
