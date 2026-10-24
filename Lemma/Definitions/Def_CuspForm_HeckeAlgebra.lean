import Lemma.Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import Theorems.Thm_CuspForm_heckeULin_comm

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)

def heckeGenerators : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T = heckeTLin k hℓ hℓN} ∪
    {U | ∃ (q : ℕ) (hqN : q ∣ N), q.Prime ∧ q ∉ S ∧ U = heckeULin k hqN}

def heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  Algebra.adjoin ℤ (heckeGenerators N k S)

variable {N k S}

theorem heckeTLin_mem_heckeGenerators {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    heckeTLin k hℓ hℓN ∈ heckeGenerators N k S :=
  Or.inl ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩

theorem heckeULin_mem_heckeGenerators {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    heckeULin k hqN ∈ heckeGenerators N k S :=
  Or.inr ⟨q, hqN, hq, hqS, rfl⟩

theorem heckeTLin_mem_heckeAlgebra {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    heckeTLin k hℓ hℓN ∈ heckeAlgebra N k S :=
  Algebra.subset_adjoin (heckeTLin_mem_heckeGenerators hℓ hℓN hℓS)

theorem heckeULin_mem_heckeAlgebra {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    heckeULin k hqN ∈ heckeAlgebra N k S :=
  Algebra.subset_adjoin (heckeULin_mem_heckeGenerators hq hqN hqS)

theorem heckeGenerators_mono {S S' : Set ℕ} (h : S ⊆ S') :
    heckeGenerators N k S' ⊆ heckeGenerators N k S := by
  rintro T (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
  · exact heckeTLin_mem_heckeGenerators hℓ hℓN fun hS => hℓS (h hS)
  · exact heckeULin_mem_heckeGenerators hq hqN fun hS => hqS (h hS)

theorem heckeAlgebra_mono {S S' : Set ℕ} (h : S ⊆ S') : heckeAlgebra N k S' ≤ heckeAlgebra N k S :=
  Algebra.adjoin_mono (heckeGenerators_mono h)

theorem commute_of_mem_heckeGenerators {T T' : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)}
    (hT : T ∈ heckeGenerators N k S) (hT' : T' ∈ heckeGenerators N k S) : Commute T T' := by
  rcases hT with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, -, -, rfl⟩ <;>
    rcases hT' with ⟨ℓ', hℓ', hℓ'N, -, rfl⟩ | ⟨q', hq'N, -, -, rfl⟩
  · exact heckeTLin_comm k hℓ hℓN hℓ' hℓ'N
  · exact heckeTLin_heckeULin_comm k hℓ hℓN hq'N
  · exact (heckeTLin_heckeULin_comm k hℓ' hℓ'N hqN).symm
  · exact heckeULin_comm k hqN hq'N

variable (N k S)

instance heckeAlgebra.instIsMulCommutative : IsMulCommutative (heckeAlgebra N k S) :=
  Algebra.isMulCommutative_adjoin ℤ fun _ hT _ hT' => commute_of_mem_heckeGenerators hT hT'

open scoped IsMulCommutative in

instance heckeAlgebra.instCommRing : CommRing (heckeAlgebra N k S) := inferInstance

instance heckeAlgebra.instIsAddTorsionFree : IsAddTorsionFree (heckeAlgebra N k S) where
  nsmul_right_injective n hn a b hab := by
    apply Subtype.ext
    have h : (n : ℂ) • (a : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) =
        (n : ℂ) • (b : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) := by
      simp only [Nat.cast_smul_eq_nsmul]
      exact congrArg Subtype.val hab
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h

variable {N k S}

def heckeAlgebra.T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) : heckeAlgebra N k S :=
  ⟨heckeTLin k hℓ hℓN, heckeTLin_mem_heckeAlgebra hℓ hℓN hℓS⟩

def heckeAlgebra.U {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) : heckeAlgebra N k S :=
  ⟨heckeULin k hqN, heckeULin_mem_heckeAlgebra hq hqN hqS⟩

@[simp] theorem heckeAlgebra.coe_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    ((heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N k S) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = heckeTLin k hℓ hℓN := rfl

@[simp] theorem heckeAlgebra.coe_U {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    ((heckeAlgebra.U hq hqN hqS : heckeAlgebra N k S) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = heckeULin k hqN := rfl

end CuspForm

end
