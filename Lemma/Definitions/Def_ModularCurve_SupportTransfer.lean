import Mathlib
import Lemma.Definitions.Def_CuspForm_HeckeAlgebra
import Lemma.Definitions.Def_ModularCurve_MazurPrincipleCore
import Lemma.Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ExitIdeal

variable (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ)

def exitGen (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N} :=
  CuspForm.heckeAlgebra.T (S := {n : ℕ | n ∣ N}) hℓ hℓN hℓN
    - ((W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N})

def exitIdealGens : Set (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) :=
  insert ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N})
    {x | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      W.IsGoodPrimeFor ℓ ∧ ℓ ≠ p ∧ x = exitGen N W ℓ hℓ hℓN}

def exitIdeal : Ideal (CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) :=
  Ideal.span (exitIdealGens N W p)

theorem natCast_mem_exitIdeal : ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ exitIdeal N W p :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem exitGen_mem_exitIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hgood : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p) :
    exitGen N W ℓ hℓ hℓN ∈ exitIdeal N W p :=
  Ideal.subset_span (Set.mem_insert_of_mem _ ⟨ℓ, hℓ, hℓN, hgood, hℓp, rfl⟩)

end ExitIdeal

section SupportTransfer

variable (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ)
  (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg)
  (J₀ : Type*) [AddCommGroup J₀] [Module HeckeAlg J₀]

def SupportTransfer : Prop :=
  HasLowerLevelTorsion S 𝔪 J₀ → exitIdeal N W p ≠ ⊤

end SupportTransfer

end ModularCurve

end
