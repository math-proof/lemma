import Mathlib
import Instance.CuspForm_HeckeAlgebra
import Def.ModularCurve_MazurPrincipleCore
import Instance.FLTPrelim_Modularity

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
