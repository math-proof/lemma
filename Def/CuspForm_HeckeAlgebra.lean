module
public import Theorem.ModularForm.HeckeOperatorForms
public import Theorems.Thm_CuspForm_heckeTLin_comm
public import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
public import Theorems.Thm_CuspForm_heckeULin_comm
set_option autoImplicit false


public section

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)

def heckeGenerators : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T = heckeTLin k hℓ hℓN} ∪
    {U | ∃ (q : ℕ) (hqN : q ∣ N), q.Prime ∧ q ∉ S ∧ U = heckeULin k hqN}

def heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  Algebra.adjoin ℤ (heckeGenerators N k S)

variable {N k S}

variable (N k S)

variable {N k S}

def heckeAlgebra.T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) : heckeAlgebra N k S :=
  ⟨heckeTLin k hℓ hℓN, heckeTLin_mem_heckeAlgebra hℓ hℓN hℓS⟩

def heckeAlgebra.U {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) : heckeAlgebra N k S :=
  ⟨heckeULin k hqN, heckeULin_mem_heckeAlgebra hq hqN hqS⟩

end CuspForm

end
