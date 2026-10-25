import Lemma.CuspForm.HeckeAlgebra
import Def.HeckeGalois_EichlerShimura
import Def.CuspForm_HeckeEvalForms

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ)


variable {N k} in
theorem heckeFormsGen_of_dvd {q : Nat.Primes} (h : (q : ℕ) ∣ N) :
    heckeFormsGen N k q = heckeAlgebra.U q.2 h (Set.notMem_empty _) :=
  dif_pos h

variable {N k} in
theorem heckeFormsGen_of_not_dvd {ℓ : Nat.Primes} (h : ¬ (ℓ : ℕ) ∣ N) :
    heckeFormsGen N k ℓ = heckeAlgebra.T ℓ.2 h (Set.notMem_empty _) :=
  dif_neg h


theorem heckeEvalForms_heckeGen (ℓ : Nat.Primes) :
    heckeEvalForms N k (ModularCurve.heckeGen ℓ) = heckeFormsGen N k ℓ :=
  MvPolynomial.aeval_X _ ℓ

variable {N k} in
theorem heckeEvalForms_heckeGen_of_dvd {q : Nat.Primes} (h : (q : ℕ) ∣ N) :
    heckeEvalForms N k (ModularCurve.heckeGen q) = heckeAlgebra.U q.2 h (Set.notMem_empty _) := by
  rw [heckeEvalForms_heckeGen, heckeFormsGen_of_dvd h]

variable {N k} in
theorem heckeEvalForms_heckeGen_of_not_dvd {ℓ : Nat.Primes} (h : ¬ (ℓ : ℕ) ∣ N) :
    heckeEvalForms N k (ModularCurve.heckeGen ℓ) = heckeAlgebra.T ℓ.2 h (Set.notMem_empty _) := by
  rw [heckeEvalForms_heckeGen, heckeFormsGen_of_not_dvd h]

theorem heckeEvalForms_C (a : ℤ) :
    heckeEvalForms N k (MvPolynomial.C a) = algebraMap ℤ (heckeAlgebra N k ∅) a :=
  MvPolynomial.aeval_C _ a

end CuspForm

end
