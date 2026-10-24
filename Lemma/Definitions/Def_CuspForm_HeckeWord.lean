import Mathlib.Algebra.FreeAlgebra
import Lemma.Definitions.Def_CuspForm_HeckeAlgebra
import Lemma.Definitions.Def_Gamma0HeckeOperatorHom

open CongruenceSubgroup

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) [DecidablePred (· ∈ S)]

noncomputable def heckeWordGenForms (n : ℕ) : Module.End ℂ (CuspForm (Gamma0 N) k) :=
  if h : n.Prime ∧ n ∉ S then
    (if hn : n ∣ N then heckeULin k hn else heckeTLin k h.1 hn)
  else 0

variable {N k S} in
theorem heckeWordGenForms_of_not_dvd {n : ℕ} (hn : n.Prime) (hnN : ¬ n ∣ N) (hnS : n ∉ S) :
    heckeWordGenForms N k S n = heckeTLin k hn hnN := by
  rw [heckeWordGenForms, dif_pos ⟨hn, hnS⟩, dif_neg hnN]

variable {N k S} in
theorem heckeWordGenForms_of_dvd {n : ℕ} (hn : n.Prime) (hnN : n ∣ N) (hnS : n ∉ S) :
    heckeWordGenForms N k S n = heckeULin k hnN := by
  rw [heckeWordGenForms, dif_pos ⟨hn, hnS⟩, dif_pos hnN]

variable {N k S} in
theorem heckeWordGenForms_of_not {n : ℕ} (h : ¬ (n.Prime ∧ n ∉ S)) : heckeWordGenForms N k S n = 0 := by
  rw [heckeWordGenForms, dif_neg h]

noncomputable def heckeWordForms : FreeAlgebra ℤ ℕ →ₐ[ℤ] Module.End ℂ (CuspForm (Gamma0 N) k) :=
  FreeAlgebra.lift ℤ (heckeWordGenForms N k S)

@[simp] theorem heckeWordForms_ι (n : ℕ) :
    heckeWordForms N k S (FreeAlgebra.ι ℤ n) = heckeWordGenForms N k S n :=
  FreeAlgebra.lift_ι_apply _ _

theorem range_heckeWordForms : (heckeWordForms N k S).range = heckeAlgebra N k S := by
  rw [heckeWordForms, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift, heckeAlgebra]
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    by_cases h : n.Prime ∧ n ∉ S
    · by_cases hn : n ∣ N
      · rw [heckeWordGenForms_of_dvd h.1 hn h.2]
        exact Algebra.subset_adjoin (heckeULin_mem_heckeGenerators h.1 hn h.2)
      · rw [heckeWordGenForms_of_not_dvd h.1 hn h.2]
        exact Algebra.subset_adjoin (heckeTLin_mem_heckeGenerators h.1 hn h.2)
    · rw [heckeWordGenForms_of_not h]
      exact Subalgebra.zero_mem _
  · refine Algebra.adjoin_mono ?_
    rintro T hT
    rcases hT with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · exact ⟨ℓ, heckeWordGenForms_of_not_dvd hℓ hℓN hℓS⟩
    · exact ⟨q, heckeWordGenForms_of_dvd hq hqN hqS⟩

theorem exists_heckeWordForms_eq (t : heckeAlgebra N k S) :
    ∃ P : FreeAlgebra ℤ ℕ, heckeWordForms N k S P = t := by
  have h : (t : Module.End ℂ (CuspForm (Gamma0 N) k)) ∈ (heckeWordForms N k S).range := by
    rw [range_heckeWordForms]
    exact t.2
  exact h

theorem heckeWordForms_mem (P : FreeAlgebra ℤ ℕ) : heckeWordForms N k S P ∈ heckeAlgebra N k S := by
  rw [← range_heckeWordForms]
  exact ⟨P, rfl⟩

end CuspForm

namespace HeckeEis

variable (N : ℕ) (A : Type*) [AddCommGroup A] (S : Set ℕ) [DecidablePred (· ∈ S)]

noncomputable def heckeWordGenHom (n : ℕ) : Module.End ℤ (Additive (Gamma0 N) →+ A) :=
  if h : n.Prime ∧ n ∉ S then
    (haveI : NeZero n := ⟨h.1.ne_zero⟩; (heckeOperatorHom N n A).toIntLinearMap)
  else 0

variable {N A S} in
theorem heckeWordGenHom_of_prime {n : ℕ} (hn : n.Prime) (hnS : n ∉ S) :
    heckeWordGenHom N A S n
      = (haveI : NeZero n := ⟨hn.ne_zero⟩; (heckeOperatorHom N n A).toIntLinearMap) := by
  rw [heckeWordGenHom, dif_pos ⟨hn, hnS⟩]

variable {N A S} in
theorem heckeWordGenHom_of_not {n : ℕ} (h : ¬ (n.Prime ∧ n ∉ S)) : heckeWordGenHom N A S n = 0 := by
  rw [heckeWordGenHom, dif_neg h]

noncomputable def heckeWordHom : FreeAlgebra ℤ ℕ →ₐ[ℤ] Module.End ℤ (Additive (Gamma0 N) →+ A) :=
  FreeAlgebra.lift ℤ (heckeWordGenHom N A S)

@[simp] theorem heckeWordHom_ι (n : ℕ) :
    heckeWordHom N A S (FreeAlgebra.ι ℤ n) = heckeWordGenHom N A S n :=
  FreeAlgebra.lift_ι_apply _ _

variable {N A S} in
theorem heckeWordHom_ι_apply_of_prime {n : ℕ} (hn : n.Prime) (hnS : n ∉ S)
    (φ : Additive (Gamma0 N) →+ A) :
    heckeWordHom N A S (FreeAlgebra.ι ℤ n) φ
      = (haveI : NeZero n := ⟨hn.ne_zero⟩; heckeOperatorHom N n A φ) := by
  rw [heckeWordHom_ι, heckeWordGenHom_of_prime hn hnS]
  rfl

end HeckeEis
