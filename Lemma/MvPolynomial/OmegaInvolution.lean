import Mathlib
import sympy.Basic
import sympy.combinatorics.symmetric.OmegaInvolution
import Lemma.MvPolynomial.SymmetricDefinitions
open MvPolynomial hiding R
open Finset
open SymmetricFunctions
open scoped BigOperators


section
-- ac-theorems


open MvPolynomial Finset BigOperators AlgebraicCombinatorics.SymmetricPolynomials

namespace SymmetricFunctions

@[simp]
lemma hsymmAlgHom_X {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    (hsymmAlgHom σ R n (X i)).val = hsymm σ R (i + 1) := by
  simp [hsymmAlgHom]

lemma hsymmAlgHom_apply {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) :
    (hsymmAlgHom σ R n p).val = aeval (fun i : Fin n ↦ hsymm σ R (i + 1)) p :=
  (Subalgebra.mvPolynomial_aeval_coe _ _ _).symm

/-- The ω-involution maps 1 to 1. -/
lemma omegaInvolution_one {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    omegaInvolution (R := R) hn 1 = 1 := by
  simp [omegaInvolution]

/-- The ω-involution preserves addition. -/
lemma omegaInvolution_add {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (p q : symmetricSubalgebra σ R) :
    omegaInvolution hn (p + q) = omegaInvolution hn p + omegaInvolution hn q :=
  map_add _ _ _

/-- The ω-involution preserves multiplication. -/
lemma omegaInvolution_mul {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (p q : symmetricSubalgebra σ R) :
    omegaInvolution hn (p * q) = omegaInvolution hn p * omegaInvolution hn q :=
  map_mul _ _ _

/-- The ω-involution commutes with scalar multiplication. -/
lemma omegaInvolution_smul {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (r : R) (p : symmetricSubalgebra σ R) :
    omegaInvolution hn (r • p) = r • omegaInvolution hn p :=
  map_smul _ _ _

/-- Recurrence for h_n from Newton-Girard: h_n = ∑_{j=1}^n (-1)^{j+1} e_j h_{n-j} for n > 0.

This follows from isolating the j=0 term in `newtonGirard_eh_general`:
∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
⟹ e_0 h_n + ∑_{j=1}^n (-1)^j e_j h_{n-j} = 0  (since e_0 = 1)
⟹ h_n = -∑_{j=1}^n (-1)^j e_j h_{n-j} = ∑_{j=1}^n (-1)^{j+1} e_j h_{n-j} -/
lemma hsymm_recurrence_eh {σ : Type*} [Fintype σ] [DecidableEq σ]
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    hsymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * 
      esymm σ R j * hsymm σ R (n - j) := by
  -- From Newton-Girard: ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
  have ng := newtonGirard_eh_general (σ := σ) (R := R) n hn
  -- Split off the j=0 term: h_n + ∑_{j>0} ... = 0
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_range.mpr (Nat.succ_pos n))] at ng
  simp only [pow_zero, one_mul, esymm_zero, Nat.sub_zero] at ng
  -- ng: ∑_{j>0} (-1)^j e_j h_{n-j} + h_n = 0, so ∑_{j>0} ... = -h_n
  -- Rearrange: h_n = -∑_{j>0} (-1)^j e_j h_{n-j}
  have h1 : hsymm σ R n = -∑ j ∈ Finset.range (n + 1) \ {0}, 
      (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j) := by
    have h := add_eq_zero_iff_eq_neg.mp ng
    rw [h, neg_neg]
  rw [h1]
  -- range(n+1) \ {0} = Ico 1 (n+1)
  have h2 : Finset.range (n + 1) \ {0} = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [h2]
  -- -∑ (-1)^j = ∑ (-1)^{j+1}
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Recurrence for e_n from symmetric Newton-Girard: e_n = ∑_{j=1}^n (-1)^{j+1} h_j e_{n-j} for n > 0.

This follows from isolating the j=0 term in `newtonGirard_he`:
∑_{j=0}^n (-1)^j h_j e_{n-j} = 0
⟹ h_0 e_n + ∑_{j=1}^n (-1)^j h_j e_{n-j} = 0  (since h_0 = 1)
⟹ e_n = -∑_{j=1}^n (-1)^j h_j e_{n-j} = ∑_{j=1}^n (-1)^{j+1} h_j e_{n-j} -/
lemma esymm_recurrence_he {σ : Type*} [Fintype σ] [DecidableEq σ]
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    esymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * 
      hsymm σ R j * esymm σ R (n - j) := by
  -- From symmetric Newton-Girard: ∑_{j=0}^n (-1)^j h_j e_{n-j} = 0
  have ng := newtonGirard_he (σ := σ) (R := R) n hn
  -- Split off the j=0 term
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_range.mpr (Nat.succ_pos n))] at ng
  simp only [pow_zero, one_mul, hsymm_zero, Nat.sub_zero] at ng
  -- ng: ∑_{j>0} (-1)^j h_j e_{n-j} + e_n = 0
  -- Rearrange: e_n = -∑_{j>0} (-1)^j h_j e_{n-j}
  have h1 : esymm σ R n = -∑ j ∈ Finset.range (n + 1) \ {0}, 
      (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (n - j) := by
    have h := add_eq_zero_iff_eq_neg.mp ng
    rw [h, neg_neg]
  rw [h1]
  -- range(n+1) \ {0} = Ico 1 (n+1)
  have h2 : Finset.range (n + 1) \ {0} = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [h2]
  -- -∑ (-1)^j = ∑ (-1)^{j+1}
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring


/-- The ω-involution applied to a determinant of h-entries gives a determinant of e-entries.
    
    This is a key step in the proof of the second Jacobi-Trudi formula:
    ω(det(h_{λᵢ - μⱼ - i + j})) = det(e_{λᵢ - μⱼ - i + j})
    
    Note: This requires showing that ω commutes with taking determinants,
    which follows from ω being an algebra homomorphism. -/
lemma omegaInvolution_det_hsymm {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n m : ℕ} (hn : Fintype.card σ = n)
    (M : Matrix (Fin m) (Fin m) (symmetricSubalgebra σ R)) :
    omegaInvolution hn M.det = (M.map (omegaInvolution hn)).det :=
  AlgHom.map_det (omegaInvolution hn) M

end SymmetricFunctions
end


/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_rename_esymm_eq
  [Fintype σ]
  [Fintype τ]
  [DecidableEq σ]
  [DecidableEq τ]
-- given
  (e : σ ≃ τ)
  (R : Type*)
  [CommRing R]
  (k : ℕ) :
-- imply
  rename e (esymm σ R k) = esymm τ R k := by
-- proof
  apply SymmetricFunctions.rename_esymm_eq e R k

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_rename_hsymm_eq
  [Fintype σ]
  [Fintype τ]
  [DecidableEq σ]
  [DecidableEq τ]
-- given
  (e : σ ≃ τ)
  (R : Type*)
  [CommRing R]
  (k : ℕ) :
-- imply
  rename e (hsymm σ R k) = hsymm τ R k := by
-- proof
  apply SymmetricFunctions.rename_hsymm_eq e R k

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_newtonGirard_eh_general
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  ∑ j ∈ range (n + 1), (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j) = 0 := by
-- proof
  apply SymmetricFunctions.newtonGirard_eh_general n hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_symmetricSubalgebra_sum_val_nat
  [CommRing R]
-- given
  (s : Finset ℕ)
  (f : ℕ → symmetricSubalgebra σ R) :
-- imply
  (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
-- proof
  apply SymmetricFunctions.symmetricSubalgebra_sum_val_nat s f

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_hsymmAlgHom_X
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (hsymmAlgHom σ R n (X i)).val = hsymm σ R (i + 1) := by
-- proof
  apply SymmetricFunctions.hsymmAlgHom_X i

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_hsymmAlgHom_apply
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (p : MvPolynomial (Fin n) R) :
-- imply
  (hsymmAlgHom σ R n p).val = aeval (fun i : Fin n ↦ hsymm σ R (i + 1)) p := by
-- proof
  apply SymmetricFunctions.hsymmAlgHom_apply p

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_esymm_succ
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (k : ℕ)
  (hn : Fintype.card σ = n)
  (hk : k < n) :
-- imply
  (omegaInvolution hn ⟨esymm σ R (k + 1), esymm_isSymmetric σ R (k + 1)⟩ : symmetricSubalgebra σ R).val = hsymm σ R (k + 1) := by
-- proof
  apply SymmetricFunctions.omegaInvolution_esymm_succ hn k hk

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_one
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n) :
-- imply
  omegaInvolution (R := R) hn 1 = 1 := by
-- proof
  apply SymmetricFunctions.omegaInvolution_one hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_add
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n)
  (p q : symmetricSubalgebra σ R) :
-- imply
  omegaInvolution hn (p + q) = omegaInvolution hn p + omegaInvolution hn q := by
-- proof
  apply SymmetricFunctions.omegaInvolution_add hn p q

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_mul
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n)
  (p q : symmetricSubalgebra σ R) :
-- imply
  omegaInvolution hn (p * q) = omegaInvolution hn p * omegaInvolution hn q := by
-- proof
  apply SymmetricFunctions.omegaInvolution_mul hn p q

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_smul
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n)
  (r : R)
  (p : symmetricSubalgebra σ R) :
-- imply
  omegaInvolution hn (r • p) = r • omegaInvolution hn p := by
-- proof
  apply SymmetricFunctions.omegaInvolution_smul hn r p

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_newtonGirard_he
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  ∑ j ∈ Finset.range (n + 1), (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (n - j) = 0 := by
-- proof
  apply SymmetricFunctions.newtonGirard_he n hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_hsymm_recurrence_eh
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  hsymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * esymm σ R j * hsymm σ R (n - j) := by
-- proof
  apply SymmetricFunctions.hsymm_recurrence_eh n hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_esymm_recurrence_he
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  esymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * hsymm σ R j * esymm σ R (n - j) := by
-- proof
  apply SymmetricFunctions.esymm_recurrence_he n hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_hsymm_succ
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (k : ℕ)
  (hn : Fintype.card σ = n)
  (hk : k < n) :
-- imply
  (omegaInvolution hn ⟨hsymm σ R (k + 1), hsymm_isSymmetric σ R (k + 1)⟩ : symmetricSubalgebra σ R).val = esymm σ R (k + 1) := by
-- proof
  apply SymmetricFunctions.omegaInvolution_hsymm_succ hn k hk

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_involutive
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n) :
-- imply
  (omegaInvolution hn).comp (omegaInvolution hn) = AlgHom.id R _ := by
-- proof
  apply SymmetricFunctions.omegaInvolution_involutive hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_bijective
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n : ℕ}
-- given
  (hn : Fintype.card σ = n) :
-- imply
  Function.Bijective (omegaInvolution (R := R) hn) := by
-- proof
  apply SymmetricFunctions.omegaInvolution_bijective hn

/--
[OmegaInvolution](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/OmegaInvolution.lean)
-/
@[path]
private lemma om_omegaInvolution_det_hsymm
  [Fintype σ]
  [DecidableEq σ]
  [CommRing R]
  {n m : ℕ}
-- given
  (hn : Fintype.card σ = n)
  (M : Matrix (Fin m) (Fin m) (symmetricSubalgebra σ R)) :
-- imply
  omegaInvolution hn M.det = (M.map (omegaInvolution hn)).det := by
-- proof
  apply SymmetricFunctions.omegaInvolution_det_hsymm hn M


-- created on 2026-10-23
