import Mathlib
import sympy.Basic
import sympy.Algebra.Algebra.AmitsurLevitzki

open AmitsurLevitzki

/--
[al_matrix_map_smul_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma matrix_map_smul_mul
  [CommRing R] [Semiring G] [Algebra R G]
-- given
  (A B : Matrix (Fin n) (Fin n) R) (g h : G) :
-- imply
  (A.map (fun r => r • g)) * (B.map (fun r => r • h))
    = (A * B).map (fun r => r • (g * h)) := by
-- proof
  apply al_matrix_map_smul_mul A B g h


/--
[al_map_one_smul_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma map_one_smul_one
  [CommRing R] [Ring G] [Algebra R G] [DecidableEq (Fin n)] :
-- imply
  ((1 : Matrix (Fin n) (Fin n) R).map (fun r => r • (1 : G))) = 1 := by
-- proof
  apply al_map_one_smul_one


/--
[al_sum_map_smul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma sum_map_smul_pow
  [CommRing R] [Ring G] [Algebra R G] [Fintype ι] [DecidableEq (Fin n)]
-- given
  (A : ι → Matrix (Fin n) (Fin n) R) (g : ι → G) (m : ℕ) :
-- imply
  (∑ i, (A i).map (fun r => r • g i)) ^ m
    = ∑ f : Fin m → ι, (((List.ofFn fun k => A (f k)).prod).map
      (fun r => r • (List.ofFn fun k => g (f k)).prod)) := by
-- proof
  apply al_sum_map_smul_pow A g m


/--
[al_grassmann_pow_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_pow_expansion
  [CommRing R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (m : ℕ) :
-- imply
  (∑ i, (M i).map (fun r => r •
      (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
        ExteriorAlgebra R (Fin (2 * n) → R)))) ^ m
    = ∑ f : Fin m → Fin (2 * n),
      (((List.ofFn fun k => M (f k)).prod).map
        (fun r => r • (ExteriorAlgebra.ιMulti R m)
          ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) ∘ f))) := by
-- proof
  apply al_grassmann_pow_expansion n M m


/--
[al_grassmann_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_pow_eq_zero
  [CommRing R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (m : ℕ) (hm : 2 * n < m) :
-- imply
  (∑ i, (M i).map (fun r => r •
      (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
        ExteriorAlgebra R (Fin (2 * n) → R)))) ^ m = 0 := by
-- proof
  apply al_grassmann_pow_eq_zero n M m hm


/--
[al_sign_smul_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma sign_smul_comm
  [CommRing R] [AddCommGroup V] [Module R V]
-- given
  (r : R) (ω : ExteriorAlgebra R V) (u : ℤˣ) :
-- imply
  r • ((u : ℤ) • ω) = (((u : ℤ) • r)) • ω := by
-- proof
  apply al_sign_smul_comm r ω u


/--
[al_grassmann_pow_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_pow_top
  [CommRing R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
-- imply
  (∑ i, (M i).map (fun r => r •
      (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
        ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * n)
    = ((∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod).map
        (fun r => r • (ExteriorAlgebra.ιMulti R (2 * n))
          (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)))) := by
-- proof
  apply al_grassmann_pow_top n M


/--
[al_trace_list_prod_ofFn_comp_finRotate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma trace_list_prod_ofFn_comp_finRotate
  [CommRing R]
-- given
  (m n : ℕ)
  (A : Fin m → Matrix (Fin n) (Fin n) R) :
-- imply
  ((List.ofFn (A ∘ finRotate m)).prod.trace)
    = ((List.ofFn A).prod.trace) := by
-- proof
  apply al_trace_list_prod_ofFn_comp_finRotate m n A


/--
[al_trace_map_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma trace_map_smul
  [CommRing R] [Ring G] [Algebra R G]
-- given
  (P : Matrix (Fin n) (Fin n) R) (g : G) :
-- imply
  ((P.map (fun r => r • g)).trace) = (P.trace) • g := by
-- proof
  apply al_trace_map_smul P g


/--
[al_sign_finRotate_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma sign_finRotate_even
-- given
  (k : ℕ) (hk : 1 ≤ k) :
-- imply
  (finRotate (2 * k)).sign = -1 := by
-- proof
  apply al_sign_finRotate_even k hk


/--
[al_grassmann_trace_pow_even_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_trace_pow_even_eq_zero
  [CommRing R]
-- given
  (k : ℕ)
  (h2 : IsUnit (2 : R)) (hk : 1 ≤ k)
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
-- imply
  (((∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * k))).trace = 0 := by
-- proof
  apply al_grassmann_trace_pow_even_eq_zero n M k hk h2


/--
[al_stdPoly_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma stdPoly_map
  [CommRing R] [CommRing S]
-- given
  (f : R →+* S) (m n : ℕ) (M : Fin m → Matrix (Fin n) (Fin n) R) :
-- imply
  f.mapMatrix (∑ σ : Equiv.Perm (Fin m),
    (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod)
    = ∑ σ : Equiv.Perm (Fin m),
      (σ.sign : ℤ) • (List.ofFn fun i => f.mapMatrix (M (σ i))).prod := by
-- proof
  apply al_stdPoly_map f m n M


/--
[al_io_mul_io_mem_center](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma io_mul_io_mem_center
  [CommRing R] [AddCommGroup V] [Module R V]
-- given
  (x y : V) :
-- imply
  (ExteriorAlgebra.ι R x) * (ExteriorAlgebra.ι R y)
    ∈ Subalgebra.center R (ExteriorAlgebra R V) := by
-- proof
  apply al_io_mul_io_mem_center x y


/--
[al_grassmann_top_functional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_top_functional
  [CommRing R]
-- given
  (m : ℕ) :
-- imply
  let v : Fin m → (Fin m → R) := fun i => Pi.single i 1
  let fam : (i : ℕ) → AlternatingMap R (Fin m → R) R (Fin i) :=
    Pi.single (M := fun i : ℕ => AlternatingMap R (Fin m → R) R (Fin i)) m
      (Matrix.detRowAlternating (n := Fin m))
  (ExteriorAlgebra.liftAlternating fam) ((ExteriorAlgebra.ιMulti R m) v) = 1 := by
-- proof
  apply al_grassmann_top_functional m


/--
[al_imulti_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma imulti_two
  [CommRing R] [AddCommGroup V] [Module R V]
-- given
  (w : Fin 2 → V) :
-- imply
  (ExteriorAlgebra.ιMulti R 2) w
    = (ExteriorAlgebra.ι R (w 0)) * (ExteriorAlgebra.ι R (w 1)) := by
-- proof
  apply al_imulti_two w


/--
[al_Xsq_entry_mem_center](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma Xsq_entry_mem_center
  [CommRing R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
-- imply
  (((∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ 2) a b
    ∈ Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) := by
-- proof
  apply al_Xsq_entry_mem_center n M a b


/--
[al_grassmann_sq_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma grassmann_sq_matrix
  [CommRing R]
-- given
  (hR : ∀ k : ℕ, 0 < k → IsUnit (k : R))
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
-- imply
  ∃ Y : Matrix (Fin n) (Fin n) (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))),
    (∀ k : ℕ, ((Y ^ k).map (Subtype.val :
      (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) →
        (ExteriorAlgebra R (Fin (2 * n) → R))))
      = (∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i)
            :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * k))
    ∧ (∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0)
    ∧ (Y ^ (n + 1) = 0)
    ∧ (∀ k : ℕ, 0 < k → IsUnit (k :
      (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))))) := by
-- proof
  apply al_grassmann_sq_matrix n M hR


/--
[al_derivative_det_eq_sum_det_updateRow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma derivative_det_eq_sum_det_updateRow
  [CommRing C] [Fintype ι] [DecidableEq ι]
-- given
  (A : Matrix ι ι (Polynomial C)) :
-- imply
  Polynomial.derivative (Matrix.det A)
    = ∑ i, Matrix.det (Matrix.updateRow A i (fun j => Polynomial.derivative (A i j))) := by
-- proof
  apply al_derivative_det_eq_sum_det_updateRow A


/--
[al_derivative_charpoly_eq_trace_adjugate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma derivative_charpoly_eq_trace_adjugate
  [CommRing C] [Fintype m] [DecidableEq m]
-- given
  (Y : Matrix m m C) :
-- imply
  Polynomial.derivative (Y.charpoly)
    = ((Matrix.adjugate (Matrix.charmatrix Y)).trace) := by
-- proof
  apply al_derivative_charpoly_eq_trace_adjugate Y


/--
[al_scalar_eq_smul_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma scalar_eq_smul_one
  [CommRing R] [Fintype nn] [DecidableEq nn]
-- given
  (c : R) :
-- imply
  (Matrix.scalar nn) c = c • (1 : Matrix nn nn R) := by
-- proof
  apply al_scalar_eq_smul_one c


/--
[al_X_mul_derivative_charpoly_of_nilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma X_mul_derivative_charpoly_of_nilpotent
  [CommRing C]
-- given
  (n : ℕ)
  (Y : Matrix (Fin n) (Fin n) C)
  (hnil : Y ^ (n + 1) = 0)
  (htr : ∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0) :
-- imply
  Polynomial.X * Polynomial.derivative (Y.charpoly)
    = ((n : Polynomial C)) * Y.charpoly := by
-- proof
  apply al_X_mul_derivative_charpoly_of_nilpotent n Y hnil htr


/--
[al_pow_eq_zero_of_trace_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma pow_eq_zero_of_trace_pow_eq_zero
  [CommRing C]
-- given
  (n : ℕ)
  (Y : Matrix (Fin n) (Fin n) C)
  (hC : ∀ k : ℕ, 0 < k → IsUnit (k : C))
  (hnil : Y ^ (n + 1) = 0)
  (htr : ∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0) :
-- imply
  Y.charpoly = Polynomial.X ^ n ∧ Y ^ n = 0 := by
-- proof
  apply al_pow_eq_zero_of_trace_pow_eq_zero n Y hC hnil htr


/--
[al_top_smul_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma top_smul_cancel
  [CommRing R]
-- given
  (m : ℕ) (r : R)
  (h : r • (ExteriorAlgebra.ιMulti R m)
    (fun j : Fin m => (Pi.single j (1 : R) : Fin m → R)) = 0) :
-- imply
  r = 0 := by
-- proof
  apply al_top_smul_cancel m r h


/--
[al_amitsur_levitzki_of_algebra_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma amitsur_levitzki_of_algebra_rat
  [CommRing R] [Algebra ℚ R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
-- imply
  (∑ σ : Equiv.Perm (Fin (2 * n)),
    (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod) = 0 := by
-- proof
  apply al_amitsur_levitzki_of_algebra_rat n M


/--
[amitsur_levitzki](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/AmitsurLevitzki.lean)
-/
@[path]
private lemma amitsur
  [CommRing R]
-- given
  (n : ℕ)
  (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
-- imply
  ∑ σ : Equiv.Perm (Fin (2 * n)),
    (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod = 0 := by
-- proof
  apply amitsur_levitzki n M


-- created on 2026-10-09
