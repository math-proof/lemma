/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/KernelsLemma.lean -/


import Lemma.Matrix.KernelsLemma
open Polynomial
open scoped BigOperators

open MathlibExt.LinearAlgebra.KernelsLemmaWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


-- An idempotent endomorphism's zero and one eigenspaces span the whole module.
example (f : Module.End K V) (hf : f * f = f) :
    LinearMap.ker f ⊔ LinearMap.ker (f - 1) = ⊤ := by
  let p : Fin 2 → K[X] := ![X, X - 1]
  have hc : IsCoprime (X : K[X]) (X - 1) := by
    simpa using (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (a := (0 : K)) (b := 1) (by simp))
  have hcop : Pairwise fun i j => IsCoprime (p i) (p j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp at hij
    · simpa [p] using hc
    · simpa [p] using hc.symm
    · simp at hij
  have hsup := (iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop).2
  have hsup_top : (⨆ i, LinearMap.ker (aeval f (p i))) = ⊤ := by
    simpa [p, Fin.prod_univ_two, mul_sub, hf] using hsup
  rw [← hsup_top]
  apply le_antisymm
  · apply sup_le
    · simpa [p] using
        (le_iSup (fun i => LinearMap.ker (aeval f (p i))) (0 : Fin 2))
    · simpa [p] using
        (le_iSup (fun i => LinearMap.ker (aeval f (p i))) (1 : Fin 2))
  · refine iSup_le fun i => ?_
    fin_cases i
    · simp [p]
    · simp [p]

-- The same family makes the zero and one eigenspaces of any endomorphism disjoint.
example (f : Module.End K V) :
    Disjoint (LinearMap.ker f) (LinearMap.ker (f - 1)) := by
  let p : Fin 2 → K[X] := ![X, X - 1]
  have hc : IsCoprime (X : K[X]) (X - 1) := by
    simpa using (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (a := (0 : K)) (b := 1) (by simp))
  have hcop : Pairwise fun i j => IsCoprime (p i) (p j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp at hij
    · simpa [p] using hc
    · simpa [p] using hc.symm
    · simp at hij
  have hindep := (iSupIndep_ker_aeval_and_iSup_eq_of_pairwise_isCoprime f p hcop).1
  have hdisjoint :
      Disjoint (LinearMap.ker (aeval f (p 0))) (LinearMap.ker (aeval f (p 1))) :=
    hindep.pairwiseDisjoint (by decide)
  simpa [p] using hdisjoint

-- A finite slice of an infinite coprime family gives the three-factor kernel decomposition.
example [CharZero K] (f : Module.End K V) :
    LinearMap.ker f ⊔ LinearMap.ker (f - 1) ⊔ LinearMap.ker (f - 2) =
      LinearMap.ker (f * (f - 1) * (f - 2)) := by
  let p : ℕ → K[X] := fun n => X - C (n : K)
  have hcop : Pairwise fun i j => IsCoprime (p i) (p j) := by
    simpa [p] using
      (Polynomial.pairwise_coprime_X_sub_C
        (K := K) (Nat.cast_injective : Function.Injective fun n : ℕ => (n : K)))
  have h := iSup_ker_aeval_eq_ker_aeval_prod_of_pairwise_isCoprime
    f p hcop (Finset.range 3)
  rw [show Finset.range 3 = {0, 1, 2} by decide] at h
  rw [Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton] at h
  simpa [p, sup_assoc, mul_assoc, map_ofNat] using h

-- One kernel is disjoint from the sum of the other two kernels in the finite slice.
example [CharZero K] (f : Module.End K V) :
    Disjoint (LinearMap.ker (f - 1))
      (LinearMap.ker f ⊔ LinearMap.ker (f - 2)) := by
  let p : ℕ → K[X] := fun n => X - C (n : K)
  have hcop : Pairwise fun i j => IsCoprime (p i) (p j) := by
    simpa [p] using
      (Polynomial.pairwise_coprime_X_sub_C
        (K := K) (Nat.cast_injective : Function.Injective fun n : ℕ => (n : K)))
  have hindep := supIndep_ker_aeval_of_pairwise_isCoprime
    f p hcop (Finset.range 3)
  have hdisjoint := hindep (t := {0, 2}) (by decide) (i := 1) (by decide) (by decide)
  simpa [p] using hdisjoint

