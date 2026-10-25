/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/HammingExpansion.lean -/


import Def.InformationTheory.HammingExpansion
import Lemma.Real.HammingExpansion


example (A : Finset (Fin 2 → Bool)) (x a : Fin 2 → Bool) (t : ℕ)
    (ha : a ∈ A) (h : hammingDist x a ≤ t) : x ∈ Hamming.expansion A t := by
  exact Hamming.mem_expansion_of_mem ha h

example (x y : Fin 2 → Bool) (t : ℕ) :
    x ∈ Hamming.expansion {y} t ↔ hammingDist x y ≤ t := by
  rw [Hamming.expansion_singleton, Hamming.mem_ball, hammingDist_comm]

example (t : ℕ) : Hamming.expansion (∅ : Finset (Fin 2 → Bool)) t = ∅ := by
  simp

example (a : Fin 2 → Bool) : Hamming.expansion {a} 0 = {a} := by
  rw [Hamming.expansion_singleton]
  ext y
  simp [Hamming.ball, eq_comm]

example (c : Fin 2 → Bool) (e : ℕ) : Hamming.IsBall (Hamming.ball c e) :=
  Hamming.isBall_ball c e

example (A : Finset (Fin 2 → Bool)) (t : ℕ) : A ⊆ Hamming.expansion A t :=
  Hamming.subset_expansion_self A t

