/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Def.NumberTheory.MultipleZeta.HOneBasis
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MetaMathlibExt.MultipleZeta

theorem decodeBlocks_pos (l : List Bool) : ∀ x ∈ decodeBlocks l, 0 < x := by
  induction l with
  | nil =>
    intro x hx
    simp [decodeBlocks] at hx
  | cons b rest ih =>
    cases b with
    | true =>
      intro x hx
      simp only [decodeBlocks, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ih x hx
    | false =>
      intro x hx
      simp only [decodeBlocks] at hx
      cases h : decodeBlocks rest with
      | nil => rw [h] at hx; simp [bump] at hx
      | cons k ks =>
        rw [h] at hx
        simp only [bump, List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · apply ih
          rw [h]
          exact List.mem_cons_of_mem k hx

theorem encodeNatBlocks_decodeBlocks (l : List Bool)
    (h : l = [] ∨ l.getLast? = some true) :
    encodeNatBlocks (decodeBlocks l) = l := by
  induction l with
  | nil => simp [decodeBlocks, encodeNatBlocks]
  | cons b rest ih =>
    cases b with
    | true =>
      have hr : rest = [] ∨ rest.getLast? = some true := by
        cases rest with
        | nil => exact Or.inl rfl
        | cons c cs =>
          exact Or.inr (by
            have hlast := Or.resolve_left h (by simp)
            rwa [List.getLast?_cons_cons] at hlast)
      have ihr := ih hr
      simp [decodeBlocks, encodeNatBlocks, ihr]
    | false =>
      cases rest with
      | nil => simp at h
      | cons c cs =>
        have hlast : (c :: cs).getLast? = some true := by
          have hlast := Or.resolve_left h (by simp)
          rwa [List.getLast?_cons_cons] at hlast
        have hr : (c :: cs) = [] ∨ (c :: cs).getLast? = some true :=
          Or.inr hlast
        have ihr := ih hr
        have hmem : true ∈ (c :: cs) := true_mem_of_getLast?_eq_true _ hlast
        have hne : decodeBlocks (c :: cs) ≠ [] :=
          decodeBlocks_ne_nil_of_mem_true _ hmem
        cases hd : decodeBlocks (c :: cs) with
        | nil => exact absurd hd hne
        | cons k ks =>
          have hdec : decodeBlocks (false :: c :: cs) = (k + 1) :: ks := by
            simp [decodeBlocks, hd, bump]
          rw [hdec]
          have henc : encodeNatBlocks ((k + 1) :: ks) =
              List.replicate k false ++ [true] ++ encodeNatBlocks ks := by
            simp [encodeNatBlocks]
          rw [henc]
          have hrest : (c :: cs) = encodeNatBlocks (k :: ks) := by
            rw [← hd]; exact ihr.symm
          have hkpos : 0 < k := decodeBlocks_pos (c :: cs) k (by rw [hd]; simp)
          have hrep : List.replicate k false =
              false :: List.replicate (k - 1) false := by
            cases k with
            | zero => simp at hkpos
            | succ n => simp [List.replicate_succ]
          rw [hrep]
          simp [hrest, encodeNatBlocks]

end MetaMathlibExt.MultipleZeta
end
