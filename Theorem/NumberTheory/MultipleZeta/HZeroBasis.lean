/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Def.NumberTheory.MultipleZeta.HZeroBasis
/-!
# Multiple-zeta word bases

This file records the two substantial basis constructions left after the
proved word-subalgebra interface in
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

theorem decAux_pos (L : List Bool) :
    ∀ (n x : Nat), x ∈ decAux L n → 0 < x := by
  induction L with
  | nil =>
    intro n x hx
    simp only [decAux] at hx
    by_cases hn : n = 0
    · simp [hn] at hx
    · simp [hn] at hx
      omega
  | cons b t ih =>
    intro n x hx
    cases b with
    | false =>
      simp only [decAux] at hx
      exact ih (n + 1) x hx
    | true =>
      simp only [decAux, List.mem_cons] at hx
      rcases hx with h | hx
      · omega
      · exact ih 0 x hx

theorem rep_append_cons (n : Nat) (X : List Bool) :
    List.replicate n false ++ (false :: X)
      = false :: (List.replicate n false ++ X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, ih]

theorem encList_decAux_append_true (L' : List Bool) (n : Nat) :
    encList (decAux (L' ++ [true]) n) = List.replicate n false ++ (L' ++ [true]) := by
  induction L' generalizing n with
  | nil =>
    simp only [List.nil_append]
    have e1 : decAux ([true] : List Bool) n = [n + 1] := rfl
    rw [e1]
    have e2 : encList [n + 1] = encBlock (n + 1) := by simp [encList]
    rw [e2]
    simp [encBlock]
  | cons b t ih =>
    cases b with
    | false =>
      have e1 : ((false :: t) ++ [true]) = false :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (false :: (t ++ [true])) n = decAux (t ++ [true]) (n + 1) := rfl
      rw [e2, ih, List.replicate_succ, List.cons_append, rep_append_cons]
    | true =>
      have e1 : ((true :: t) ++ [true]) = true :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (true :: (t ++ [true])) n
          = (n + 1) :: decAux (t ++ [true]) 0 := rfl
      rw [e2]
      have e3 : encList ((n + 1) :: decAux (t ++ [true]) 0)
          = encBlock (n + 1) ++ encList (decAux (t ++ [true]) 0) := rfl
      rw [e3, ih]
      simp [encBlock, List.append_assoc]

theorem decAux_append_true_head (M' : List Bool) (n : Nat) :
    ∃ j rest, decAux (M' ++ [true]) n = (n + 1 + j) :: rest := by
  induction M' generalizing n with
  | nil =>
    exact ⟨0, decAux [] 0, rfl⟩
  | cons b t ih =>
    cases b with
    | false =>
      have e1 : ((false :: t) ++ [true]) = false :: (t ++ [true]) := rfl
      rw [e1]
      have e2 : decAux (false :: (t ++ [true])) n = decAux (t ++ [true]) (n + 1) := rfl
      rw [e2]
      obtain ⟨j, rest, hj⟩ := ih (n + 1)
      refine ⟨j + 1, rest, ?_⟩
      rw [hj]
      congr 1
      omega
    | true =>
      exact ⟨0, decAux (t ++ [true]) 0, rfl⟩

theorem toList_zWordPNat (l : List PNat) :
    FreeMonoid.toList (zWordPNat l) = encList (l.map PNat.val) := by
  induction l with
  | nil => simp [zWordPNat, encList]
  | cons k ks ih =>
    have e : zWordPNat (k :: ks) = hoffmanBlock k * zWordPNat ks := rfl
    rw [e, FreeMonoid.toList_mul, toList_hoffmanBlock, ih]
    simp [encList, encBlock]

theorem toList_zWord (idx : Index) :
    FreeMonoid.toList (zWord idx) = encList idx.entries := by
  have e : zWord idx = zWordPNat idx.pnatEntries := rfl
  rw [e, toList_zWordPNat, pnatEntries_val]

theorem zWord_injective : Function.Injective zWord := by
  intro a b hab
  have h := congrArg FreeMonoid.toList hab
  rw [toList_zWord, toList_zWord] at h
  have he := encList_inj a.entries (entries_pos a) b.entries (entries_pos b) h
  exact entries_injective he

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
end
