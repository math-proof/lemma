/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

namespace MetaMathlibExt

section

variable {R : Type*} [CommRing R] (a : ℕ → R)

/-- The Hessenberg–Toeplitz matrix: `a (i + 1 - j)` on and below the first
superdiagonal, `0` above it. -/
private def tH (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0

/-- The signed sum over ordered compositions of `n`. -/
private def cS (n : ℕ) : R :=
  Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
      Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r)))

/-- Forward map for `splitEquiv`: values `< iv` go left, the rest go right. -/
private def splitTo (N iv : ℕ) (r : Fin N) : Fin iv ⊕ Fin (N - iv) :=
  if hr : r.val < iv then Sum.inl ⟨r.val, hr⟩
  else Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩

/-- Backward map for `splitEquiv`. -/
private def splitInv (N iv : ℕ) (h : iv ≤ N) : Fin iv ⊕ Fin (N - iv) → Fin N :=
  Sum.elim (fun r => ⟨r.val, by have h1 := r.isLt; omega⟩)
    (fun r => ⟨r.val + iv, by have h1 := r.isLt; omega⟩)

/-- Splitting `Fin N` into values `< iv` and values `≥ iv`. -/
private def splitEquiv (N iv : ℕ) (h : iv ≤ N) : Fin N ≃ Fin iv ⊕ Fin (N - iv) where
  toFun := splitTo N iv
  invFun := splitInv N iv h
  left_inv := fun r => by
    simp only [splitTo]
    split
    · next hr =>
      have e : splitInv N iv h (Sum.inl ⟨r.val, hr⟩)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
    · next hr =>
      have e : splitInv N iv h (Sum.inr ⟨r.val - iv, by have h1 := r.isLt; omega⟩)
          = (⟨r.val - iv + iv, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e]
      ext
      dsimp only
      omega
  right_inv := fun x => by
    rcases x with r | c
    · have e1 : splitInv N iv h (Sum.inl r)
          = (⟨r.val, by have h1 := r.isLt; omega⟩ : Fin N) := rfl
      rw [e1]
      simp only [splitTo, dite_eq_left r.isLt]
    · have e2 : splitInv N iv h (Sum.inr c)
          = (⟨c.val + iv, by have h1 := c.isLt; omega⟩ : Fin N) := rfl
      rw [e2]
      simp only [splitTo, dite_eq_right (show ¬ c.val + iv < iv by omega)]
      congr 1
      ext
      dsimp only
      omega

/-- Forward map: a composition of `n + 1` gives its first block and the rest. -/
private def compConsTo (n : ℕ) (c : Composition (n + 1))
    : Σ _i : Fin (n + 1), Composition (n - _i.val) :=
  have hne : c.blocks ≠ [] := by
    intro hcon
    have hs := c.blocks_sum
    rw [hcon] at hs
    simp at hs
  have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
  have hsum : c.blocks.head hne + c.blocks.tail.sum = n + 1 := by
    have hs := c.blocks_sum
    rw [← List.cons_head_tail hne, List.sum_cons] at hs
    exact hs
  ⟨⟨c.blocks.head hne - 1, by omega⟩,
    ⟨c.blocks.tail,
      fun {i} hi => c.blocks_pos (by
        rw [← List.cons_head_tail hne]
        exact List.mem_cons_of_mem _ hi),
      by
        change c.blocks.tail.sum = n - (c.blocks.head hne - 1)
        omega⟩⟩

/-- Backward map: prepend a first block to a composition. -/
private def compConsInv (n : ℕ) (x : Σ _i : Fin (n + 1), Composition (n - _i.val))
    : Composition (n + 1) :=
  ⟨(x.1.val + 1) :: x.2.blocks,
    fun {i} hi => by
      rcases List.mem_cons.mp hi with rfl | hm
      · omega
      · exact x.2.blocks_pos hm,
    by
      have hs := x.2.blocks_sum
      have hlt := x.1.isLt
      rw [List.sum_cons]
      omega⟩

/-- A composition of `n + 1` is a first block together with a composition of
the rest. -/
private def compCons (n : ℕ) :
    Composition (n + 1) ≃ Σ _i : Fin (n + 1), Composition (n - _i.val) where
  toFun := compConsTo n
  invFun := compConsInv n
  left_inv := fun c => by
    have hne : c.blocks ≠ [] := by
      intro hcon
      have hs := c.blocks_sum
      rw [hcon] at hs
      simp at hs
    have hpos : 0 < c.blocks.head hne := c.blocks_pos (List.head_mem hne)
    apply Composition.ext
    simp only [compConsTo, compConsInv]
    rw [Nat.sub_add_cancel hpos, List.cons_head_tail hne]
  right_inv := fun x => by
    obtain ⟨i, d⟩ := x
    have h1 : (compConsTo n (compConsInv n ⟨i, d⟩)).1 = i := by
      simp only [compConsTo, compConsInv]
      exact Fin.ext (Nat.add_sub_cancel _ _)
    have h2 : (compConsTo n (compConsInv n ⟨i, d⟩)).2 ≍ d := by
      simp only [compConsTo, compConsInv]
      exact HEq.rfl
    exact Sigma.ext h1 h2
end
end MetaMathlibExt
