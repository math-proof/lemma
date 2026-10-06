import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : ({x, y} : Finset ℤ) = ({0, 1} : Finset ℤ)) :
-- imply
  (x, y) = (Int.ofNat (1 - KroneckerDelta 0 x), Int.ofNat (KroneckerDelta 0 x)) := by
-- proof
  have hx : x = 0 ∨ x = 1 := by
    have : x ∈ ({x, y} : Finset ℤ) := by simp
    rw [h] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  rw [Prod.ext_iff]
  rw [Nat.Delta.eq.Ite (0 : ℤ) x]
  obtain hx0 | hx1 := hx
  · split_ifs with h0
    · constructor
      · rw [hx0]; norm_num
      · have h1 : 1 = x ∨ 1 = y := by
          have : 1 ∈ ({x, y} : Finset ℤ) := by
            rw [h]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          tauto
        obtain h1x | h1y := h1
        · omega
        · rw [←h1y]; norm_num
    · exact False.elim (h0 hx0.symm)
  · split_ifs with h0
    · omega
    · constructor
      · rw [hx1]; norm_num
      · have h0' : 0 = x ∨ 0 = y := by
          have : 0 ∈ ({x, y} : Finset ℤ) := by
            rw [h]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          tauto
        obtain h0x | h0y := h0'
        · omega
        · rw [←h0y]; norm_num


-- created on 2021-04-02
