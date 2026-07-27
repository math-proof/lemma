import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqData1'1
import Lemma.Tensor.Le.is.LeDataS
import Lemma.Tensor.Le0Stack.of.All_Ge_0
import Lemma.Vector.EqGet0_0
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  (n l u : ℕ) :
-- imply
  (1 : Tensor α [n, n]).band_part l u ≥ 0 := by
-- proof
  rw [BandPart.eq.Stack_BoolIn_Icc]
  let row : Fin n → Tensor α [n] := fun i => [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u) : Bool)
  apply Le0Stack.of.All_Ge_0 (X := row)
  intro ir
  simp [row]
  apply Le0Stack.of.All_Ge_0
  intro j
  refine ge_iff_le.mpr ?_
  apply Le.of.LeDataS
  intro k
  have hzero : ((0 : Tensor α []).data)[k] = (0 : α) := by
    rw [EqData0'0]
    exact Vector.EqGet0_0.fin (α := α) k
  fin_cases k
  rw [hzero]
  by_cases hmem : (j - ir : ℤ) ∈ Icc (-l : ℤ) u
  ·
    obtain ⟨h_l, h_u⟩ := Set.mem_Icc.mp hmem
    have h1 : (↑ir : ℤ) ≤ ↑j + l := by linarith
    have h2 : (↑j : ℤ) ≤ ↑u + ↑ir := by linarith
    simp [h1, h2, EqData1'1]
    exact (zero_le_one : (0 : α) ≤ 1)
  ·
    rw [Set.mem_Icc, not_and_or] at hmem
    obtain h1 | h2 := hmem
    · have h1' : ¬(↑ir : ℤ) ≤ ↑j + l := by linarith
      rw [decide_eq_false h1', Bool.false_and, Bool.toNat_false]
      simp only [Nat.cast_zero, EqData0'0, GetElem.getElem]
      rw [← Vector.EqGet0_0.fin (α := α)]
    · have h2' : ¬(↑j : ℤ) ≤ ↑u + ↑ir := by linarith
      rw [decide_eq_false h2', Bool.and_false, Bool.toNat_false]
      simp only [Nat.cast_zero, EqData0'0, GetElem.getElem]
      rw [← Vector.EqGet0_0.fin (α := α)]


-- created on 2026-07-26
