import sympy.series.limits
import sympy.tensor.tensor
import Lemma.Tensor.HeadDataSum.eq.SumData
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.XEqDivS_Sum.of.XEq.Ge_0
open Hyperreal Tensor Vector


@[main]
private lemma main
  {x y : Tensor ℝ* [n]}
-- given
  (h_pos : x ≥ 0)
  (h_not_sum : ¬(x.data.sum → 0))
  (h : y ≈ x) :
-- imply
  let den_x : Tensor ℝ* [] := x.sum 0
  let den_y : Tensor ℝ* [] := y.sum 0
  y / den_y ≈ x / den_x := by
-- proof
  intro den_x den_y
  apply XEq.of.XEqDataS
  have h_pos_data : x.data ≥ 0 := h_pos
  have h_vec := Vector.XEqDivS_Sum.of.XEq.Ge_0 h_pos_data h_not_sum (XEqDataS.of.XEq h)
  have h_den_y : den_y = y.sum 0 := rfl
  have h_den_x : den_x = x.sum 0 := rfl
  have h_sum_scalar_y : den_y.data[0] = y.data.sum := calc
    den_y.data[0] = den_y.data.head := by
      rw [Head.eq.Get_0.fin]
      simp [GetElem.getElem]
    _ = (y.sum 0).data.head := by rw [h_den_y]
    _ = y.data.sum := HeadDataSum.eq.SumData y
  have h_sum_scalar_x : den_x.data[0] = x.data.sum := calc
    den_x.data[0] = den_x.data.head := by
      rw [Head.eq.Get_0.fin]
      simp [GetElem.getElem]
    _ = (x.sum 0).data.head := by rw [h_den_x]
    _ = x.data.sum := HeadDataSum.eq.SumData x
  have hy : (y / den_y).data = y.data / y.data.sum := by
    simp only [HDiv.hDiv]
    rw [h_sum_scalar_y]
  have hx : (x / den_x).data = x.data / x.data.sum := by
    simp only [HDiv.hDiv]
    rw [h_sum_scalar_x]
  rw [hy, hx]
  exact h_vec


-- created on 2026-07-25
