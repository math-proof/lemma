import sympy.tensor.tensor
import Lemma.Algebra.LengthJoin.eq.SumMap_FunLength
import Lemma.Algebra.ProdCons.eq.Mul_Prod
import Lemma.Algebra.Mul
import Lemma.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  {s : List (Tensor α shape)}
-- given
  (h : s.length ≠ 0) :
-- imply
  let head_dimension := shape.headD 1 * s.length
  let tail_dimension := s[0].shape.tail
  (head_dimension :: tail_dimension).prod = ((s.map fun t => t.data.val).flatten).length := by
-- proof
  intro head_dimension tail_dimension
  let data := (s.map fun t => t.data.val).flatten
  have h : data.length = ((s.map fun t => t.data.val).map fun t => t.length).sum :=
    LengthJoin.eq.SumMap_FunLength
  have h_eq_prod := ProdCons.eq.Mul_Prod head_dimension tail_dimension
  rw [h, h_eq_prod]
  simp
  have h_Eq_Fun : ((fun t => t.length) ∘ fun t : Tensor α shape => t.data.val) = fun t => t.data.val.length := by
    congr
  simp [h_Eq_Fun]
  simp [head_dimension]
  rw [Mul.comm (b := s.length)]
  rw [MulMul.eq.Mul_Mul]
  have h_tail_dimension : tail_dimension = shape.tail := by
    simp [tail_dimension]
    simp [Tensor.shape]
  have h_Eq : shape.head?.getD 1 * tail_dimension.prod = shape.prod := by
    rw [h_tail_dimension]
    cases shape <;> simp_all
  rw [h_Eq]


-- created on 2024-07-01
-- updated on 2025-05-31
