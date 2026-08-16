import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.MapMatmul.eq.MatmulMapS.of.Length.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.ReshapeMap.eq.MapReshape.of.Dvd
import Lemma.Tensor.SEqMapS.of.SEq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Tensor.Tensordot.eq.Matmul.of.Length
open Bool Tensor


/-- `tensordot` commutes with a pointwise map `f`. -/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
  {s s' : List ℕ}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (h_add : ∀ a b, f (a + b) = f a + f b)
  (A : Tensor α (s ++ [m, n]))
  (C : Tensor α (s' ++ [n, k])) :
-- imply
  (A.tensordot C).map f = (A.map f).tensordot (C.map f) := by
-- proof
  if hlt : s.length < s'.length then
    apply Bool.Eq.of.SEq
    have hL := Tensordot.as.Matmul.of.LtLengthS hlt (A.map f) (C.map f)
    have hR := Tensordot.as.Matmul.of.LtLengthS hlt A C
    let sR := s'.take (s'.length - s.length) ++ s ++ [m, n]
    have hmat :=
      MapMatmul.eq.MatmulMapS.of.Length.All_Eq_Add.All_Eq_Mul h_mul h_add
        (by grind) (A.reshape sR (by grind)) C
    refine (SEqMapS.of.SEq hR f).trans ?_
    refine (Bool.SEq.of.Eq (by
      change ((A.reshape sR (by grind)).matmul C (by grind)).map f = _
      rw [hmat, ReshapeMap.eq.MapReshape.of.Dvd])).trans hL.symm
  else if hgt : s.length > s'.length then
    apply Bool.Eq.of.SEq
    have hge : s.length ≥ s'.length := Nat.le_of_lt hgt
    have hL := Tensordot.as.Matmul.of.GeLengthS hge (A.map f) (C.map f)
    have hR := Tensordot.as.Matmul.of.GeLengthS hge A C
    let sL := s.take (s.length - s'.length) ++ s' ++ [n, k]
    have hmat :=
      MapMatmul.eq.MatmulMapS.of.Length.All_Eq_Add.All_Eq_Mul h_mul h_add
        (by grind) A (C.reshape sL (by grind))
    refine (SEqMapS.of.SEq hR f).trans ?_
    exact (Bool.SEq.of.Eq (by
      change (A.matmul (C.reshape sL (by grind)) (by grind)).map f = _
      rw [hmat, ReshapeMap.eq.MapReshape.of.Dvd])).trans hL.symm
  else
    have hlen := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
    rw [Tensordot.eq.Matmul.of.Length hlen, Tensordot.eq.Matmul.of.Length hlen]
    apply MapMatmul.eq.MatmulMapS.of.Length.All_Eq_Add.All_Eq_Mul h_mul h_add hlen


-- created on 2026-08-17
