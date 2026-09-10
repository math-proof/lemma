import Lemma.Tensor.AppendHstackS.eq.Eye
import Lemma.Tensor.AppendHstackS.eq.SwapMatrix
import Lemma.Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS
import Lemma.Tensor.EqDot0_0
import Lemma.Tensor.EqDot_0'0
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.MatProd.eq.DotMatProd
open Tensor
set_option maxHeartbeats 2000000


@[main]
private lemma main
  [Semiring α] [CharZero α]
  {n m : ℕ}
-- given
  (hm : m ≤ n)
  (b : Fin m → Fin n) :
-- imply
  (Tensor.matProd m (fun i => SwapMatrix n i (b i))).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1) =
    Tensor.matProd m (fun i => SwapMatrix (n + 1) i (b i)) := by
-- proof
  induction m with
  | zero =>
    simp only [matProd]
    apply AppendHstackS.eq.Eye
  | succ m ih =>
    let b' : Fin m → Fin n := fun i => b i.castSucc
    let P : Tensor α [n, n] := Tensor.matProd m (fun i => SwapMatrix n i (b' i))
    let W : Tensor α [n, n] := SwapMatrix n m (b (Fin.last m))
    let P' : Tensor α [n + 1, n + 1] := Tensor.matProd m (fun i => SwapMatrix (n + 1) i (b' i))
    let W' : Tensor α [n + 1, n + 1] := SwapMatrix (n + 1) m (b (Fin.last m))
    have hL : Tensor.matProd (m + 1) (fun i => SwapMatrix n i (b i)) = P @ W := by
      rw [MatProd.eq.DotMatProd]
      dsimp only [P, W, b']
      congr 1
    have hR : Tensor.matProd (m + 1) (fun i => SwapMatrix (n + 1) i (b i)) = P' @ W' := by
      rw [MatProd.eq.DotMatProd]
      dsimp only [P', W', b']
      congr 1
    rw [hL, hR]
    change
      (id (α := Tensor α [n, n]) (P @ W)).hstack (0 : Tensor α [n, 1])
          ++ (0 : Tensor α [1, n]).hstack (eye 1) =
        id (α := Tensor α [n + 1, n + 1]) (P' @ W')
    have hP0 : id (α := Tensor α [n, 1]) (P @ (0 : Tensor α [n, 1])) = 0 := EqDot_0'0 P
    have h00n : id (α := Tensor α [n, n]) ((0 : Tensor α [n, 1]) @ (0 : Tensor α [1, n])) = 0 := by
      simp [id, EqDot0_0]
    have h0I : id (α := Tensor α [n, 1]) ((0 : Tensor α [n, 1]) @ (eye (α := α) 1)) = 0 := by
      simp [id, EqDot0_0]
    have h0W : id (α := Tensor α [1, n]) ((0 : Tensor α [1, n]) @ W) = 0 := by
      simp [id, EqDot0_0]
    have hI0 : id (α := Tensor α [1, n]) ((eye (α := α) 1) @ (0 : Tensor α [1, n])) = 0 :=
      EqDot_0'0 (eye (α := α) 1)
    have h00_1 : id (α := Tensor α [1, 1]) ((0 : Tensor α [1, n]) @ (0 : Tensor α [n, 1])) = 0 := by
      simp [id, EqDot0_0]
    have hII : id (α := Tensor α [1, 1]) ((eye (α := α) 1) @ (eye (α := α) 1)) = eye 1 := by
      simp [id, EqDotEye]
    have hblock :
        (P.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1))
            @ (W.hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (eye 1)) =
          (id (α := Tensor α [n, n]) (P @ W)).hstack (0 : Tensor α [n, 1])
            ++ (0 : Tensor α [1, n]).hstack (eye 1) := by
      rw [DotAppendSHstackS.eq.AppendHstackSAddSDotS, hP0, h00n, h0I, h0W, hI0, h00_1, hII]
      simp [zero_add, add_zero]
      rfl
    rw [← hblock]
    congr 1
    ·
      dsimp only [P, P', b']
      apply ih (Nat.le_of_succ_le hm)
    ·
      dsimp only [W, W']
      apply AppendHstackS.eq.SwapMatrix (i := ⟨m, Nat.lt_of_succ_le hm⟩) (j := b (Fin.last m))


-- created on 2020-08-31
-- updated on 2026-09-09
