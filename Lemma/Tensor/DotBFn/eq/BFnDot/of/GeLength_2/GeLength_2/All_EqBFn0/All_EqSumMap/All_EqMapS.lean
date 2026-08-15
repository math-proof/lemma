import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.ReshapeBFn.eq.BFnReshape.of.Dvd
import Lemma.Tensor.ResizeBFn.eq.BFnResize
import Lemma.Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Tensor.Tensordot.eq.Matmul.of.Length
open Bool List Tensor
set_option maxHeartbeats 1000000


/-- `dot` commutes with a pointwise scalar binary operator `f` when both ranks are ≥ 2. -/
@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A.map (f · B.data[0])) @ C = (A @ C).map (f · B.data[0]) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  if hb : s.take (s.length - 2) = s'.take (s'.length - 2) then
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
    have hEf := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (F A) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let batch' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let K := n ⊔ n'
    let X0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Af0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (F A)
    have hAf0 : Af0 = F X0 :=
      Cast_MapBFn.eq.MapCast.of.Eq (f := f)
        (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let X : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
    let Af : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (Af0.resize ⟨batch.length + 1, by grind⟩ K)
    have hAf : Af = F X := by
      simp only [Af, X, hAf0]
      rw [ResizeBFn.eq.BFnResize h0 X0 B ⟨batch.length + 1, by grind⟩ K]
      exact Cast_MapBFn.eq.MapCast.of.Eq (f := f) (by simp) _ B
    let Y0 : Tensor α (batch' ++ [n', k]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch' ++ [K, k]) :=
      cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
    have hbY : batch' ++ [K, k] = batch ++ [K, k] := by
      simp only [batch, batch']; rw [hb]
    let Y : Tensor α (batch ++ [K, k]) :=
      cast (congrArg (Tensor α) hbY) Y'
    have hY : Y' ≃ Y := (Bool.SEqCast.of.Eq hbY Y').symm
    have htd : Af.tensordot Y = F (X.tensordot Y) := by
      rw [hAf]
      rw [Tensordot.eq.Matmul.of.Length (by rfl) (F X) Y]
      rw [Tensordot.eq.Matmul.of.Length (by rfl) X Y]
      exact MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS (f := f) h_mul h_sum h0 (by rfl) X Y B
    have htd' : Af.tensordot Y' = F (X.tensordot Y') := by
      apply Bool.Eq.of.SEq
      have h1 :=
        SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : Af ≃ Af) hY
      have h2 :=
        SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : X ≃ X) hY
      exact h1.trans (Bool.SEq.of.Eq htd) |>.trans (Bool.SEqUFnS.of.SEq h2.symm (F ·))
    have hL : (F A).einsum C ≃ Af.tensordot Y' := by
      refine hEf.trans ?_
      simp only [Af, Af0, Y', Y0, batch, batch', m, n, n', k, K, F]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y' := by
      refine hE.trans ?_
      simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    exact hL.trans (Bool.SEq.of.Eq htd') |>.trans (Bool.SEqUFnS.of.SEq hR (F ·)).symm
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
    have hEf := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (F A) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let batch' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let K := n ⊔ n'
    let X0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Af0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (F A)
    have hAf0 : Af0 = F X0 :=
      Cast_MapBFn.eq.MapCast.of.Eq (f := f)
        (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let X : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
    let Af : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (Af0.resize ⟨batch.length + 1, by grind⟩ K)
    have hAf : Af = F X := by
      simp only [Af, X, hAf0]
      rw [ResizeBFn.eq.BFnResize h0 X0 B ⟨batch.length + 1, by grind⟩ K]
      exact Cast_MapBFn.eq.MapCast.of.Eq (f := f) (by simp) _ B
    let Y0 : Tensor α (batch' ++ [n', k]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch' ++ [K, k]) :=
      cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
    have htd : Af.tensordot Y' = F (X.tensordot Y') := by
      rw [hAf]
      if hlt : batch.length < batch'.length then
        have hL := Tensordot.as.Matmul.of.LtLengthS hlt (F X) Y'
        have hR := Tensordot.as.Matmul.of.LtLengthS hlt X Y'
        let sR := batch'.take (batch'.length - batch.length) ++ batch ++ [m, K]
        have hmat := MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS (f := f) h_mul h_sum h0 (by grind) (X.reshape sR (by grind)) Y' B
        apply Bool.Eq.of.SEq
        refine hL.trans ?_
        convert (Bool.SEq.of.Eq (by
          change ((F X).reshape sR (by grind)).matmul Y' (by grind) = _
          rwa [ReshapeBFn.eq.BFnReshape.of.Dvd])).trans
          (Bool.SEqUFnS.of.SEq hR (F ·)).symm
      else if hgt : batch.length > batch'.length then
        have hge : batch.length ≥ batch'.length := Nat.le_of_lt hgt
        have hL := Tensordot.as.Matmul.of.GeLengthS hge (F X) Y'
        have hR := Tensordot.as.Matmul.of.GeLengthS hge X Y'
        let sL := batch.take (batch.length - batch'.length) ++ batch' ++ [K, k]
        have hmat' := MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS (f := f) h_mul h_sum h0 (by grind) X (Y'.reshape sL (by grind)) B
        apply Bool.Eq.of.SEq
        refine hL.trans ?_
        convert (Bool.SEq.of.Eq hmat').trans (Bool.SEqUFnS.of.SEq hR (F ·)).symm
      else
        have hlen := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
        have h1 := Tensordot.eq.Matmul.of.Length hlen (F X) Y'
        have h2 := Tensordot.eq.Matmul.of.Length hlen X Y'
        rw [h1, h2]
        apply MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS (f := f) h_mul h_sum h0 hlen
    have hL : (F A).einsum C ≃ Af.tensordot Y' := by
      refine hEf.trans ?_
      simp only [Af, Af0, Y', Y0, batch, batch', m, n, n', k, K, F]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y' := by
      refine hE.trans ?_
      simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    apply (hL.trans (Bool.SEq.of.Eq htd)).trans
    symm
    apply Bool.SEqUFnS.of.SEq hR (F ·)


-- created on 2026-08-15
