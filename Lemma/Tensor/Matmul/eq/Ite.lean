import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open Nat List
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  X.matmul Y =
    if h_s : s.length = 0 then
      cast (by simp_all [Tensor.matmul_shape]) (X.data[0]'(by simp_all) * Y)
    else if h_s' : s'.length = 0 then
      cast (by simp_all [Tensor.matmul_shape]) (X * Y.data[0]'(by simp_all))
    else if h_s : s.length = 1 then
      match s with
      | [n] =>
        if h_s' : s'.length = 1 then
          match s' with
          | [n'] =>
            if h_n : n < n' then
              let q := n' / n
              let r := n' % n
              let X : Tensor α [n'] := cast
                (by simp [q, r, EqAddMulDiv])
                ((cast (by simp_all) (X.repeat q ⟨0, by linarith⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
              ((X.data * Y.data).sum : Tensor α [])
            else if h_n : n > n' then
              let q := n / n'
              let r := n % n'
              let Y : Tensor α [n] := cast
                (by simp [q, r, EqAddMulDiv])
                ((cast (by simp_all) (Y.repeat q ⟨0, by linarith⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
              ((X.data * Y.data).sum : Tensor α [])
            else
              let Y : Tensor α [n] := cast (by grind) Y
              ((X.data * Y.data).sum : Tensor α [])
        else
          have h_s' : s'.length ≥ 2 := by omega
          let batch_size' := s'.take (s'.length - 2)
          let n' := s'[s'.length - 2]
          let k' := s'[s'.length - 1]
          let Y : Tensor α (batch_size' ++ [n', k']) := cast
            (by
              congr
              simp [batch_size', n', k']
              conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
              apply EqAppendS.of.Eq.left
              apply Drop.eq.ListGetS.of.GeLength_2 h_s'
            )
            Y
          if h_n : n < n' then
            let q := n' / n
            let r := n' % n
            let X : Tensor α [n'] := cast
              (by simp [q, r, EqAddMulDiv])
              ((cast (by grind) (X.repeat q ⟨0, by linarith⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
            let X := X.broadcast ((batch_size' ++ [1, n'])) (by simp)
            cast
              (by
                congr
                simp [batch_size', k', Tensor.matmul_shape]
                have h_s' : s' ≠ [] := by grind
                simp [h_s']
                rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                simp [EraseIdx.eq.Append_Drop_Add_1]
                simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
                rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
              )
              ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)
          else if h_n : n > n' then
            let q := n / n'
            let r := n % n'
            let Y : Tensor α (batch_size' ++ [n, k']) := cast (by simp [q, r, EqAddMulDiv]) ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k'])) ++ (0 : Tensor α (batch_size' ++ [r, k'])))
            let X := X.broadcast ((batch_size' ++ [1, n])) (by simp)
            cast
              (by
                congr
                simp [batch_size', k', Tensor.matmul_shape]
                have h_s' : s' ≠ [] := by grind
                simp [h_s']
                rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                simp [EraseIdx.eq.Append_Drop_Add_1]
                simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
                rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
              )
              ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)
          else if h_n : n < n' then
            let q := n' / n
              let r := n' % n
              let X : Tensor α [n'] := cast
                (by simp [q, r, EqAddMulDiv])
                ((cast (by grind) (X.repeat q ⟨0, by linarith⟩) : Tensor α [q * n]) ++ (0 : Tensor α [r]))
              let X := X.broadcast ((batch_size' ++ [1, n'])) (by simp)
              cast
                (by
                  congr
                  simp [batch_size', k', Tensor.matmul_shape]
                  have h_s' : s' ≠ [] := by grind
                  simp [h_s']
                  rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                  simp [EraseIdx.eq.Append_Drop_Add_1]
                  simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
                  rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
                )
                ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)

          else if h_n : n > n' then
            let q := n / n'
              let r := n % n'
              let Y : Tensor α (batch_size' ++ [n, k']) := cast (by simp [q, r, EqAddMulDiv]) ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k'])) ++ (0 : Tensor α (batch_size' ++ [r, k'])))
              let X := X.broadcast ((batch_size' ++ [1, n])) (by simp)
              cast
                (by
                  congr
                  simp [batch_size', k', Tensor.matmul_shape]
                  have h_s' : s' ≠ [] := by grind
                  simp [h_s']
                  rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                  simp [EraseIdx.eq.Append_Drop_Add_1]
                  simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
                  rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
                )
                ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)

          else
            let Y : Tensor α (batch_size' ++ [n, k']) := cast (by grind) Y
              let X := X.broadcast ((batch_size' ++ [1, n])) (by simp)
              cast
                (by
                  congr
                  simp [batch_size', k', Tensor.matmul_shape]
                  have h_s' : s' ≠ [] := by grind
                  simp [h_s']
                  rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
                  simp [EraseIdx.eq.Append_Drop_Add_1]
                  simp [show s'.length - 2 + 1 = s'.length - 1 by omega]
                  rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]
                )
                ((X.batch_dot Y).select ⟨s'.length - 2, by simp [batch_size']⟩ ⟨0, by grind⟩)
    else if h_s' : s'.length = 1 then
      match s' with
      | [n'] =>
        have h_s : s.length ≥ 2 := by omega
        let batch_size := s.take (s.length - 2)
        let k := s[s.length - 2]
        let n := s[s.length - 1]
        let X : Tensor α (batch_size ++ [k, n]) := cast
          (by
            congr
            simp [batch_size, n, k]
            conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
            apply EqAppendS.of.Eq.left
            apply Drop.eq.ListGetS.of.GeLength_2 h_s
          )
          X
        if h_n : n < n' then
          let q := n' / n
          let r := n' % n
          let X : Tensor α (batch_size ++ [k, n']) := cast (by simp [q, r, EqAddMulDiv]) ((cast (by simp [batch_size]; grind) (X.repeat q ⟨s.length - 1, by simp [batch_size]; omega⟩) : Tensor α (batch_size ++ [k] ++ [q * n])) ++ (0 : Tensor α (batch_size ++ [k] ++ [r])))
          let Y := Y.broadcast ((batch_size ++ [n', 1])) (by simp)
          cast
            (by
              congr
              simp [batch_size, k, Tensor.matmul_shape]
              have h_s : s ≠ [] := by grind
              simp [h_s]
              have h_s : s.length ≠ 1 := by grind
              simp [h_s]
              rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
              simp [EraseIdx.eq.Append_Drop_Add_1]
              simp [show s.length - 1 - (s.length - 2) = 1 by omega]
              simp [show s.length - 2 + 1 = s.length - 1 by omega]
              rw [DropLast.eq.Take_SubLength_1]
            )
            ((X.batch_dot Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩)
        else if h_n : n > n' then
          let q := n / n'
          let r := n % n'
          let Y : Tensor α [n] := cast
            (by simp [q, r, EqAddMulDiv])
            ((cast (by grind) (Y.repeat q ⟨0, by linarith⟩) : Tensor α [q * n']) ++ (0 : Tensor α [r]))
          let Y := Y.broadcast ((batch_size ++ [n, 1])) (by simp)
          cast
            (by
              congr
              simp [batch_size, k, Tensor.matmul_shape]
              have h_s : s ≠ [] := by grind
              simp [h_s]
              have h_s : s.length ≠ 1 := by grind
              simp [h_s]
              rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
              simp [EraseIdx.eq.Append_Drop_Add_1]
              simp [show s.length - 1 - (s.length - 2) = 1 by omega]
              simp [show s.length - 2 + 1 = s.length - 1 by omega]
              rw [DropLast.eq.Take_SubLength_1]
            )
            ((X.batch_dot Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩)
        else
          have h_n : n = n' := by omega
          let Y := Y.broadcast ((batch_size ++ [n, 1])) (by simp_all)
          cast
            (by
              congr
              simp [batch_size, k, Tensor.matmul_shape]
              have h_s : s ≠ [] := by grind
              simp [h_s]
              have h_s : s.length ≠ 1 := by grind
              simp [h_s]
              rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
              simp [EraseIdx.eq.Append_Drop_Add_1]
              simp [show s.length - 1 - (s.length - 2) = 1 by omega]
              simp [show s.length - 2 + 1 = s.length - 1 by omega]
              rw [DropLast.eq.Take_SubLength_1]
            )
            ((X.batch_dot Y).select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩)
    else
      have h_s : s.length ≥ 2 := by omega
      have h_s' : s'.length ≥ 2 := by omega
      let batch_size := s.take (s.length - 2)
      let batch_size' := s'.take (s'.length - 2)
      let m := s[s.length - 2]
      let n := s[s.length - 1]
      let n' := s'[s'.length - 2]
      let k := s'[s'.length - 1]
      let X : Tensor α (batch_size ++ [m, n]) := cast
        (by
          congr
          simp [batch_size, m, n]
          conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
          apply EqAppendS.of.Eq.left
          apply Drop.eq.ListGetS.of.GeLength_2 h_s
        )
        X
      let Y : Tensor α (batch_size' ++ [n', k]) := cast
        (by
          congr
          simp [batch_size', n', k]
          conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
          apply EqAppendS.of.Eq.left
          apply Drop.eq.ListGetS.of.GeLength_2 h_s'
        )
        Y
      if h_n : n < n' then
        let q := n' / n
        let r := n' % n
        let X : Tensor α (batch_size ++ [m, n']) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp; grind) (X.repeat q ⟨s.length - 1, by simp [batch_size]; omega⟩) : Tensor α (batch_size ++ [m] ++ [q * n])) ++ (0 : Tensor α (batch_size ++ [m] ++ [r])))
        cast
          (by
            congr
            simp [batch_size, batch_size', m, k, Tensor.matmul_shape, Tensor.broadcast_shape]
            grind
          )
          (Tensor.broadcast_matmul X Y)
      else if h_n : n > n' then
        let q := n / n'
        let r := n % n'
        let Y : Tensor α (batch_size' ++ [n, k]) := cast
          (by simp [q, r, EqAddMulDiv])
          ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k])) ++ (0 : Tensor α (batch_size' ++ [r, k])))
        cast
          (by
            congr
            simp [batch_size, batch_size', m, k, Tensor.matmul_shape, Tensor.broadcast_shape]
            grind
          )
          (Tensor.broadcast_matmul X Y)
      else
        have h_n : n = n' := by omega
        let Y : Tensor α (batch_size' ++ [n, k]) := cast (by simp_all) Y
        cast
          (by
            congr
            simp [batch_size, batch_size', m, k, Tensor.matmul_shape, Tensor.broadcast_shape]
            grind
          )
          (Tensor.broadcast_matmul X Y) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-05
-- updated on 2026-01-06
