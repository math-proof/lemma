import Lemma.Bool.HEq.of.SEq
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [n]) :
-- imply
  X.einsum Y = (X * Y).sum := by
-- proof
  unfold Tensor.einsum
  simp
  congr
  ·
    simp
  ·
    grind
  ·
    grind
  ·
    grind
  ·
    grind
  ·
    grind
  ·
    apply HEq.of.SEq
    apply SEqResize_0.of.Eq_Get_0.GtLength_0
    ·
      simp
    ·
      grind
  ·
    apply HEq.of.SEq
    apply SEqResize_0.of.Eq_Get_0.GtLength_0
    ·
      simp
    ·
      grind


@[main]
private lemma resize
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n])
  (Y : Tensor α [n']) :
-- imply
  let n := n ⊔ n'
  let X' : Tensor α [n] := X.resize ⟨0, by grind⟩ n
  let Y' : Tensor α [n] := Y.resize ⟨0, by grind⟩ n
  X.einsum Y = (X' * Y').sum := by
-- proof
  unfold Tensor.einsum
  simp


-- created on 2026-01-05
-- updated on 2026-08-17
