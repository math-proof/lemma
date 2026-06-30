import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import sympy.tensor.tensor
open Bool
set_option maxHeartbeats 1000000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α ((b :: bz) ++ [m, k]))
  (Y : Tensor α ((b :: bz) ++ [k, n]))
  (i : Fin b) :
-- imply
  (X.batch_dot Y).get i ≃ (X.get i).batch_dot (Y.get i) := by
-- proof
  simp [Tensor.batch_dot]
  apply SEq_Cast.of.SEq.Eq (by grind)
  have h_s : (b :: bz ++ [m, n, k]).eraseIdx ((b :: bz).length + 2) = b :: bz ++ [m, n] := by
    grind
  have h_s₁ : (b :: bz ++ [m, 1, k]).set ((b :: bz).length + 1) (n * (b :: bz ++ [m, 1, k])[(b :: bz).length + 1]) = b :: bz ++ [m, n, k] := by
    grind
  have := Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
    (s' := b :: bz ++ [m, n])
    (s := (b :: bz ++ [m, n, k]).eraseIdx ((b :: bz).length + 2))
    (by grind)
    (by grind)
    ((cast (congrArg (Tensor α) h_s₁) ((cast ⋯ (X.unsqueeze (bz.length + 1 + 1))).repeat n ⟨bz.length + 1 + 1, ⋯⟩) *
              cast ⋯ ((cast ⋯ ((cast ⋯ Yᵀ).unsqueeze (bz.length + 1))).repeat m ⟨bz.length + 1, ⋯⟩)).sum
          (bz.length + 1 + 2))
    (i := ⟨i, by grind⟩)
  rw [this]
  sorry


-- created on 2026-06-24
-- updated on 2026-06-28
