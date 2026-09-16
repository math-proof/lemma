import sympy.matrices.expressions.matmul
import Lemma.Tensor.EqBmm_0'0
import Lemma.Tensor.Resize0.eq.Zero
import Lemma.Tensor.ToVector0.eq.Zero
import Lemma.Vector.Map₂.eq.Zero.of.BFn.eq.Zero
import Lemma.Tensor.OfVector0.eq.Zero
import Lemma.Tensor.EqCast_0'0.of.Eq
open Tensor Vector


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {s s' : List ℕ} {m t k : ℕ}
-- given
  (X : Tensor α (s ++ [m, t]))
  (h : s.length = s'.length) :
-- imply
  X.matmul (0 : Tensor α (s' ++ [t, k])) h = 0 := by
-- proof
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil =>
      unfold Tensor.matmul
      exact Tensor.EqBmm_0'0 X
    | cons =>
      simp at h
  | cons n s ih =>
    cases s' with
    | nil =>
      simp at h
    | cons n' s' =>
      unfold Tensor.matmul
      simp (config := { zeta := true }) only []
      have h_v : List.Vector.map₂
          (fun X Y => Tensor.matmul X Y (by simp at h; omega))
          ((X.resize ⟨0, by simp⟩ (n ⊔ n')).toVector)
          (((0 : Tensor α (n' :: s' ++ [t, k])).resize ⟨0, by simp⟩ (n ⊔ n')).toVector) = 0 := by
        rw [Tensor.Resize0.eq.Zero ⟨0, by simp⟩ (n ⊔ n'), Tensor.ToVector0.eq.Zero _]
        exact Vector.Map₂.eq.Zero.of.BFn.eq.Zero _
          (fun (Xb : Tensor α (s ++ [m, t])) =>
            ih Xb (by simp at h; omega))
      have h_tail : s.length = s'.length := by simp at h; omega
      have hp : n ⊔ n' :: (broadcast_shape s s' ++ [m, k]) =
          broadcast_shape (n :: s) (n' :: s') ++ [m, k] := by
        simp [broadcast_shape]
        split_ifs
        · simp_all
        · simp_all
        · simp [List.zipWith_cons_cons]
      have h_after : cast (congrArg (Tensor α) hp)
          (Tensor.OfVector
            (0 : List.Vector (Tensor α (broadcast_shape s s' ++ [m, k])) (n ⊔ n'))) =
          (0 : Tensor α (broadcast_shape (n :: s) (n' :: s') ++ [m, k])) := by
        rw [Tensor.OfVector0.eq.Zero _ _]
        exact Tensor.EqCast_0'0.of.Eq hp
      exact (congrArg
        (fun v => cast (congrArg (Tensor α) hp) (Tensor.OfVector v)) h_v).trans h_after


-- created on 2026-09-16
