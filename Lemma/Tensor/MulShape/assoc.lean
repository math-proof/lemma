import sympy.core.mul
import sympy.Basic
import Lemma.List.ZipWithLcm.assoc.of.EqLengthS.EqLengthS
import Lemma.Tensor.Pad1ZipWithLcmPad1.eq.ZipWithLcmPad1.of.Le.LeMaxLength
open List Tensor


@[path]
private lemma main
-- given
  (s s' s'' : List ℕ) :
-- imply
  mul_shape (mul_shape s s') s'' =
      mul_shape s (mul_shape s' s'') := by
-- proof
  let r := s.length ⊔ s'.length ⊔ s''.length
  have hABlen : (mul_shape s s').length ⊔ s''.length = r := by
    rw [mul_shape_length]
  have hBClen : s.length ⊔ (mul_shape s' s'').length = r := by
    rw [mul_shape_length]
    simp [r, max_comm, max_left_comm]
  have hL :
      mul_shape (mul_shape s s') s'' =
        (pad1 (mul_shape s s') r).zipWith Nat.lcm (pad1 s'' r) := by
    rw [mul_shape_eq, hABlen]
  have hR :
      mul_shape s (mul_shape s' s'') =
        (pad1 s r).zipWith Nat.lcm (pad1 (mul_shape s' s'') r) := by
    rw [mul_shape_eq, hBClen]
  have hABpad :
      pad1 (mul_shape s s') r =
        (pad1 s r).zipWith Nat.lcm (pad1 s' r) := by
    rw [mul_shape_eq]
    exact Pad1ZipWithLcmPad1.eq.ZipWithLcmPad1.of.Le.LeMaxLength s s' le_rfl le_sup_left
  have hBCpad :
      pad1 (mul_shape s' s'') r =
        (pad1 s' r).zipWith Nat.lcm (pad1 s'' r) := by
    rw [mul_shape_eq]
    exact Pad1ZipWithLcmPad1.eq.ZipWithLcmPad1.of.Le.LeMaxLength s' s'' le_rfl (by simp [r])
  rw [hL, hR, hABpad, hBCpad]
  apply ZipWithLcm.assoc.of.EqLengthS.EqLengthS
  ·
    rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])]
  ·
    rw [pad1_length s' r (by simp [r]), pad1_length s'' r (by simp [r])]


-- created on 2026-10-07
