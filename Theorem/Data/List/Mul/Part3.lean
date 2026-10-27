import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Def.Data.List.Mul.Part3


namespace Tensor

theorem wrapFlat_lt (s out : List ℕ) (hlen : s.length = out.length)
    (hs : s.prod ≠ 0) (i : ℕ) :
    wrapFlat s out i < s.prod := by
  induction s generalizing out i with
  | nil =>
    cases out with
    | nil =>
      simp [wrapFlat]
    | cons _ _ =>
      cases hlen
  | cons n s ih =>
    cases out with
    | nil =>
      cases hlen
    | cons k tout =>
      have hn : n ≠ 0 := by
        intro hz
        simp [hz] at hs
      have hs' : s.prod ≠ 0 := by
        intro hz
        simp [hz] at hs
      have hlen' : s.length = tout.length := by simpa using hlen
      simp only [wrapFlat, List.prod_cons]
      have hq : i / tout.prod % k % n < n :=
        Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
      have hr : wrapFlat s tout i < s.prod := ih tout hlen' hs' i
      calc
        (i / tout.prod % k % n) * s.prod + wrapFlat s tout i
            < (i / tout.prod % k % n) * s.prod + s.prod :=
          Nat.add_lt_add_left hr _
        _ = (i / tout.prod % k % n + 1) * s.prod := by
          ring
        _ ≤ n * s.prod :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hq)


theorem wrapFlat_lt_src (s s' : List ℕ) (i : ℕ)
    (h : (mul_shape s s').prod ≠ 0) :
    wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s') i < s.prod := by
  have hsa : (pad1 s (s.length ⊔ s'.length)).prod ≠ 0 := by
    rw [pad1_prod]
    exact mt Or.inl ((mul_shape_prod_eq_zero_iff s s').not.mp h)
  have hlen :
      (pad1 s (s.length ⊔ s'.length)).length = (mul_shape s s').length := by
    rw [pad1_length_max, mul_shape_length]
  have := wrapFlat_lt _ _ hlen hsa i
  rwa [pad1_prod] at this

theorem wrapFlat_lt_src' (s s' : List ℕ) (i : ℕ)
    (h : (mul_shape s s').prod ≠ 0) :
    wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s') i < s'.prod := by
  have hsb : (pad1 s' (s.length ⊔ s'.length)).prod ≠ 0 := by
    rw [pad1_prod]
    exact mt Or.inr ((mul_shape_prod_eq_zero_iff s s').not.mp h)
  have hlen :
      (pad1 s' (s.length ⊔ s'.length)).length = (mul_shape s s').length := by
    rw [pad1_length_max', mul_shape_length]
  have := wrapFlat_lt _ _ hlen hsb i
  rwa [pad1_prod] at this

end Tensor
