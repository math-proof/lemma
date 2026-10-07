import Mathlib.Data.Nat.GCD.Basic
import torch.Tensor.Basic

namespace Tensor

/-- Left-pad with `1`s to length `n` (PyTorch-style rank alignment). -/
def pad1 (s : List ℕ) (n : ℕ) : List ℕ :=
  List.replicate (n - s.length) 1 ++ s


theorem pad1_prod (s : List ℕ) (n : ℕ) :
    (pad1 s n).prod = s.prod := by
  simp [pad1, List.prod_replicate]

theorem pad1_length (s : List ℕ) (n : ℕ) (h : s.length ≤ n) :
    (pad1 s n).length = n := by
  simp [pad1]
  omega

theorem pad1_length_max (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s _ le_sup_left

theorem pad1_length_max' (s s' : List ℕ) :
    (pad1 s' (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s' _ le_sup_right

theorem pad1_length_eq (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length =
      (pad1 s' (s.length ⊔ s'.length)).length := by
  rw [pad1_length_max, pad1_length_max']


theorem zipWith_lcm_prod_eq_zero_iff (s s' : List ℕ)
    (h : s.length = s'.length) :
    (s.zipWith Nat.lcm s').prod = 0 ↔ s.prod = 0 ∨ s'.prod = 0 := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil =>
      simp
    | cons _ _ =>
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      simp only [List.zipWith, List.prod_cons, Nat.mul_eq_zero, Nat.lcm_eq_zero_iff]
      rw [ih s' (Nat.succ_injective h)]
      tauto


/--
Output shape of `Tensor.mul`.

Right-align the shapes (left-pad `1`s), then take `Nat.lcm` on each axis.
`lcm 0 x = 0`, so a zero-size axis stays zero.
-/
def mul_shape (s s' : List ℕ) : List ℕ :=
  let n := s.length ⊔ s'.length
  (pad1 s n).zipWith Nat.lcm (pad1 s' n)

theorem mul_shape_eq (s s' : List ℕ) :
    mul_shape s s' =
      (pad1 s (s.length ⊔ s'.length)).zipWith Nat.lcm
        (pad1 s' (s.length ⊔ s'.length)) :=
  rfl

theorem mul_shape_length (s s' : List ℕ) :
    (mul_shape s s').length = s.length ⊔ s'.length := by
  simp [mul_shape, List.length_zipWith, pad1_length_max, pad1_length_max']


theorem mul_shape_prod_eq_zero_iff (s s' : List ℕ) :
    (mul_shape s s').prod = 0 ↔ s.prod = 0 ∨ s'.prod = 0 := by
  rw [mul_shape_eq]
  simp [zipWith_lcm_prod_eq_zero_iff _ _ (pad1_length_eq s s'),
    pad1_prod]

/--
Row-major wrap of a flat index `i` of `out` back into shape `s`.

On each axis: `(coord_out % out_axis) % s_axis`.
Requires `s.length = out.length`.
-/
def wrapFlat : List ℕ → List ℕ → ℕ → ℕ
  | n :: s, k :: tout, i =>
    (i / tout.prod % k % n) * s.prod + wrapFlat s tout i
  | _, _, _ => 0


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


private theorem wrapFlat_lt_src (s s' : List ℕ) (i : ℕ)
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

private theorem wrapFlat_lt_src' (s s' : List ℕ) (i : ℕ)
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

/--
Heterogeneous tensor multiplication `A.mul B`.

Shapes are right-aligned and combined with per-axis `lcm`. Data is the
pointwise product after wrapping each axis (`wrapFlat`).
-/
def mul [Mul α] (A : Tensor α s) (B : Tensor α s') :
    Tensor α (mul_shape s s') :=
  if h : (mul_shape s s').prod = 0 then
    ⟨cast (congrArg (List.Vector α) h.symm) List.Vector.nil⟩
  else
    ⟨List.Vector.ofFn fun i =>
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩⟩


theorem get_mul [Mul α] (A : Tensor α s) (B : Tensor α s')
    (h : (mul_shape s s').prod ≠ 0)
    (i : Fin (mul_shape s s').prod) :
    (A.mul B).data.get i =
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩ := by
  unfold mul
  rw [dif_neg h]
  exact List.Vector.get_ofFn _ _

end Tensor
