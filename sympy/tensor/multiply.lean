import Mathlib.Data.Nat.GCD.Basic
import sympy.tensor.Basic

namespace Tensor

/-- Left-pad with `1`s to length `n` (PyTorch-style rank alignment). -/
def pad1 (s : List ℕ) (n : ℕ) : List ℕ :=
  List.replicate (n - s.length) 1 ++ s

lemma pad1_id (s : List ℕ) :
    pad1 s s.length = s := by
  simp [pad1]

lemma pad1_prod (s : List ℕ) (n : ℕ) :
    (pad1 s n).prod = s.prod := by
  simp [pad1, List.prod_replicate]

lemma pad1_length (s : List ℕ) (n : ℕ) (h : s.length ≤ n) :
    (pad1 s n).length = n := by
  simp [pad1]
  omega

lemma pad1_length_max (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s _ le_sup_left

lemma pad1_length_max' (s s' : List ℕ) :
    (pad1 s' (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s' _ le_sup_right

lemma pad1_length_eq (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length =
      (pad1 s' (s.length ⊔ s'.length)).length := by
  rw [pad1_length_max, pad1_length_max']

lemma pad1_append_replicate (s : List ℕ) {n m : ℕ}
    (hn : s.length ≤ n) (hm : n ≤ m) :
    pad1 s m = List.replicate (m - n) 1 ++ pad1 s n := by
  simp [pad1]
  have : m - s.length = m - n + (n - s.length) := by omega
  rw [this, List.replicate_add, List.append_assoc]

lemma zipWith_lcm_self (s : List ℕ) :
    s.zipWith Nat.lcm s = s := by
  induction s with
  | nil =>
    rfl
  | cons n s ih =>
    simp [List.zipWith, Nat.lcm_self]

lemma zipWith_lcm_comm (s s' : List ℕ) (h : s.length = s'.length) :
    s.zipWith Nat.lcm s' = s'.zipWith Nat.lcm s := by
  induction s generalizing s' with
  | nil =>
    cases s'
    ·
      rfl
    ·
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      simp [List.zipWith, Nat.lcm_comm]
      exact ih s' (Nat.succ_injective h)

lemma zipWith_lcm_assoc (s s' s'' : List ℕ)
    (h₁ : s.length = s'.length) (h₂ : s'.length = s''.length) :
    (s.zipWith Nat.lcm s').zipWith Nat.lcm s'' =
      s.zipWith Nat.lcm (s'.zipWith Nat.lcm s'') := by
  induction s generalizing s' s'' with
  | nil =>
    cases s'
    ·
      cases s''
      ·
        rfl
      ·
        cases h₂
    ·
      cases h₁
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h₁
    | cons n' s' =>
      cases s'' with
      | nil =>
        cases h₂
      | cons n'' s'' =>
        simp [List.zipWith, Nat.lcm_assoc]
        exact ih s' s'' (Nat.succ_injective h₁) (Nat.succ_injective h₂)

lemma zipWith_lcm_length (s s' : List ℕ) (h : s.length = s'.length) :
    (s.zipWith Nat.lcm s').length = s.length := by
  simp [List.length_zipWith, h]

lemma zipWith_lcm_prod_eq_zero_iff (s s' : List ℕ)
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

lemma zipWith_replicate_one_lcm (k : ℕ) :
    (List.replicate k (1 : ℕ)).zipWith Nat.lcm (List.replicate k 1) =
      List.replicate k 1 := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    simp [List.replicate_succ, Nat.lcm_self]

lemma pad1_zipWith_lcm (s s' : List ℕ) {n m : ℕ}
    (hn : s.length ⊔ s'.length ≤ n) (hm : n ≤ m) :
    pad1 ((pad1 s n).zipWith Nat.lcm (pad1 s' n)) m =
      (pad1 s m).zipWith Nat.lcm (pad1 s' m) := by
  have hs : s.length ≤ n := le_trans le_sup_left hn
  have hs' : s'.length ≤ n := le_trans le_sup_right hn
  have hlen : (pad1 s n).length = (pad1 s' n).length := by
    rw [pad1_length s n hs, pad1_length s' n hs']
  rw [pad1_append_replicate s hs hm, pad1_append_replicate s' hs' hm,
    List.zipWith_append (by simp), zipWith_replicate_one_lcm]
  have hzip_len : ((pad1 s n).zipWith Nat.lcm (pad1 s' n)).length = n := by
    rw [zipWith_lcm_length _ _ hlen, pad1_length s n hs]
  change
    List.replicate (m - ((pad1 s n).zipWith Nat.lcm (pad1 s' n)).length) 1 ++
        (pad1 s n).zipWith Nat.lcm (pad1 s' n) =
      List.replicate (m - n) 1 ++ (pad1 s n).zipWith Nat.lcm (pad1 s' n)
  rw [hzip_len]

/--
Output shape of `Tensor.multiply`.

Right-align the shapes (left-pad `1`s), then take `Nat.lcm` on each axis.
`lcm 0 x = 0`, so a zero-size axis stays zero.
-/
def multiply_shape (s s' : List ℕ) : List ℕ :=
  let n := s.length ⊔ s'.length
  (pad1 s n).zipWith Nat.lcm (pad1 s' n)

lemma multiply_shape_eq (s s' : List ℕ) :
    multiply_shape s s' =
      (pad1 s (s.length ⊔ s'.length)).zipWith Nat.lcm
        (pad1 s' (s.length ⊔ s'.length)) :=
  rfl

lemma multiply_shape_length (s s' : List ℕ) :
    (multiply_shape s s').length = s.length ⊔ s'.length := by
  simp [multiply_shape, List.length_zipWith, pad1_length_max, pad1_length_max']

lemma multiply_shape_self (s : List ℕ) :
    multiply_shape s s = s := by
  simp [multiply_shape, pad1_id]

lemma multiply_shape_comm (s s' : List ℕ) :
    multiply_shape s s' = multiply_shape s' s := by
  have hmax : s.length ⊔ s'.length = s'.length ⊔ s.length := max_comm _ _
  simp only [multiply_shape, hmax]
  exact zipWith_lcm_comm _ _ (by
    rw [← hmax]
    exact pad1_length_eq s s')

lemma multiply_shape_assoc (s s' s'' : List ℕ) :
    multiply_shape (multiply_shape s s') s'' =
      multiply_shape s (multiply_shape s' s'') := by
  let r := s.length ⊔ s'.length ⊔ s''.length
  have hABlen : (multiply_shape s s').length ⊔ s''.length = r := by
    rw [multiply_shape_length]
  have hBClen : s.length ⊔ (multiply_shape s' s'').length = r := by
    rw [multiply_shape_length]
    simp [r, max_comm, max_left_comm]
  have hL :
      multiply_shape (multiply_shape s s') s'' =
        (pad1 (multiply_shape s s') r).zipWith Nat.lcm (pad1 s'' r) := by
    rw [multiply_shape_eq, hABlen]
  have hR :
      multiply_shape s (multiply_shape s' s'') =
        (pad1 s r).zipWith Nat.lcm (pad1 (multiply_shape s' s'') r) := by
    rw [multiply_shape_eq, hBClen]
  have hABpad :
      pad1 (multiply_shape s s') r =
        (pad1 s r).zipWith Nat.lcm (pad1 s' r) := by
    rw [multiply_shape_eq]
    exact pad1_zipWith_lcm s s' le_rfl le_sup_left
  have hBCpad :
      pad1 (multiply_shape s' s'') r =
        (pad1 s' r).zipWith Nat.lcm (pad1 s'' r) := by
    rw [multiply_shape_eq]
    exact pad1_zipWith_lcm s' s'' le_rfl (by simp [r])
  rw [hL, hR, hABpad, hBCpad]
  apply zipWith_lcm_assoc
  ·
    rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])]
  ·
    rw [pad1_length s' r (by simp [r]), pad1_length s'' r (by simp [r])]

lemma multiply_shape_prod_eq_zero_iff (s s' : List ℕ) :
    (multiply_shape s s').prod = 0 ↔ s.prod = 0 ∨ s'.prod = 0 := by
  rw [multiply_shape_eq]
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

lemma wrapFlat_mod (s out : List ℕ) (hlen : s.length = out.length) (i : ℕ) :
    wrapFlat s out i = wrapFlat s out (i % out.prod) := by
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
      have hlen' : s.length = tout.length := by simpa using hlen
      simp only [wrapFlat, List.prod_cons]
      have hdiv :
          (i % (k * tout.prod)) / tout.prod = i / tout.prod % k :=
        Nat.mod_mul_left_div_self i tout.prod k
      have htail := ih tout hlen' i
      have htail' := ih tout hlen' (i % (k * tout.prod))
      have hmod : (i % (k * tout.prod)) % tout.prod = i % tout.prod :=
        Nat.mod_mod_of_dvd i (Nat.dvd_mul_left tout.prod k)
      rw [htail, htail', hmod, hdiv, Nat.mod_mod]

lemma wrapFlat_lt (s out : List ℕ) (hlen : s.length = out.length)
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

lemma wrapFlat_self (s : List ℕ) {i : ℕ} (hi : i < s.prod) :
    wrapFlat s s i = i := by
  induction s generalizing i with
  | nil =>
    simp [wrapFlat] at hi ⊢
    omega
  | cons n s ih =>
    simp only [wrapFlat, List.prod_cons] at hi ⊢
    have hs : s.prod ≠ 0 := by
      intro hz
      simp [hz] at hi
    have hdiv : i / s.prod < n := by
      rw [Nat.mul_comm] at hi
      exact Nat.div_lt_of_lt_mul hi
    have hmod : i % s.prod < s.prod := Nat.mod_lt _ (Nat.pos_of_ne_zero hs)
    rw [Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hdiv]
    rw [wrapFlat_mod s s rfl i, ih hmod, Nat.mul_comm, Nat.div_add_mod]

lemma wrapFlat_pad (s out : List ℕ) (k i : ℕ) :
    wrapFlat (List.replicate k 1 ++ s) (List.replicate k 1 ++ out) i =
      wrapFlat s out i := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    simp [List.replicate_succ, wrapFlat, Nat.mod_one, ih]

lemma wrapFlat_pad1 (s : List ℕ) {n m : ℕ} (out : List ℕ)
    (hn : s.length ≤ n) (hm : n ≤ m) (hout : out.length = n) (i : ℕ) :
    wrapFlat (pad1 s m) (pad1 out m) i = wrapFlat (pad1 s n) out i := by
  rw [pad1_append_replicate s hn hm]
  have : pad1 out m = List.replicate (m - n) 1 ++ out := by
    simp [pad1, hout]
  rw [this, wrapFlat_pad]

lemma wrapFlat_comp (s mid out : List ℕ) (i : ℕ)
    (hsm : List.Forall₂ (fun a b => a ∣ b) s mid)
    (hmo : List.Forall₂ (fun a b => a ∣ b) mid out)
    (hmid : mid.prod ≠ 0) :
    wrapFlat s mid (wrapFlat mid out i) = wrapFlat s out i := by
  induction hsm generalizing out i with
  | nil =>
    cases hmo
    simp [wrapFlat]
  | @cons n m s mid hnm _ ih =>
    cases hmo with
    | @cons _ k _ tout hmk hmo =>
      have hm : m ≠ 0 := by
        intro hz
        simp [hz] at hmid
      have hmt : mid.prod ≠ 0 := by
        intro hz
        simp [hz] at hmid
      simp only [wrapFlat]
      have hr : wrapFlat mid tout i < mid.prod :=
        wrapFlat_lt mid tout (List.Forall₂.length_eq hmo) hmt i
      have hdiv :
          ((i / tout.prod % k % m) * mid.prod + wrapFlat mid tout i) / mid.prod =
            i / tout.prod % k % m := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hmt),
          Nat.div_eq_of_lt hr, zero_add]
      have hmod' :
          ((i / tout.prod % k % m) * mid.prod + wrapFlat mid tout i) % mid.prod =
            wrapFlat mid tout i := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      rw [hdiv, Nat.mod_mod, Nat.mod_mod_of_dvd (i / tout.prod % k) hnm]
      have hlen_sm : s.length = mid.length := List.Forall₂.length_eq ‹_›
      rw [wrapFlat_mod s mid hlen_sm, hmod', ih tout i hmo hmt]

lemma forall₂_dvd_lcm_left (s s' : List ℕ) (h : s.length = s'.length) :
    List.Forall₂ (fun a b => a ∣ b) s (s.zipWith Nat.lcm s') := by
  induction s generalizing s' with
  | nil =>
    cases s'
    ·
      constructor
    ·
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      exact List.Forall₂.cons (Nat.dvd_lcm_left n n')
        (ih s' (Nat.succ_injective h))

lemma forall₂_dvd_lcm_right (s s' : List ℕ) (h : s.length = s'.length) :
    List.Forall₂ (fun a b => a ∣ b) s' (s.zipWith Nat.lcm s') := by
  rw [zipWith_lcm_comm s s' h]
  exact forall₂_dvd_lcm_left s' s h.symm

lemma val_cast_vector {n m : ℕ} (h : n = m) (v : List.Vector α n) :
    (cast (congrArg (List.Vector α) h) v).val = v.val := by
  subst h
  rfl

lemma val_cast_tensor {s s' : List ℕ} (h : s = s') (X : Tensor α s) :
    (cast (congrArg (Tensor α) h) X).data.val = X.data.val := by
  subst h
  rfl

lemma val_get (v : List.Vector α n) {i : ℕ} (hi : i < n)
    (_ : i < v.val.length) :
    v.val[i] = v.get ⟨i, hi⟩ :=
  rfl

private lemma wrapFlat_lt_src (s s' : List ℕ) (i : ℕ)
    (h : (multiply_shape s s').prod ≠ 0) :
    wrapFlat (pad1 s (s.length ⊔ s'.length)) (multiply_shape s s') i < s.prod := by
  have hsa : (pad1 s (s.length ⊔ s'.length)).prod ≠ 0 := by
    rw [pad1_prod]
    exact mt Or.inl ((multiply_shape_prod_eq_zero_iff s s').not.mp h)
  have hlen :
      (pad1 s (s.length ⊔ s'.length)).length = (multiply_shape s s').length := by
    rw [pad1_length_max, multiply_shape_length]
  have := wrapFlat_lt _ _ hlen hsa i
  rwa [pad1_prod] at this

private lemma wrapFlat_lt_src' (s s' : List ℕ) (i : ℕ)
    (h : (multiply_shape s s').prod ≠ 0) :
    wrapFlat (pad1 s' (s.length ⊔ s'.length)) (multiply_shape s s') i < s'.prod := by
  have hsb : (pad1 s' (s.length ⊔ s'.length)).prod ≠ 0 := by
    rw [pad1_prod]
    exact mt Or.inr ((multiply_shape_prod_eq_zero_iff s s').not.mp h)
  have hlen :
      (pad1 s' (s.length ⊔ s'.length)).length = (multiply_shape s s').length := by
    rw [pad1_length_max', multiply_shape_length]
  have := wrapFlat_lt _ _ hlen hsb i
  rwa [pad1_prod] at this

/--
Heterogeneous tensor multiplication `A.multiply B`.

Shapes are right-aligned and combined with per-axis `lcm`. Data is the
pointwise product after wrapping each axis (`wrapFlat`).
-/
def multiply [Mul α] (A : Tensor α s) (B : Tensor α s') :
    Tensor α (multiply_shape s s') :=
  if h : (multiply_shape s s').prod = 0 then
    ⟨cast (congrArg (List.Vector α) h.symm) List.Vector.nil⟩
  else
    ⟨List.Vector.ofFn fun i =>
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (multiply_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (multiply_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩⟩

lemma val_multiply_zero [Mul α] (A : Tensor α s) (B : Tensor α s')
    (h : (multiply_shape s s').prod = 0) :
    (A.multiply B).data.val = [] := by
  unfold multiply
  rw [dif_pos h]
  exact val_cast_vector h.symm List.Vector.nil

lemma get_multiply [Mul α] (A : Tensor α s) (B : Tensor α s')
    (h : (multiply_shape s s').prod ≠ 0)
    (i : Fin (multiply_shape s s').prod) :
    (A.multiply B).data.get i =
      A.data.get ⟨wrapFlat (pad1 s (s.length ⊔ s'.length)) (multiply_shape s s') i.val,
        wrapFlat_lt_src s s' i.val h⟩ *
      B.data.get ⟨wrapFlat (pad1 s' (s.length ⊔ s'.length)) (multiply_shape s s') i.val,
        wrapFlat_lt_src' s s' i.val h⟩ := by
  unfold multiply
  rw [dif_neg h]
  exact List.Vector.get_ofFn _ _

lemma pad_rank_left (s s' s'' : List ℕ) :
    s.length ⊔ (multiply_shape s' s'').length =
      s.length ⊔ s'.length ⊔ s''.length := by
  rw [multiply_shape_length]
  simp [max_comm, max_left_comm]

lemma pad_rank_right (s s' s'' : List ℕ) :
    (multiply_shape s s').length ⊔ s''.length =
      s.length ⊔ s'.length ⊔ s''.length := by
  rw [multiply_shape_length]

/--
Wrapping `A` through `A.multiply B`, then through `(A.multiply B).multiply C`,
is wrapping `A` directly into the ternary output.
-/
lemma wrapFlat_through_multiply (s s' s'' : List ℕ) (i : ℕ)
    (hAB : (multiply_shape s s').prod ≠ 0)
    (_hout : (multiply_shape (multiply_shape s s') s'').prod ≠ 0) :
    wrapFlat (pad1 s (s.length ⊔ s'.length)) (multiply_shape s s')
      (wrapFlat
        (pad1 (multiply_shape s s')
          ((multiply_shape s s').length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i) =
      wrapFlat (pad1 s (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i := by
  let r := s.length ⊔ s'.length ⊔ s''.length
  let n := s.length ⊔ s'.length
  have hn : n ≤ r := le_sup_left
  have hABlen : (multiply_shape s s').length = n := multiply_shape_length s s'
  have hpadn : (multiply_shape s s').length ⊔ s''.length = r := by
    rw [hABlen]
  have hmid :
      pad1 (multiply_shape s s') r =
        (pad1 s r).zipWith Nat.lcm (pad1 s' r) := by
    rw [multiply_shape_eq]
    exact pad1_zipWith_lcm s s' le_rfl hn
  have hsm :
      List.Forall₂ (fun a b => a ∣ b) (pad1 s r)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r)) :=
    forall₂_dvd_lcm_left _ _ (by
      rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])])
  have hmo :
      List.Forall₂ (fun a b => a ∣ b)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
        (multiply_shape (multiply_shape s s') s'') := by
    have : multiply_shape (multiply_shape s s') s'' =
        (pad1 (multiply_shape s s') r).zipWith Nat.lcm (pad1 s'' r) := by
      rw [multiply_shape_eq, hpadn]
    rw [this, hmid]
    exact forall₂_dvd_lcm_left _ _
      (by
        rw [zipWith_lcm_length _ _
            (by rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])]),
          pad1_length s r (by simp [r]),
          pad1_length s'' r (by simp [r])])
  have hmid_ne : ((pad1 s r).zipWith Nat.lcm (pad1 s' r)).prod ≠ 0 := by
    rw [← hmid, pad1_prod]
    exact hAB
  have hcomp :=
    wrapFlat_comp (pad1 s r) ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
      (multiply_shape (multiply_shape s s') s'') i hsm hmo hmid_ne
  have hpad :=
    wrapFlat_pad1 s (multiply_shape s s') le_sup_left hn hABlen
      (wrapFlat (pad1 (multiply_shape s s')
          ((multiply_shape s s').length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i)
  rw [hpadn] at hpad ⊢
  rw [← hpad, hmid]
  exact hcomp

/--
Wrapping `B` through `A.multiply B`, then through `(A.multiply B).multiply C`,
is wrapping `B` directly into the ternary output.
-/
lemma wrapFlat_through_multiply' (s s' s'' : List ℕ) (i : ℕ)
    (hAB : (multiply_shape s s').prod ≠ 0)
    (_hout : (multiply_shape (multiply_shape s s') s'').prod ≠ 0) :
    wrapFlat (pad1 s' (s.length ⊔ s'.length)) (multiply_shape s s')
      (wrapFlat
        (pad1 (multiply_shape s s')
          ((multiply_shape s s').length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i) =
      wrapFlat (pad1 s' (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i := by
  let r := s.length ⊔ s'.length ⊔ s''.length
  let n := s.length ⊔ s'.length
  have hn : n ≤ r := le_sup_left
  have hABlen : (multiply_shape s s').length = n := multiply_shape_length s s'
  have hpadn : (multiply_shape s s').length ⊔ s''.length = r := by
    rw [hABlen]
  have hmid :
      pad1 (multiply_shape s s') r =
        (pad1 s r).zipWith Nat.lcm (pad1 s' r) := by
    rw [multiply_shape_eq]
    exact pad1_zipWith_lcm s s' le_rfl hn
  have hsm :
      List.Forall₂ (fun a b => a ∣ b) (pad1 s' r)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r)) :=
    forall₂_dvd_lcm_right _ _ (by
      rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])])
  have hmo :
      List.Forall₂ (fun a b => a ∣ b)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
        (multiply_shape (multiply_shape s s') s'') := by
    have : multiply_shape (multiply_shape s s') s'' =
        (pad1 (multiply_shape s s') r).zipWith Nat.lcm (pad1 s'' r) := by
      rw [multiply_shape_eq, hpadn]
    rw [this, hmid]
    exact forall₂_dvd_lcm_left _ _
      (by
        rw [zipWith_lcm_length _ _
            (by rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])]),
          pad1_length s r (by simp [r]),
          pad1_length s'' r (by simp [r])])
  have hmid_ne : ((pad1 s r).zipWith Nat.lcm (pad1 s' r)).prod ≠ 0 := by
    rw [← hmid, pad1_prod]
    exact hAB
  have hcomp :=
    wrapFlat_comp (pad1 s' r) ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
      (multiply_shape (multiply_shape s s') s'') i hsm hmo hmid_ne
  have hpad :=
    wrapFlat_pad1 s' (multiply_shape s s') le_sup_right hn hABlen
      (wrapFlat (pad1 (multiply_shape s s')
          ((multiply_shape s s').length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i)
  rw [hpadn] at hpad ⊢
  rw [← hpad, hmid]
  exact hcomp

/--
Wrapping `B` through `B.multiply C`, then through `A.multiply (B.multiply C)`.
-/
lemma wrapFlat_through_multiply_right (s s' s'' : List ℕ) (i : ℕ)
    (hBC : (multiply_shape s' s'').prod ≠ 0)
    (hout : (multiply_shape s (multiply_shape s' s'')).prod ≠ 0) :
    wrapFlat (pad1 s' (s'.length ⊔ s''.length)) (multiply_shape s' s'')
      (wrapFlat
        (pad1 (multiply_shape s' s'')
          (s.length ⊔ (multiply_shape s' s'').length))
        (multiply_shape s (multiply_shape s' s'')) i) =
      wrapFlat (pad1 s' (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape s (multiply_shape s' s'')) i := by
  have h := wrapFlat_through_multiply s' s'' s i hBC (by
    rwa [multiply_shape_comm])
  simp only [multiply_shape_comm (multiply_shape s' s'') s,
    max_comm (multiply_shape s' s'').length s.length,
    max_comm (s'.length ⊔ s''.length) s.length] at h
  rw [max_assoc]
  exact h

/--
Wrapping `C` through `B.multiply C`, then through `A.multiply (B.multiply C)`.
-/
lemma wrapFlat_through_multiply_right' (s s' s'' : List ℕ) (i : ℕ)
    (hBC : (multiply_shape s' s'').prod ≠ 0)
    (hout : (multiply_shape s (multiply_shape s' s'')).prod ≠ 0) :
    wrapFlat (pad1 s'' (s'.length ⊔ s''.length)) (multiply_shape s' s'')
      (wrapFlat
        (pad1 (multiply_shape s' s'')
          (s.length ⊔ (multiply_shape s' s'').length))
        (multiply_shape s (multiply_shape s' s'')) i) =
      wrapFlat (pad1 s'' (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape s (multiply_shape s' s'')) i := by
  have h := wrapFlat_through_multiply' s' s'' s i hBC (by
    rwa [multiply_shape_comm])
  simp only [multiply_shape_comm (multiply_shape s' s'') s,
    max_comm (multiply_shape s' s'').length s.length,
    max_comm (s'.length ⊔ s''.length) s.length] at h
  rw [max_assoc]
  exact h

lemma wrapFlat_align_left (s s' s'' : List ℕ) (i : ℕ) :
    wrapFlat (pad1 s (s.length ⊔ (multiply_shape s' s'').length))
      (multiply_shape s (multiply_shape s' s'')) i =
      wrapFlat (pad1 s (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape s (multiply_shape s' s'')) i := by
  rw [pad_rank_left]

lemma wrapFlat_align_right (s s' s'' : List ℕ) (i : ℕ) :
    wrapFlat (pad1 s'' ((multiply_shape s s').length ⊔ s''.length))
      (multiply_shape (multiply_shape s s') s'') i =
      wrapFlat (pad1 s'' (s.length ⊔ s'.length ⊔ s''.length))
        (multiply_shape (multiply_shape s s') s'') i := by
  rw [pad_rank_right]

end Tensor
