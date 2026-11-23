import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Lemma.Matrix.MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
open Matrix Real
open scoped Matrix
set_option maxHeartbeats 800000


private lemma sum_single
  {d : ℕ}
  {t : Fin d}
  {body : Fin d → ℝ}
-- given
  (hoff : ∀ r, r ≠ t → body r = 0) :
-- imply
  ∑ r : Fin d, body r = body t := by
-- proof
  refine Finset.sum_eq_single t ?_ ?_
  ·
    intro r _ hne
    apply hoff r hne
  ·
    intro h
    exact absurd (Finset.mem_univ t) h

private lemma sum_mul_ite
  {d : ℕ}
-- given
  (t s : Fin d)
  (f g : Fin d → ℝ) :
-- imply
  (∑ r : Fin d, (if r = t then f r else 0) * (if r = s then g r else 0)) =
    if t = s then f t * g t else 0 := by
-- proof
  if h : t = s then
    subst h
    have hterm (r : Fin d) :
      (if r = t then f r else 0) * (if r = t then g r else 0) =
        if r = t then f r * g r else 0 := by
      if hr : r = t then
        simp [hr]
      else
        simp [hr]
    simp_rw [hterm]
    simp
  else
    rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro r _
    if hr : r = t then
      simp [hr, h]
    else
      simp [hr]

private lemma sum_if_and_comm
  {d : ℕ}
  {p q : Fin d → Prop} [DecidablePred p] [DecidablePred q]
-- given
  (f : Fin d → ℝ) :
-- imply
  (∑ t : Fin d, if p t ∧ q t then f t else 0) =
    ∑ t : Fin d, if q t ∧ p t then f t else 0 := by
-- proof
  refine Finset.sum_congr rfl fun t _ => ?_
  if h : p t ∧ q t then
    rw [ite_eq_left h, ite_eq_left h.symm]
  else
    have h' : ¬ (q t ∧ p t) := fun hc => h hc.symm
    rw [ite_eq_right h, ite_eq_right h']

private lemma rotaryOn_uu
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (huv : ∀ t s, u t ≠ v s)
  (θ : Fin d → ℝ)
  (t s : Fin d) :
-- imply
  Matrix.rotaryOn u v θ (u t) (u s) = if t = s then Real.cos (θ t) else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [Matrix.of_apply]
  refine Eq.trans (sum_single (t := t) ?_) ?_
  ·
    intro r hne
    have htu : u t ≠ u r := fun h => hne (hu h).symm
    have htv : u t ≠ v r := huv t r
    simp [htu, htv]
  ·
    have htv : u t ≠ v t := huv t t
    have hsw : u s ≠ v t := huv s t
    if hts : t = s then
      subst hts
      simp [htv]
    else
      have hsu : u s ≠ u t := fun h => hts (hu h).symm
      simp [hts, htv, hsw, hsu]

private lemma rotaryOn_uv
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (θ : Fin d → ℝ)
  (t s : Fin d) :
-- imply
  Matrix.rotaryOn u v θ (u t) (v s) = if t = s then -Real.sin (θ t) else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [Matrix.of_apply]
  refine Eq.trans (sum_single (t := t) ?_) ?_
  ·
    intro r hne
    have htu : u t ≠ u r := fun h => hne (hu h).symm
    have htv : u t ≠ v r := huv t r
    simp [htu, htv]
  ·
    have htu : u t ≠ v t := huv t t
    have hcol : v s ≠ u t := (huv t s).symm
    if hts : t = s then
      subst hts
      simp [htu, hcol]
    else
      have hsv : v s ≠ v t := fun h => hts (hv h).symm
      simp [hts, htu, hcol, hsv]

private lemma rotaryOn_vu
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (θ : Fin d → ℝ)
  (t s : Fin d) :
-- imply
  Matrix.rotaryOn u v θ (v t) (u s) = if t = s then Real.sin (θ t) else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [Matrix.of_apply]
  refine Eq.trans (sum_single (t := t) ?_) ?_
  ·
    intro r hne
    have htu : v t ≠ u r := (huv r t).symm
    have htv : v t ≠ v r := fun h => hne (hv h).symm
    simp [htu, htv]
  ·
    have htu : v t ≠ u t := (huv t t).symm
    have hcol : u s ≠ v t := huv s t
    if hts : t = s then
      subst hts
      simp [htu, hcol]
    else
      have hsu : u s ≠ u t := fun h => hts (hu h).symm
      simp [hts, htu, hcol, hsu]

private lemma rotaryOn_vv
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (θ : Fin d → ℝ)
  (t s : Fin d) :
-- imply
  Matrix.rotaryOn u v θ (v t) (v s) = if t = s then Real.cos (θ t) else 0 := by
-- proof
  unfold Matrix.rotaryOn
  rw [Matrix.of_apply]
  refine Eq.trans (sum_single (t := t) ?_) ?_
  ·
    intro r hne
    have htu : v t ≠ u r := (huv r t).symm
    have htv : v t ≠ v r := fun h => hne (hv h).symm
    simp [htu, htv]
  ·
    have htu : v t ≠ u t := (huv t t).symm
    have hcol : v s ≠ u t := (huv t s).symm
    if hts : t = s then
      subst hts
      simp [htu]
    else
      have hsv : v s ≠ v t := fun h => hts (hv h).symm
      simp [hts, htu, hcol, hsv]

private lemma natAdd_inj
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.natAdd d : Fin d → Fin (d + d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.natAdd] at this
  omega

private lemma half_disj
-- given
  (d : ℕ)
  (t s : Fin d) :
-- imply
  Fin.castAdd d t ≠ Fin.natAdd d s := by
-- proof
  intro h
  have := congrArg Fin.val h
  simp [Fin.castAdd, Fin.natAdd] at this
  have := t.isLt
  omega

private lemma half_surj
-- given
  (d : ℕ)
  (i : Fin (d + d)) :
-- imply
  (∃ t : Fin d, Fin.castAdd d t = i) ∨ (∃ t : Fin d, Fin.natAdd d t = i) := by
-- proof
  if h : (i : ℕ) < d then
    refine Or.inl ⟨⟨(i : ℕ), h⟩, ?_⟩
    ext
    rfl
  else
    refine Or.inr ⟨⟨(i : ℕ) - d, ?_⟩, ?_⟩
    ·
      have := i.isLt
      omega
    ·
      ext
      simp [Fin.natAdd]
      omega

private lemma sum_half
  {d : ℕ}
-- given
  (f : Fin (d + d) → ℝ) :
-- imply
  ∑ i, f i = ∑ t : Fin d, f (Fin.castAdd d t) + ∑ t : Fin d, f (Fin.natAdd d t) := by
-- proof
  let e := finSumFinEquiv (m := d) (n := d)
  have hs : ∑ i, f i = ∑ s : Fin d ⊕ Fin d, f (e s) := (e.sum_comp f).symm
  rw [hs, Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_left]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e, finSumFinEquiv_apply_right]

private lemma ropeEven_inj
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Matrix.ropeEven d) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Matrix.ropeEven] at this
  omega

private lemma ropeOdd_inj
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Matrix.ropeOdd d) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Matrix.ropeOdd] at this
  omega

private lemma rope_disj
-- given
  (d : ℕ)
  (t s : Fin d) :
-- imply
  Matrix.ropeEven d t ≠ Matrix.ropeOdd d s := by
-- proof
  intro h
  have := congrArg Fin.val h
  simp [Matrix.ropeEven, Matrix.ropeOdd] at this
  omega

private lemma div2_lt
  {d : ℕ}
-- given
  (i : Fin (d + d)) :
-- imply
  (i : ℕ) / 2 < d := by
-- proof
  have := i.isLt
  omega

private lemma rope_surj
-- given
  (d : ℕ)
  (i : Fin (d + d)) :
-- imply
  (∃ t : Fin d, Matrix.ropeEven d t = i) ∨ (∃ t : Fin d, Matrix.ropeOdd d t = i) := by
-- proof
  if h : (i : ℕ) % 2 = 0 then
    refine Or.inl ⟨⟨(i : ℕ) / 2, div2_lt i⟩, ?_⟩
    ext
    simp [Matrix.ropeEven]
    omega
  else
    refine Or.inr ⟨⟨(i : ℕ) / 2, div2_lt i⟩, ?_⟩
    ext
    simp [Matrix.ropeOdd]
    omega

private lemma sum_rope
-- given
  (d : ℕ)
  (f : Fin (d + d) → ℝ) :
-- imply
  ∑ i, f i = ∑ t : Fin d, f (Matrix.ropeEven d t) + ∑ t : Fin d, f (Matrix.ropeOdd d t) := by
-- proof
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) :=
    { toFun := fun
        | Sum.inl t => Matrix.ropeEven d t
        | Sum.inr t => Matrix.ropeOdd d t
      invFun := fun i =>
        if (i : ℕ) % 2 = 0 then
          Sum.inl ⟨(i : ℕ) / 2, div2_lt i⟩
        else
          Sum.inr ⟨(i : ℕ) / 2, div2_lt i⟩
      left_inv := by
        intro s
        cases s with
        | inl t =>
          simp [Matrix.ropeEven, show 2 * (t : ℕ) % 2 = 0 by omega]
        | inr t =>
          have hod : (2 * (t : ℕ) + 1) % 2 = 1 := by omega
          simp [Matrix.ropeOdd, hod, show (1 : ℕ) ≠ 0 by decide]
          apply Fin.ext
          change (2 * (t : ℕ) + 1) / 2 = (t : ℕ)
          rw [Nat.mul_add_div (by decide : 0 < 2)]
          simp
      right_inv := by
        intro i
        ext
        if h : (i : ℕ) % 2 = 0 then
          simp [Matrix.ropeEven, h]
          omega
        else
          simp [Matrix.ropeOdd, h]
          omega }
  have hs : ∑ i, f i = ∑ s : Fin d ⊕ Fin d, f (e s) := (e.sum_comp f).symm
  rw [hs, Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [e]

private lemma rotaryOn_neg
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (θ : Fin d → ℝ) :
-- imply
  Matrix.rotaryOn u v (-θ) = (Matrix.rotaryOn u v θ)ᵀ := by
-- proof
  ext i j
  have hL :
    Matrix.rotaryOn u v (-θ) i j =
      (∑ t : Fin d, if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if i = u t ∧ j = v t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = u t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.rotaryOn, Matrix.of_apply, Pi.neg_apply, Finset.sum_add_distrib, Real.cos_neg,
      Real.sin_neg, neg_neg]
  have hR :
    (Matrix.rotaryOn u v θ)ᵀ i j =
      (∑ t : Fin d, if j = u t ∧ i = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if j = u t ∧ i = v t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = u t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.transpose_apply, Matrix.rotaryOn, Matrix.of_apply, Finset.sum_add_distrib]
  rw [hL, hR]
  rw [sum_if_and_comm (p := fun t => i = u t) (q := fun t => j = u t) (f := fun t => Real.cos (θ t))]
  rw [sum_if_and_comm (p := fun t => i = u t) (q := fun t => j = v t) (f := fun t => Real.sin (θ t))]
  rw [sum_if_and_comm (p := fun t => i = v t) (q := fun t => j = u t) (f := fun t => -Real.sin (θ t))]
  rw [sum_if_and_comm (p := fun t => i = v t) (q := fun t => j = v t) (f := fun t => Real.cos (θ t))]
  ring

private lemma trig_uu
-- given
  (a b : ℝ) :
-- imply
  a.cos * b.cos + a.sin * b.sin = (b - a).cos := by
-- proof
  rw [Real.cos_sub]
  ring

private lemma trig_uv
-- given
  (a b : ℝ) :
-- imply
  -(a.cos * b.sin) + a.sin * b.cos = -((b - a).sin) := by
-- proof
  rw [Real.sin_sub]
  ring

private lemma trig_vu
-- given
  (a b : ℝ) :
-- imply
  -(a.sin * b.cos) + a.cos * b.sin = (b - a).sin := by
-- proof
  rw [Real.sin_sub]
  ring

private lemma trig_vv
-- given
  (a b : ℝ) :
-- imply
  a.sin * b.sin + a.cos * b.cos = (b - a).cos := by
-- proof
  rw [Real.cos_sub]
  ring

private lemma rotaryOn_mul_sub
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (α β : Fin d → ℝ) :
-- imply
  (Matrix.rotaryOn u v α)ᵀ * Matrix.rotaryOn u v β =
    Matrix.rotaryOn u v (β - α) := by
-- proof
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply]
  cases (hsurj i) with
  | inl hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (u t) * Matrix.rotaryOn u v β k (u s))]
      simp_rw [rotaryOn_uu hu huv α, rotaryOn_uu hu huv β, rotaryOn_vu hu hv huv α,
        rotaryOn_vu hu hv huv β, sum_mul_ite, rotaryOn_uu hu huv (β - α)]
      if h : t = s then
        simp [h, trig_uu]
      else
        simp [h]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (u t) * Matrix.rotaryOn u v β k (v s))]
      simp_rw [rotaryOn_uu hu huv α, rotaryOn_uv hu hv huv β, rotaryOn_vu hu hv huv α,
        rotaryOn_vv hv huv β, sum_mul_ite, rotaryOn_uv hu hv huv (β - α)]
      if h : t = s then
        simp [h, trig_uv]
      else
        simp [h]
  | inr hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (v t) * Matrix.rotaryOn u v β k (u s))]
      simp_rw [rotaryOn_uv hu hv huv α, rotaryOn_uu hu huv β, rotaryOn_vv hv huv α,
        rotaryOn_vu hu hv huv β, sum_mul_ite, rotaryOn_vu hu hv huv (β - α)]
      if h : t = s then
        simp [h, trig_vu]
      else
        simp [h]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (v t) * Matrix.rotaryOn u v β k (v s))]
      simp_rw [rotaryOn_uv hu hv huv α, rotaryOn_uv hu hv huv β, rotaryOn_vv hv huv α,
        rotaryOn_vv hv huv β, sum_mul_ite, rotaryOn_vv hv huv (β - α)]
      if h : t = s then
        simp [h, trig_vv]
      else
        simp [h]

private lemma dot_of
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotaryOn u v α *ᵥ q ⬝ᵥ Matrix.rotaryOn u v β *ᵥ k =
    q ⬝ᵥ Matrix.rotaryOn u v (β - α) *ᵥ k := by
-- proof
  have hmul := rotaryOn_mul_sub hu hv huv hsurj hsum α β
  rw [← hmul, ← Matrix.mulVec_mulVec, dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec (Matrix.rotaryOn u v α) q
    (Matrix.rotaryOn u v β *ᵥ k)).symm

private lemma zero_of
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i)) :
-- imply
  Matrix.rotaryOn u v 0 = 1 := by
-- proof
  ext i j
  cases (hsurj i) with
  | inl hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_uu hu huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.cos_zero]
      if h : t = s then
        simp [h]
      else
        simp [h, hu.eq_iff]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_uv hu hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.sin_zero]
      simp [huv t s]
  | inr hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_vu hu hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.sin_zero]
      have hne : v t ≠ u s := (huv s t).symm
      simp [hne]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_vv hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.cos_zero]
      if h : t = s then
        simp [h]
      else
        simp [h, hv.eq_iff]

private lemma inv_of
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotaryOn u v φ)⁻¹ = (Matrix.rotaryOn u v φ)ᵀ := by
-- proof
  apply Matrix.inv_eq_left_inv
  have hmul := rotaryOn_mul_sub hu hv huv hsurj hsum φ φ
  have hsub : (φ - φ) = 0 := by
    funext t
    simp
  rw [hmul, hsub, zero_of hu hv huv hsurj]

private lemma rotary_dot
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary α *ᵥ q ⬝ᵥ Matrix.rotary β *ᵥ k =
    q ⬝ᵥ Matrix.rotary (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary] using
    dot_of (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)
      (sum_half (d := d)) α β q k

private lemma rotary_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary (-φ) = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using rotaryOn_neg (u := Fin.castAdd d) (v := Fin.natAdd d) φ

private lemma rotary_zero
  {d : ℕ} :
-- imply
  Matrix.rotary (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary] using
    zero_of (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)

private lemma rotary_inv
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary φ)⁻¹ = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using
    inv_of (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)
      (sum_half (d := d)) φ

private lemma rotary'_dot
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary' α *ᵥ q ⬝ᵥ Matrix.rotary' β *ᵥ k =
    q ⬝ᵥ Matrix.rotary' (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary'] using
    dot_of (ropeEven_inj d) (ropeOdd_inj d) (rope_disj d) (rope_surj d) (sum_rope d) α β q k

private lemma rotary'_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary' (-φ) = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using rotaryOn_neg (u := Matrix.ropeEven d) (v := Matrix.ropeOdd d) φ

private lemma rotary'_zero
  {d : ℕ} :
-- imply
  Matrix.rotary' (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary'] using
    zero_of (ropeEven_inj d) (ropeOdd_inj d) (rope_disj d) (rope_surj d)

private lemma rotary'_inv
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary' φ)⁻¹ = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using
    inv_of (ropeEven_inj d) (ropeOdd_inj d) (rope_disj d) (rope_surj d) (sum_rope d) φ

/--
Rotary attention collapses to relative angles when each frequency row is linear in the token index.

The usual schedule is `θ[i][j] = λ * i / b ^ (j / d)`. Here that is weakened to `θ[i][j] = τ j * i`.
`Matrix.rotary` is the half-split rotation, with planes `(j, j + d)`.
-/
@[path]
private lemma main
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    rotary_dot (fun φ => (rotary_neg φ).trans (rotary_inv φ).symm) rotary_zero Q K V

/-- Adjacent-pair form of the same identity. `Matrix.rotary'` rotates planes `(2j, 2j + 1)`. -/
@[path]
private lemma interleave
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary'
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    rotary'_dot (fun φ => (rotary'_neg φ).trans (rotary'_inv φ).symm) rotary'_zero Q K V


-- created on 2023-06-09
-- updated on 2026-11-21
