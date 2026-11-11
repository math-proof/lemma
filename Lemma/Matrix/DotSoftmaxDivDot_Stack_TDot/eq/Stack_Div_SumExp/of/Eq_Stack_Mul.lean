import Def.Analysis.Matrix.Softmax
import Def.LinearAlgebra.Matrix.Rotary
import Instance.Analysis.SpecialFunctions.Exponential
import Instance.LinearAlgebra.Matrix.Div
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Instance.LinearAlgebra.Matrix.GetElem
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
  Matrix.rotaryOn u v (fun t => -θ t) = (Matrix.rotaryOn u v θ)ᵀ := by
-- proof
  ext i j
  have hL :
    Matrix.rotaryOn u v (fun t => -θ t) i j =
      (∑ t : Fin d, if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if i = u t ∧ j = v t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = u t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.rotaryOn, Matrix.of_apply, Finset.sum_add_distrib, Real.cos_neg,
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
    Matrix.rotaryOn u v (fun t => β t - α t) := by
-- proof
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply]
  cases hsurj i with
  | inl hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (u t) * Matrix.rotaryOn u v β k (u s))]
      simp_rw [rotaryOn_uu hu huv α, rotaryOn_uu hu huv β, rotaryOn_vu hu hv huv α,
        rotaryOn_vu hu hv huv β, sum_mul_ite, rotaryOn_uu hu huv (fun x => β x - α x)]
      if h : t = s then
        simp [h, trig_uu]
      else
        simp [h]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (u t) * Matrix.rotaryOn u v β k (v s))]
      simp_rw [rotaryOn_uu hu huv α, rotaryOn_uv hu hv huv β, rotaryOn_vu hu hv huv α,
        rotaryOn_vv hv huv β, sum_mul_ite, rotaryOn_uv hu hv huv (fun x => β x - α x)]
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
        rotaryOn_vu hu hv huv β, sum_mul_ite, rotaryOn_vu hu hv huv (fun x => β x - α x)]
      if h : t = s then
        simp [h, trig_vu]
      else
        simp [h]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [hsum (fun k => Matrix.rotaryOn u v α k (v t) * Matrix.rotaryOn u v β k (v s))]
      simp_rw [rotaryOn_uv hu hv huv α, rotaryOn_uv hu hv huv β, rotaryOn_vv hv huv α,
        rotaryOn_vv hv huv β, sum_mul_ite, rotaryOn_vv hv huv (fun x => β x - α x)]
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
  dotProduct ((Matrix.rotaryOn u v α) *ᵥ q) ((Matrix.rotaryOn u v β) *ᵥ k) =
    dotProduct q ((Matrix.rotaryOn u v (fun t => β t - α t)) *ᵥ k) := by
-- proof
  have hmul := rotaryOn_mul_sub hu hv huv hsurj hsum α β
  rw [← hmul, ← Matrix.mulVec_mulVec, dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec (Matrix.rotaryOn u v α) q
    ((Matrix.rotaryOn u v β) *ᵥ k)).symm

private lemma zero_of
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i)) :
-- imply
  Matrix.rotaryOn u v (fun _ => (0 : ℝ)) = 1 := by
-- proof
  ext i j
  cases hsurj i with
  | inl hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_uu hu huv _ t s, Matrix.one_apply, Real.cos_zero]
      if h : t = s then
        simp [h]
      else
        simp [h, hu.eq_iff]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_uv hu hv huv _ t s, Matrix.one_apply, Real.sin_zero]
      simp [huv t s]
  | inr hi =>
    obtain ⟨t, rfl⟩ := hi
    cases hsurj j with
    | inl hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_vu hu hv huv _ t s, Matrix.one_apply, Real.sin_zero]
      have hne : v t ≠ u s := (huv s t).symm
      simp [hne]
    | inr hj =>
      obtain ⟨s, rfl⟩ := hj
      rw [rotaryOn_vv hv huv _ t s, Matrix.one_apply, Real.cos_zero]
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
  have hsub : (fun t => φ t - φ t) = fun _ => (0 : ℝ) := by
    funext t
    ring
  rw [hmul, hsub, zero_of hu hv huv hsurj]

private lemma rotary_dot
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  dotProduct ((Matrix.rotary α) *ᵥ q) ((Matrix.rotary β) *ᵥ k) =
    dotProduct q ((Matrix.rotary (fun t => β t - α t)) *ᵥ k) := by
-- proof
  simpa [Matrix.rotary] using
    dot_of (Fin.castAdd_injective d d) (natAdd_inj d) (half_disj d) (half_surj d)
      (sum_half (d := d)) α β q k

private lemma rotary_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary (fun t => -φ t) = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using rotaryOn_neg (u := Fin.castAdd d) (v := Fin.natAdd d) φ

private lemma rotary_zero
  {d : ℕ} :
-- imply
  Matrix.rotary (fun (_ : Fin d) => (0 : ℝ)) = 1 := by
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
  dotProduct ((Matrix.rotary' α) *ᵥ q) ((Matrix.rotary' β) *ᵥ k) =
    dotProduct q ((Matrix.rotary' (fun t => β t - α t)) *ᵥ k) := by
-- proof
  simpa [Matrix.rotary'] using
    dot_of (ropeEven_inj d) (ropeOdd_inj d) (rope_disj d) (rope_surj d) (sum_rope d) α β q k

private lemma rotary'_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary' (fun t => -φ t) = (Matrix.rotary' φ)ᵀ := by
-- proof
  simpa [Matrix.rotary'] using rotaryOn_neg (u := Matrix.ropeEven d) (v := Matrix.ropeOdd d) φ

private lemma rotary'_zero
  {d : ℕ} :
-- imply
  Matrix.rotary' (fun (_ : Fin d) => (0 : ℝ)) = 1 := by
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

private lemma theta_apply
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (p : Fin n)
  (t : Fin d) :
-- imply
  θ[p][t] = τ t * (p : ℝ) := by
-- proof
  simp [hθ, Pi.smul_apply]
  ring

private lemma rel_linear
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
  {rot : (Fin d → ℝ) → ℝ ^ [d + d, d + d]}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (hneg : ∀ φ : Fin d → ℝ, rot (fun t => -φ t) = (rot φ)ᵀ)
  (hzero : rot (fun _ => (0 : ℝ)) = 1)
  (hinv : ∀ φ : Fin d → ℝ, (rot φ)⁻¹ = (rot φ)ᵀ)
  (i k : Fin n) :
-- imply
  rot (fun t => (θ[k] : Fin d → ℝ) t - (θ[i] : Fin d → ℝ) t) =
    Matrix.signPow (rot (θ[(⟨((k : ℤ) - (i : ℤ)).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ))
      (((k : ℤ) - (i : ℤ)).sign) := by
-- proof
  if hlt : (k : ℕ) < (i : ℕ) then
    have hsign : ((k : ℤ) - (i : ℤ)).sign = -1 := by
      apply Int.sign_eq_neg_one_of_neg
      omega
    have hle : (k : ℕ) ≤ (i : ℕ) := Nat.le_of_lt hlt
    have habs : ((k : ℤ) - (i : ℤ)).natAbs = (i : ℕ) - (k : ℕ) := by
      have hsub : (k : ℤ) - (i : ℤ) = -((i : ℤ) - (k : ℤ)) := by ring
      rw [hsub, Int.natAbs_neg]
      have hcoe (p : Fin n) : (p : ℤ) = ((p : ℕ) : ℤ) := by simp
      rw [hcoe i, hcoe k, (Int.ofNat_sub hle).symm]
      simp
    rw [hsign]
    simp only [Matrix.signPow]
    rw [hinv, ← hneg]
    apply congrArg
    funext t
    simp only [getElem_apply, ← getElem_getElem, theta_apply hθ]
    rw [show ((k : ℤ) - (i : ℤ)).natAbs = (i : ℕ) - (k : ℕ) from habs]
    rw [Nat.cast_sub hle]
    ring
  else if heq : (k : ℕ) = (i : ℕ) then
    have hsign : ((k : ℤ) - (i : ℤ)).sign = 0 := by
      have hsub : (k : ℤ) - (i : ℤ) = 0 := by omega
      simp [hsub]
    rw [hsign]
    simp only [Matrix.signPow, ite_true]
    rw [← hzero]
    apply congrArg
    funext t
    simp only [getElem_apply, ← getElem_getElem, theta_apply hθ, heq]
    ring
  else
    have hgt : (i : ℕ) < (k : ℕ) := by
      omega
    have hle : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt hgt
    have hsign : ((k : ℤ) - (i : ℤ)).sign = 1 := by
      apply Int.sign_eq_one_of_pos
      omega
    have habs : ((k : ℤ) - (i : ℤ)).natAbs = (k : ℕ) - (i : ℕ) := by
      omega
    rw [hsign]
    simp only [Matrix.signPow]
    apply congrArg
    funext t
    simp only [getElem_apply, ← getElem_getElem, theta_apply hθ]
    rw [show ((k : ℤ) - (i : ℤ)).natAbs = (k : ℕ) - (i : ℕ) from habs]
    rw [Nat.cast_sub hle]
    ring

private lemma attention
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
  {rot : (Fin d → ℝ) → ℝ ^ [d + d, d + d]}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (hdot : ∀ (α β : Fin d → ℝ) (q k : Fin (d + d) → ℝ),
    dotProduct ((rot α) *ᵥ q) ((rot β) *ᵥ k) =
      dotProduct q ((rot (fun t => β t - α t)) *ᵥ k))
  (hneg : ∀ φ : Fin d → ℝ, rot (fun t => -φ t) = (rot φ)ᵀ)
  (hzero : rot (fun _ => (0 : ℝ)) = 1)
  (hinv : ∀ φ : Fin d → ℝ, (rot φ)⁻¹ = (rot φ)ᵀ)
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let R (i : Fin n) := rot (θ[i])
  let Rel (i k : Fin n) :=
    Matrix.signPow (R ⟨((k : ℤ) - (i : ℤ)).natAbs, by omega⟩) (((k : ℤ) - (i : ℤ)).sign)
  (([i < n, a < d + d] ((R i) *ᵥ (Q i)) a) *
      ([i < n, a < d + d] ((R i) *ᵥ (K i)) a)ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n, j < d + d]
      (∑ k : Fin n, V k j * Exp.exp (dotProduct (Q i) ((Rel i k) *ᵥ (K k)) / √(d + d : ℝ))) /
        ∑ k : Fin n, Exp.exp
          (dotProduct ((R i) *ᵥ (Q i)) ((R k) *ᵥ (K k)) / √(d + d : ℝ)) := by
-- proof
  intro R Rel
  ext i j
  simp only [Matrix.ofFun_apply]
  let RQ : ℝ ^ [n, d + d] := [p < n, a < d + d] ((R p) *ᵥ (Q p)) a
  let RK : ℝ ^ [n, d + d] := [p < n, a < d + d] ((R p) *ᵥ (K p)) a
  let S : ℝ ^ [n, n] := RQ * RKᵀ / √(d + d : ℝ)
  have hRQ (p : Fin n) : RQ p = (R p) *ᵥ (Q p) := by
    ext a
    simp [RQ]
  have hRK (p : Fin n) : RK p = (R p) *ᵥ (K p) := by
    ext a
    simp [RK]
  have hS : (([p < n, a < d + d] ((R p) *ᵥ (Q p)) a) *
      ([p < n, a < d + d] ((R p) *ᵥ (K p)) a)ᵀ / √(d + d : ℝ)) = S := by
    simp [S, RQ, RK]
  rw [hS]
  have hsm (k : Fin n) :
    (S.softmax) i k = Exp.exp (S i k) / ∑ k' : Fin n, Exp.exp (S i k') := by
    unfold Matrix.softmax
    rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0)]
    rw [ite_eq_left (by decide : (1 : ℕ) = 1)]
    simp [Matrix.of_apply]
  have hprod (k : Fin n) : (RQ * RKᵀ) i k = dotProduct (RQ i) (RK k) := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  have hentry (k : Fin n) :
    S i k = dotProduct ((R i) *ᵥ (Q i)) ((R k) *ᵥ (K k)) / √(d + d : ℝ) := by
    simp [S, Matrix.div_apply, hprod, hRQ, hRK]
  have hRel (k : Fin n) :
      Rel i k = rot (fun t => (θ[k] : Fin d → ℝ) t - (θ[i] : Fin d → ℝ) t) := by
    simpa [Rel, R] using (rel_linear hθ hneg hzero hinv i k).symm
  have hscore (k : Fin n) :
    S i k = dotProduct (Q i) ((Rel i k) *ᵥ (K k)) / √(d + d : ℝ) := by
    rw [hentry k, hdot (θ[i]) (θ[k]) (Q i) (K k), ← hRel k]
  rw [Matrix.mul_apply]
  simp_rw [hsm, ← hscore]
  have hden :
    (∑ k : Fin n, Exp.exp
        (dotProduct ((R i) *ᵥ (Q i)) ((R k) *ᵥ (K k)) / √(d + d : ℝ))) =
      ∑ k : Fin n, Exp.exp (S i k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry k]
  rw [hden]
  let D : ℝ := ∑ k : Fin n, Exp.exp (S i k)
  have hdiv :
    (∑ k : Fin n, Exp.exp (S i k) / D * V k j) =
      (∑ k : Fin n, V k j * Exp.exp (S i k)) / D := by
    have hterm (k : Fin n) :
      Exp.exp (S i k) / D * V k j = V k j * Exp.exp (S i k) / D := by
      rw [div_mul_eq_mul_div, mul_comm]
    simp_rw [hterm]
    exact (Finset.sum_div Finset.univ (fun k => V k j * Exp.exp (S i k)) D).symm
  simpa [D, Matrix.mul_apply] using hdiv

/--
Rotary attention collapses to relative angles when each frequency row is linear in the token index.

The usual schedule is `θ[i][j] = λ * i / b ^ (j / d)`. Here that is weakened to `θ[i][j] = τ j * i`.
`Matrix.rotary` is the half-split rotation, with planes `(j, j + d)`.
-/
@[path]
private lemma main
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let R (i : Fin n) := Matrix.rotary (θ[i])
  let Rel (i k : Fin n) :=
    Matrix.signPow (R ⟨((k : ℤ) - (i : ℤ)).natAbs, by omega⟩) (((k : ℤ) - (i : ℤ)).sign)
  (([i < n, a < d + d] ((R i) *ᵥ (Q i)) a) *
      ([i < n, a < d + d] ((R i) *ᵥ (K i)) a)ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n, j < d + d]
      (∑ k : Fin n, V k j * Exp.exp (dotProduct (Q i) ((Rel i k) *ᵥ (K k)) / √(d + d : ℝ))) /
        ∑ k : Fin n, Exp.exp
          (dotProduct ((R i) *ᵥ (Q i)) ((R k) *ᵥ (K k)) / √(d + d : ℝ)) := by
-- proof
  apply attention hθ rotary_dot rotary_neg rotary_zero rotary_inv Q K V

/-- Adjacent-pair form of the same identity. `Matrix.rotary'` rotates planes `(2j, 2j + 1)`. -/
@[path]
private lemma interleave
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let R (i : Fin n) := Matrix.rotary' (θ[i])
  let Rel (i k : Fin n) :=
    Matrix.signPow (R ⟨((k : ℤ) - (i : ℤ)).natAbs, by omega⟩) (((k : ℤ) - (i : ℤ)).sign)
  (([i < n, a < d + d] ((R i) *ᵥ (Q i)) a) *
      ([i < n, a < d + d] ((R i) *ᵥ (K i)) a)ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n, j < d + d]
      (∑ k : Fin n, V k j * Exp.exp (dotProduct (Q i) ((Rel i k) *ᵥ (K k)) / √(d + d : ℝ))) /
        ∑ k : Fin n, Exp.exp
          (dotProduct ((R i) *ᵥ (Q i)) ((R k) *ᵥ (K k)) / √(d + d : ℝ)) := by
-- proof
  apply attention hθ rotary'_dot rotary'_neg rotary'_zero rotary'_inv Q K V


-- created on 2023-06-09
-- updated on 2026-11-08
