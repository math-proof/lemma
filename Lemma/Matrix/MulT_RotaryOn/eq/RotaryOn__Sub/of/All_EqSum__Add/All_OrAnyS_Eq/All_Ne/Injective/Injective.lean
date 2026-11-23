import Def.LinearAlgebra.Matrix.Rotary
import Initialize.Tactic.Attr.Basic
import Mathlib
open scoped Matrix


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

private lemma trig_uu
-- given
  (a b : ℝ) :
-- imply
  Real.cos a * Real.cos b + Real.sin a * Real.sin b = Real.cos (b - a) := by
-- proof
  rw [Real.cos_sub]
  ring

private lemma trig_uv
-- given
  (a b : ℝ) :
-- imply
  -(Real.cos a * Real.sin b) + Real.sin a * Real.cos b = -Real.sin (b - a) := by
-- proof
  rw [Real.sin_sub]
  ring

private lemma trig_vu
-- given
  (a b : ℝ) :
-- imply
  -(Real.sin a * Real.cos b) + Real.cos a * Real.sin b = Real.sin (b - a) := by
-- proof
  rw [Real.sin_sub]
  ring

private lemma trig_vv
-- given
  (a b : ℝ) :
-- imply
  Real.sin a * Real.sin b + Real.cos a * Real.cos b = Real.cos (b - a) := by
-- proof
  rw [Real.cos_sub]
  ring

/-- Left-transposing a rotation multiplies the angles: `(R α)ᵀ * R β = R (β - α)`. -/
@[path]
private lemma main
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


-- created on 2026-11-23
