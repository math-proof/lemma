import Def.LinearAlgebra.Matrix.Rotary
import Initialize.Tactic.Attr.Basic
import Mathlib


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

/-- The zero-angle rotation is the identity. -/
@[path]
private lemma main
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), ∃ t : Fin d, i ∈ ({u t, v t} : Set (Fin (d + d)))) :
-- imply
  Matrix.rotaryOn u v 0 = 1 := by
-- proof
  ext i j
  obtain ⟨t, ht⟩ := hsurj i
  obtain ⟨s, hs⟩ := hsurj j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht hs
  obtain rfl | rfl := ht <;> obtain rfl | rfl := hs
  ·
    rw [rotaryOn_uu hu huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.cos_zero]
    if h : t = s then
      simp [h]
    else
      simp [h, hu.eq_iff]
  ·
    rw [rotaryOn_uv hu hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.sin_zero]
    simp [huv t s]
  ·
    rw [rotaryOn_vu hu hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.sin_zero]
    have hne : v t ≠ u s := (huv s t).symm
    simp [hne]
  ·
    rw [rotaryOn_vv hv huv (0 : Fin d → ℝ) t s, Matrix.one_apply, Pi.zero_apply, Real.cos_zero]
    if h : t = s then
      simp [h]
    else
      simp [h, hv.eq_iff]


-- created on 2026-11-23
