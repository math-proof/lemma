import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Nontrivial1234_3412Classes
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ntRC_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
  ntRC σ i = (σ i.rev).rev := by
  simp [ntRC, Equiv.Perm.mul_apply, Fin.revPerm_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRev_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRev_mul_self (n : ℕ) :
  (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
  apply Equiv.Perm.ext
  intro i
  simp [Equiv.Perm.mul_apply, Fin.revPerm_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRC_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  Equiv.Perm.sign (ntRC σ) = Equiv.Perm.sign σ := by
  have hs : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) *
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = 1 := by
    rw [← Equiv.Perm.sign_mul, ntRev_mul_self, Equiv.Perm.sign_one]
  rw [ntRC, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul]
  calc
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) * Equiv.Perm.sign σ *
      Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) *
        Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) * Equiv.Perm.sign σ := by
          ac_rfl
    _ = Equiv.Perm.sign σ := by rw [hs, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntE_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntE_symm {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ ntE m) :
  σ.symm ∈ ntE m := by
  constructor
  · intro h
    apply hσ.2
    simpa using (congrArg σ h).symm
  · intro h
    apply hσ.1
    simpa using (congrArg σ h).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntE_rc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntE_rc {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ ntE m) :
  ntRC σ ∈ ntE m := by
  constructor
  · intro h
    apply hσ.2
    simpa [ntRC_apply] using congrArg Fin.rev h
  · intro h
    apply hσ.1
    simpa [ntRC_apply] using congrArg Fin.rev h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInc5_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInc5_symm {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : ntInc5 n σ) :
  ntInc5 n σ.symm := by
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, sab, sbc, scd, sde⟩ := h
  refine ⟨σ a, σ b, σ c, σ d, σ e, sab, sbc, scd, sde, ?_, ?_, ?_, ?_⟩
  · simpa using hab
  · simpa using hbc
  · simpa using hcd
  · simpa using hde

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInc5_rc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInc5_rc {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : ntInc5 n σ) :
  ntInc5 n (ntRC σ) := by
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, sab, sbc, scd, sde⟩ := h
  refine ⟨e.rev, d.rev, c.rev, b.rev, a.rev,
    (Fin.rev_lt_rev).2 hde, (Fin.rev_lt_rev).2 hcd, (Fin.rev_lt_rev).2 hbc,
    (Fin.rev_lt_rev).2 hab, ?_, ?_, ?_, ?_⟩
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 sde
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 scd
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 sbc
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 sab

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_eq {n : ℕ} {σ τ : Equiv.Perm (Fin n)} {i1 i2 i3 i4 : Fin n}
  (h12 : i1.val < i2.val) (h23 : i2.val < i3.val) (h34 : i3.val < i4.val)
  (s12 : σ i1 < σ i2) (s23 : σ i2 < σ i3) (s34 : σ i3 < σ i4)
  (t1 : τ i1 = σ i3) (t2 : τ i2 = σ i4) (t3 : τ i3 = σ i1) (t4 : τ i4 = σ i2)
  (hrest : ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j) :
  τ = σ * Equiv.swap i1 i3 * Equiv.swap i2 i4 := by
  have d12 : i1 ≠ i2 := by intro h; rw [h] at h12; exact lt_irrefl _ h12
  have d13 : i1 ≠ i3 := by intro h; rw [h] at h12; exact absurd (lt_trans h12 h23) (lt_irrefl _)
  have d14 : i1 ≠ i4 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 (lt_trans h23 h34)) (lt_irrefl _)
  have d23 : i2 ≠ i3 := by intro h; rw [h] at h23; exact lt_irrefl _ h23
  have d24 : i2 ≠ i4 := by intro h; rw [h] at h23; exact absurd (lt_trans h23 h34) (lt_irrefl _)
  have d34 : i3 ≠ i4 := by intro h; rw [h] at h34; exact lt_irrefl _ h34
  apply Equiv.ext
  intro j
  by_cases hj1 : j = i1
  · subst hj1
    rw [t1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne d12 d14, Equiv.swap_apply_left]
  · by_cases hj2 : j = i2
    · subst hj2
      rw [t2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d34)]
    · by_cases hj3 : j = i3
      · subst hj3
        rw [t3, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) d34, Equiv.swap_apply_right]
      · by_cases hj4 : j = i4
        · subst hj4
          rw [t4, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) d23]
        · rw [hrest j hj1 hj2 hj3 hj4, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hj2 hj4, Equiv.swap_apply_of_ne_of_ne hj1 hj3]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_symm {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
  ntMove n σ.symm τ.symm := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34,
    t1, t2, t3, t4, hrest⟩ := h
  refine ⟨σ i1, σ i2, σ i3, σ i4, s12, s23, s34, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h12
  · simpa using h23
  · simpa using h34
  · rw [← t3, τ.symm_apply_apply, σ.symm_apply_apply]
  · rw [← t4, τ.symm_apply_apply, σ.symm_apply_apply]
  · rw [← t1, τ.symm_apply_apply, σ.symm_apply_apply]
  · rw [← t2, τ.symm_apply_apply, σ.symm_apply_apply]
  · intro j hj1 hj2 hj3 hj4
    have hk1 : τ.symm j ≠ i1 := by
      intro hk
      apply hj3
      rw [← t1, ← hk, τ.apply_symm_apply]
    have hk2 : τ.symm j ≠ i2 := by
      intro hk
      apply hj4
      rw [← t2, ← hk, τ.apply_symm_apply]
    have hk3 : τ.symm j ≠ i3 := by
      intro hk
      apply hj1
      rw [← t3, ← hk, τ.apply_symm_apply]
    have hk4 : τ.symm j ≠ i4 := by
      intro hk
      apply hj2
      rw [← t4, ← hk, τ.apply_symm_apply]
    apply σ.injective
    rw [σ.apply_symm_apply, ← hrest _ hk1 hk2 hk3 hk4, τ.apply_symm_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_rc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_rc {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
  ntMove n (ntRC σ) (ntRC τ) := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34,
    t1, t2, t3, t4, hrest⟩ := h
  refine ⟨i4.rev, i3.rev, i2.rev, i1.rev,
    (Fin.rev_lt_rev).2 h34, (Fin.rev_lt_rev).2 h23, (Fin.rev_lt_rev).2 h12,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 s34
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 s23
  · simpa [ntRC_apply] using (Fin.rev_lt_rev).2 s12
  · simp [ntRC_apply, t4]
  · simp [ntRC_apply, t3]
  · simp [ntRC_apply, t2]
  · simp [ntRC_apply, t1]
  · intro j hj1 hj2 hj3 hj4
    have hk1 : j.rev ≠ i1 := by
      intro hk
      apply hj4
      simpa using congrArg Fin.rev hk
    have hk2 : j.rev ≠ i2 := by
      intro hk
      apply hj3
      simpa using congrArg Fin.rev hk
    have hk3 : j.rev ≠ i3 := by
      intro hk
      apply hj2
      simpa using congrArg Fin.rev hk
    have hk4 : j.rev ≠ i4 := by
      intro hk
      apply hj1
      simpa using congrArg Fin.rev hk
    simp only [ntRC_apply]
    rw [hrest _ hk1 hk2 hk3 hk4]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_sign {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
  Equiv.Perm.sign τ = Equiv.Perm.sign σ := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4, hrest⟩ := h
  have d13 : i1 ≠ i3 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 h23) (lt_irrefl _)
  have d24 : i2 ≠ i4 := by
    intro h; rw [h] at h23; exact absurd (lt_trans h23 h34) (lt_irrefl _)
  have heq := ntMove_eq h12 h23 h34 s12 s23 s34 t1 t2 t3 t4 hrest
  rw [heq, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap d13,
    Equiv.Perm.sign_swap d24]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_pat3412](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_pat3412 {n : ℕ} {σ τ : Equiv.Perm (Fin n)} {i1 i2 i3 i4 : Fin n}
  (_h12 : i1.val < i2.val) (_h23 : i2.val < i3.val) (_h34 : i3.val < i4.val)
  (s12 : σ i1 < σ i2) (s23 : σ i2 < σ i3) (s34 : σ i3 < σ i4)
  (t1 : τ i1 = σ i3) (t2 : τ i2 = σ i4) (t3 : τ i3 = σ i1) (t4 : τ i4 = σ i2) :
  τ i3 < τ i4 ∧ τ i4 < τ i1 ∧ τ i1 < τ i2 := by
  rw [t1, t2, t3, t4]
  exact ⟨s12, s23, s34⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_of_1234](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_of_1234 {n : ℕ} {σ : Equiv.Perm (Fin n)} {i1 i2 i3 i4 : Fin n}
  (h12 : i1.val < i2.val) (h23 : i2.val < i3.val) (h34 : i3.val < i4.val)
  (s12 : σ i1 < σ i2) (s23 : σ i2 < σ i3) (s34 : σ i3 < σ i4) :
  ntMove n σ (σ * Equiv.swap i1 i3 * Equiv.swap i2 i4) := by
  have d12 : i1 ≠ i2 := by intro h; rw [h] at h12; exact lt_irrefl _ h12
  have d13 : i1 ≠ i3 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 h23) (lt_irrefl _)
  have d14 : i1 ≠ i4 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 (lt_trans h23 h34)) (lt_irrefl _)
  have d23 : i2 ≠ i3 := by intro h; rw [h] at h23; exact lt_irrefl _ h23
  have d24 : i2 ≠ i4 := by
    intro h; rw [h] at h23; exact absurd (lt_trans h23 h34) (lt_irrefl _)
  have d34 : i3 ≠ i4 := by intro h; rw [h] at h34; exact lt_irrefl _ h34
  have e1 : (σ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i1 = σ i3 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne d12 d14,
      Equiv.swap_apply_left]
  have e2 : (σ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i2 = σ i4 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d34)]
  have e3 : (σ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i3 = σ i1 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) d34,
      Equiv.swap_apply_right]
  have e4 : (σ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i4 = σ i2 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) d23]
  refine ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, e1, e2, e3, e4, ?_⟩
  intro j hj1 hj2 hj3 hj4
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hj2 hj4,
    Equiv.swap_apply_of_ne_of_ne hj1 hj3]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_of_3412](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_of_3412 {n : ℕ} {τ : Equiv.Perm (Fin n)} {i1 i2 i3 i4 : Fin n}
  (h12 : i1.val < i2.val) (h23 : i2.val < i3.val) (h34 : i3.val < i4.val)
  (s31 : τ i3 < τ i4) (s42 : τ i4 < τ i1) (s13 : τ i1 < τ i2) :
  ntMove n (τ * Equiv.swap i1 i3 * Equiv.swap i2 i4) τ := by
  have d12 : i1 ≠ i2 := by intro h; rw [h] at h12; exact lt_irrefl _ h12
  have d13 : i1 ≠ i3 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 h23) (lt_irrefl _)
  have d14 : i1 ≠ i4 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 (lt_trans h23 h34)) (lt_irrefl _)
  have d23 : i2 ≠ i3 := by intro h; rw [h] at h23; exact lt_irrefl _ h23
  have d24 : i2 ≠ i4 := by
    intro h; rw [h] at h23; exact absurd (lt_trans h23 h34) (lt_irrefl _)
  have d34 : i3 ≠ i4 := by intro h; rw [h] at h34; exact lt_irrefl _ h34
  have e1 : (τ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i1 = τ i3 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne d12 d14,
      Equiv.swap_apply_left]
  have e2 : (τ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i2 = τ i4 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d34)]
  have e3 : (τ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i3 = τ i1 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) d34,
      Equiv.swap_apply_right]
  have e4 : (τ * Equiv.swap i1 i3 * Equiv.swap i2 i4) i4 = τ i2 := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) d23]
  refine ⟨i1, i2, i3, i4, h12, h23, h34, ?_, ?_, ?_, e3.symm, e4.symm, e1.symm,
    e2.symm, ?_⟩
  · rw [e1, e2]; exact s31
  · rw [e2, e3]; exact s42
  · rw [e3, e4]; exact s13
  · intro j hj1 hj2 hj3 hj4
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hj2 hj4,
      Equiv.swap_apply_of_ne_of_ne hj1 hj3]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_ne {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
  σ ≠ τ := by
  obtain ⟨i1, i2, i3, i4, h12, h23, -, -, -, -, t1, -, -, -, -⟩ := h
  intro heq
  have d13 : i1 ≠ i3 := by
    intro h; rw [h] at h12; exact absurd (lt_trans h12 h23) (lt_irrefl _)
  have e : σ i1 = τ i1 := by rw [heq]
  exact d13 (σ.injective (e.trans t1))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_sign {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
  (h : Relation.EqvGen (ntMove n) σ τ) :
  Equiv.Perm.sign σ = Equiv.Perm.sign τ := by
  induction h with
  | rel _ _ h => exact (ntMove_sign h).symm
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_symm {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
  (h : Relation.EqvGen (ntMove n) σ τ) :
  Relation.EqvGen (ntMove n) σ.symm τ.symm := by
  induction h with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ (ntMove_symm h)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_rc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_rc {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
  (h : Relation.EqvGen (ntMove n) σ τ) :
  Relation.EqvGen (ntMove n) (ntRC σ) (ntRC τ) := by
  induction h with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ (ntMove_rc h)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_pat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_pat {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
  (h : ntMove n σ τ ∨ ntMove n τ σ) : ntPat n σ := by
  obtain h | h := h
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, -, -, -, -, -⟩ := h
    exact Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4, -⟩ := h
    refine Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, ?_, ?_, ?_⟩
    · rw [t3, t4]; exact s12
    · rw [t4, t1]; exact s23
    · rw [t1, t2]; exact s34

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCls_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCls_eq {α : Type*} {r : α → α → Prop} {x y : α} :
  ntCls r x = ntCls r y ↔ Relation.EqvGen r x y := by
  constructor
  · intro h
    have hmem : x ∈ ntCls r y := by
      rw [← h]
      exact Relation.EqvGen.refl x
    simp only [ntCls, Set.mem_ofPred_eq] at hmem
    exact Relation.EqvGen.symm y x hmem
  · intro h
    ext z
    simp only [ntCls, Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact Relation.EqvGen.trans y x z (Relation.EqvGen.symm x y h) hz
    · intro hz
      exact Relation.EqvGen.trans x y z h hz

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntNcl_eq_of_reps](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntNcl_eq_of_reps {α : Type*} [Finite α] {r : α → α → Prop}
  {S : Set α} {m : ℕ} {x : Fin m → α}
  (hxS : ∀ k, x k ∈ S)
  (hcard : ∀ k, 1 < Nat.card ↥(ntCls r (x k)))
  (hne : ∀ k l, k ≠ l → ¬Relation.EqvGen r (x k) (x l))
  (hcov : ∀ z ∈ S, 1 < Nat.card ↥(ntCls r z) → ∃ k, Relation.EqvGen r z (x k)) :
  ntncl r S = m := by
  have hinj : Function.Injective (ntRepFun r S x hxS hcard) := by
    intro k l hkl
    have hval : ntCls r (x k) = ntCls r (x l) := congrArg Subtype.val hkl
    by_contra hnekl
    exact hne k l hnekl ((ntCls_eq.mp hval))
  have hsurj : Function.Surjective (ntRepFun r S x hxS hcard) := by
    intro C
    obtain ⟨D, z, hzS, hCz, hcardz⟩ := C
    have hcardz' : 1 < Nat.card ↥(ntCls r z) := by
      rwa [← hCz]
    obtain ⟨k, hkz⟩ := hcov z hzS hcardz'
    refine ⟨k, ?_⟩
    have hval : ntCls r (x k) = D := by
      rw [hCz]
      exact (ntCls_eq.mpr hkz).symm
    have hval2 : (ntRepFun r S x hxS hcard k).1 = D := hval
    exact Subtype.ext hval2
  have hbij : Function.Bijective (ntRepFun r S x hxS hcard) := ⟨hinj, hsurj⟩
  have hcardF := Nat.card_eq_of_bijective (ntRepFun r S x hxS hcard) hbij
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcardF
  unfold ntncl
  exact hcardF.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntChain_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntChain_symm {α : Type*} {r : α → α → Prop} {a b : α}
  (h : Relation.ReflTransGen (Relation.SymmGen r) a b) :
  Relation.ReflTransGen (Relation.SymmGen r) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h rest ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Relation.SymmGen.symm rest)) ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_chain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_chain {α : Type*} {r : α → α → Prop} {x y : α}
  (h : Relation.EqvGen r x y) : Relation.ReflTransGen (Relation.SymmGen r) x y := by
  induction h with
  | rel a b hab =>
    exact Relation.ReflTransGen.single (Relation.SymmGen.of_rel hab)
  | refl a => exact Relation.ReflTransGen.refl
  | symm a b _ ih => exact ntChain_symm ih
  | trans a b c _ _ ih1 ih2 => exact Relation.ReflTransGen.trans ih1 ih2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_first](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_first {α : Type*} {r : α → α → Prop} {x y : α}
  (h : Relation.EqvGen r x y) (hne : x ≠ y) : ∃ w, r x w ∨ r w x := by
  have hchain := ntEqvGen_chain h
  rw [Relation.ReflTransGen.cases_head_iff] at hchain
  obtain rfl | ⟨c, hc, -⟩ := hchain
  · exact absurd rfl hne
  · exact ⟨c, hc⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntNcl_nontrivial_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntNcl_nontrivial_iff {α : Type*} [Finite α] {r : α → α → Prop}
  {x : α} (hirr : ∀ a b, r a b → a ≠ b) :
  1 < Nat.card ↥(ntCls r x) ↔ ∃ y, r x y ∨ r y x := by
  have hfin : (ntCls r x).Finite := Set.toFinite _
  have hft : Fintype ↥(ntCls r x) := Set.Finite.fintype hfin
  have hiff : 1 < Nat.card ↥(ntCls r x) ↔ Nontrivial ↥(ntCls r x) := by
    rw [@Nat.card_eq_fintype_card _ hft]
    exact @Fintype.one_lt_card_iff_nontrivial _ hft
  constructor
  · intro hlt
    rw [hiff] at hlt
    obtain ⟨a, b, hab⟩ := hlt
    have ha : Relation.EqvGen r x a.1 := by simpa [ntCls] using a.2
    have hb : Relation.EqvGen r x b.1 := by simpa [ntCls] using b.2
    by_cases hax : a.1 = x
    · have hbx : b.1 ≠ x := by
      intro hbx
      exact hab (Subtype.ext (hax.trans hbx.symm))
      exact ntEqvGen_first hb (Ne.symm hbx)
    · exact ntEqvGen_first ha (Ne.symm hax)
  · rintro ⟨y, hy⟩
    have hxy : x ≠ y := by
      obtain h | h := hy
      · exact hirr x y h
      · exact Ne.symm (hirr y x h)
    have hmemx : x ∈ ntCls r x := by simpa [ntCls] using Relation.EqvGen.refl x
    have hmemy : y ∈ ntCls r x := by
      obtain h | h := hy
      · simpa [ntCls] using Relation.EqvGen.rel x y h
      · simpa [ntCls] using Relation.EqvGen.symm y x (Relation.EqvGen.rel y x h)
    have hne : (⟨x, hmemx⟩ : ↥(ntCls r x)) ≠ ⟨y, hmemy⟩ := by
      intro hcon
      exact hxy (congrArg Subtype.val hcon)
    have hnt : Nontrivial ↥(ntCls r x) := ⟨⟨x, hmemx⟩, ⟨y, hmemy⟩, hne⟩
    exact hiff.mpr hnt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_apply_same {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
  ntIns p v ρ p = v := by
  change ntInsFwd p v ρ p = v
  unfold ntInsFwd
  exact Fin.insertNth_apply_same (α := fun _ => Fin (m + 1)) p v _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_apply_succAbove](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_apply_succAbove {m : ℕ} (p v : Fin (m + 1))
  (ρ : Equiv.Perm (Fin m)) (i : Fin m) :
  ntIns p v ρ (p.succAbove i) = v.succAbove (ρ i) := by
  change ntInsFwd p v ρ (p.succAbove i) = v.succAbove (ρ i)
  unfold ntInsFwd
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin (m + 1)) p v _ i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_symm {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
  (ntIns p v ρ).symm = ntIns v p ρ.symm := by
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_mul_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_mul_swap {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m))
  (a b : Fin m) :
  ntIns p v (ρ * Equiv.swap a b) =
    ntIns p v ρ * Equiv.swap (p.succAbove a) (p.succAbove b) := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = p
  · subst x
    rw [ntIns_apply_same, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_succAbove p a) (Fin.ne_succAbove p b),
      ntIns_apply_same]
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxp
    by_cases hia : i = a
    · subst i
      rw [ntIns_apply_succAbove, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, ntIns_apply_succAbove]
    · by_cases hib : i = b
      · subst i
        rw [ntIns_apply_succAbove, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.Perm.mul_apply, Equiv.swap_apply_right, ntIns_apply_succAbove]
      · have hia' : p.succAbove i ≠ p.succAbove a := by
        intro h
        exact hia (Fin.succAbove_right_injective h)
        have hib' : p.succAbove i ≠ p.succAbove b := by
          intro h
          exact hib (Fin.succAbove_right_injective h)
        rw [ntIns_apply_succAbove, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hia hib, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hia' hib', ntIns_apply_succAbove]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRC_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_ins {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
  ntRC (ntIns p v ρ) = ntIns p.rev v.rev (ntRC ρ) := by
  apply Equiv.Perm.ext
  intro x
  by_cases hx : x = p.rev
  · subst x
    simp [ntRC_apply, ntIns_apply_same]
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
    simp [ntRC_apply, ntIns_apply_succAbove, Fin.rev_succAbove]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_injective {m : ℕ} (p v : Fin (m + 1)) :
  Function.Injective (ntIns p v) := by
  intro ρ ρ' h
  apply Equiv.Perm.ext
  intro i
  have h2 : (ntIns p v ρ) (p.succAbove i) = (ntIns p v ρ') (p.succAbove i) := by
    rw [h]
  rw [ntIns_apply_succAbove, ntIns_apply_succAbove] at h2
  exact Fin.succAbove_right_injective h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_exists {m : ℕ} (p v : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1)))
  (hσ : σ p = v) : ∃ ρ, σ = ntIns p v ρ := by
  have hex : ∀ i : Fin m, ∃ j : Fin m, v.succAbove j = σ (p.succAbove i) := by
    intro i
    apply Fin.exists_succAbove_eq
    intro hcon
    have hne : p.succAbove i ≠ p := Fin.succAbove_ne p i
    apply hne
    apply σ.injective
    rw [hcon, hσ]
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro i i' hii
    have e : σ (p.succAbove i) = σ (p.succAbove i') := by
      rw [← hg i, ← hg i', hii]
    have e2 : p.succAbove i = p.succAbove i' := σ.injective e
    exact Fin.succAbove_right_injective e2
  refine ⟨Equiv.ofBijective g hinj.bijective_of_finite, ?_⟩
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = p
  · subst hxp
    rw [hσ, ntIns_apply_same]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxp
    subst hi
    rw [ntIns_apply_succAbove]
    exact (hg i).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_zero_one {m : ℕ} :
  ntIns (0 : Fin (m + 2)) 0 1 = 1 := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = 0
  · subst hxp
    rw [ntIns_apply_same]
    rfl
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxp
    subst hi
    rw [ntIns_apply_succAbove]
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_last_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_last_one {m : ℕ} :
  ntIns (Fin.last (m + 1)) (Fin.last (m + 1)) 1 = 1 := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = Fin.last (m + 1)
  · subst hxp
    rw [ntIns_apply_same]
    rfl
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxp
    subst hi
    rw [ntIns_apply_succAbove, Fin.succAbove_last]
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_zero_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_zero_swap {m : ℕ} (a b : Fin (m + 1)) :
  ntIns (0 : Fin (m + 2)) 0 (Equiv.swap a b) = Equiv.swap a.succ b.succ := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = 0
  · subst hxp
    rw [ntIns_apply_same, Equiv.swap_apply_of_ne_of_ne
      (Ne.symm (Fin.succ_ne_zero a)) (Ne.symm (Fin.succ_ne_zero b))]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxp
    subst hi
    rw [ntIns_apply_succAbove]
    change Fin.succ ((Equiv.swap a b) i) = Equiv.swap a.succ b.succ (Fin.succ i)
    by_cases ha : i = a
    · subst ha
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hb : i = b
      · subst hb
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb,
        Equiv.swap_apply_of_ne_of_ne (fun h => ha (Fin.succ_injective _ h))
          (fun h => hb (Fin.succ_injective _ h))]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_last_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_last_swap {m : ℕ} (a b : Fin (m + 1)) :
  ntIns (Fin.last (m + 1)) (Fin.last (m + 1)) (Equiv.swap a b) =
    Equiv.swap a.castSucc b.castSucc := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxp : x = Fin.last (m + 1)
  · subst hxp
    rw [ntIns_apply_same, Equiv.swap_apply_of_ne_of_ne
      (ne_of_gt (Fin.castSucc_lt_last a)) (ne_of_gt (Fin.castSucc_lt_last b))]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxp
    subst hi
    rw [ntIns_apply_succAbove, Fin.succAbove_last]
    by_cases ha : i = a
    · subst ha
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hb : i = b
      · subst hb
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb,
        Equiv.swap_apply_of_ne_of_ne (fun h => ha (Fin.castSucc_injective _ h))
          (fun h => hb (Fin.castSucc_injective _ h))]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_ins {m : ℕ} (p v : Fin (m + 1)) {ρ ρ' : Equiv.Perm (Fin m)}
  (h : ntMove m ρ ρ') : ntMove (m + 1) (ntIns p v ρ) (ntIns p v ρ') := by
  obtain ⟨j1, j2, j3, j4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4, hrest⟩ := h
  refine ⟨p.succAbove j1, p.succAbove j2, p.succAbove j3, p.succAbove j4, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.lt_def.mp
    ((Fin.strictMono_succAbove p) (Fin.lt_def.mp h12))
  · exact Fin.lt_def.mp
    ((Fin.strictMono_succAbove p) (Fin.lt_def.mp h23))
  · exact Fin.lt_def.mp
    ((Fin.strictMono_succAbove p) (Fin.lt_def.mp h34))
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr s12
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr s23
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr s34
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove, t1]
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove, t2]
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove, t3]
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove, t4]
  · intro x hx1 hx2 hx3 hx4
    by_cases hxp : x = p
    · subst hxp
      rw [ntIns_apply_same, ntIns_apply_same]
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hxp
      subst hj
      have e := hrest j (fun hcon => hx1 (by rw [hcon]))
        (fun hcon => hx2 (by rw [hcon])) (fun hcon => hx3 (by rw [hcon]))
        (fun hcon => hx4 (by rw [hcon]))
      rw [ntIns_apply_succAbove, ntIns_apply_succAbove, e]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_ins {m : ℕ} (p v : Fin (m + 1)) {ρ ρ' : Equiv.Perm (Fin m)}
  (h : Relation.EqvGen (ntMove m) ρ ρ') :
  Relation.EqvGen (ntMove (m + 1)) (ntIns p v ρ) (ntIns p v ρ') := by
  induction h with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ (ntMove_ins p v h)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_descent_zero_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_descent_zero_last {m : ℕ} {ρ ρ' : Equiv.Perm (Fin m)}
  (h : ntMove (m + 1) (ntIns 0 (Fin.last m) ρ) (ntIns 0 (Fin.last m) ρ')) :
  ntMove m ρ ρ' := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4, hrest⟩ := h
  have q1 : i1 ≠ 0 := by
    intro hcon
    have e : (ntIns 0 (Fin.last m) ρ) i1 = Fin.last m := by
      rw [hcon]
      exact ntIns_apply_same _ _ _
    rw [e, Fin.lt_def, Fin.val_last] at s12
    have hb := ((ntIns 0 (Fin.last m) ρ) i2).is_lt
    omega
  have q2 : i2 ≠ 0 := by
    intro hcon
    rw [hcon, Fin.val_zero] at h12
    exact Nat.not_lt_zero _ h12
  have q3 : i3 ≠ 0 := by
    intro hcon
    rw [hcon, Fin.val_zero] at h23
    exact Nat.not_lt_zero _ h23
  have q4 : i4 ≠ 0 := by
    intro hcon
    rw [hcon, Fin.val_zero] at h34
    exact Nat.not_lt_zero _ h34
  obtain ⟨j1, hj1⟩ := Fin.exists_succAbove_eq q1
  obtain ⟨j2, hj2⟩ := Fin.exists_succAbove_eq q2
  obtain ⟨j3, hj3⟩ := Fin.exists_succAbove_eq q3
  obtain ⟨j4, hj4⟩ := Fin.exists_succAbove_eq q4
  refine ⟨j1, j2, j3, j4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hj1, ← hj2] at h12
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h12))
  · rw [← hj2, ← hj3] at h23
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h23))
  · rw [← hj3, ← hj4] at h34
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h34))
  · rw [← hj1, ← hj2, ntIns_apply_succAbove, ntIns_apply_succAbove] at s12
    exact Fin.succAbove_lt_succAbove_iff.mp s12
  · rw [← hj2, ← hj3, ntIns_apply_succAbove, ntIns_apply_succAbove] at s23
    exact Fin.succAbove_lt_succAbove_iff.mp s23
  · rw [← hj3, ← hj4, ntIns_apply_succAbove, ntIns_apply_succAbove] at s34
    exact Fin.succAbove_lt_succAbove_iff.mp s34
  · rw [← hj1, ← hj3, ntIns_apply_succAbove, ntIns_apply_succAbove] at t1
    exact Fin.succAbove_right_injective t1
  · rw [← hj2, ← hj4, ntIns_apply_succAbove, ntIns_apply_succAbove] at t2
    exact Fin.succAbove_right_injective t2
  · rw [← hj3, ← hj1, ntIns_apply_succAbove, ntIns_apply_succAbove] at t3
    exact Fin.succAbove_right_injective t3
  · rw [← hj4, ← hj2, ntIns_apply_succAbove, ntIns_apply_succAbove] at t4
    exact Fin.succAbove_right_injective t4
  · intro j f1 f2 f3 f4
    have g1 : (0 : Fin (m + 1)).succAbove j ≠ i1 := by
      intro hcon
      apply f1
      apply Fin.succAbove_right_injective
      rw [hcon, hj1]
    have g2 : (0 : Fin (m + 1)).succAbove j ≠ i2 := by
      intro hcon
      apply f2
      apply Fin.succAbove_right_injective
      rw [hcon, hj2]
    have g3 : (0 : Fin (m + 1)).succAbove j ≠ i3 := by
      intro hcon
      apply f3
      apply Fin.succAbove_right_injective
      rw [hcon, hj3]
    have g4 : (0 : Fin (m + 1)).succAbove j ≠ i4 := by
      intro hcon
      apply f4
      apply Fin.succAbove_right_injective
      rw [hcon, hj4]
    have e := hrest _ g1 g2 g3 g4
    rw [ntIns_apply_succAbove, ntIns_apply_succAbove] at e
    exact Fin.succAbove_right_injective e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_descent_last_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_descent_last_zero {m : ℕ} {ρ ρ' : Equiv.Perm (Fin m)}
  (h : ntMove (m + 1) (ntIns (Fin.last m) 0 ρ) (ntIns (Fin.last m) 0 ρ')) :
  ntMove m ρ ρ' := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4, hrest⟩ := h
  have q4 : i4 ≠ Fin.last m := by
    intro hcon
    have e : (ntIns (Fin.last m) 0 ρ) i4 = 0 := by
      rw [hcon]
      exact ntIns_apply_same _ _ _
    rw [e, Fin.lt_def, Fin.val_zero] at s34
    exact Nat.not_lt_zero _ s34
  have q1 : i1 ≠ Fin.last m := by
    intro hcon
    rw [hcon, Fin.val_last] at h12
    have hb := i2.is_lt
    omega
  have q2 : i2 ≠ Fin.last m := by
    intro hcon
    rw [hcon, Fin.val_last] at h23
    have hb := i3.is_lt
    omega
  have q3 : i3 ≠ Fin.last m := by
    intro hcon
    rw [hcon, Fin.val_last] at h34
    have hb := i4.is_lt
    omega
  obtain ⟨j1, hj1⟩ := Fin.exists_succAbove_eq q1
  obtain ⟨j2, hj2⟩ := Fin.exists_succAbove_eq q2
  obtain ⟨j3, hj3⟩ := Fin.exists_succAbove_eq q3
  obtain ⟨j4, hj4⟩ := Fin.exists_succAbove_eq q4
  refine ⟨j1, j2, j3, j4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hj1, ← hj2] at h12
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h12))
  · rw [← hj2, ← hj3] at h23
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h23))
  · rw [← hj3, ← hj4] at h34
    exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp (Fin.lt_def.mp h34))
  · rw [← hj1, ← hj2, ntIns_apply_succAbove, ntIns_apply_succAbove] at s12
    exact Fin.succAbove_lt_succAbove_iff.mp s12
  · rw [← hj2, ← hj3, ntIns_apply_succAbove, ntIns_apply_succAbove] at s23
    exact Fin.succAbove_lt_succAbove_iff.mp s23
  · rw [← hj3, ← hj4, ntIns_apply_succAbove, ntIns_apply_succAbove] at s34
    exact Fin.succAbove_lt_succAbove_iff.mp s34
  · rw [← hj1, ← hj3, ntIns_apply_succAbove, ntIns_apply_succAbove] at t1
    exact Fin.succAbove_right_injective t1
  · rw [← hj2, ← hj4, ntIns_apply_succAbove, ntIns_apply_succAbove] at t2
    exact Fin.succAbove_right_injective t2
  · rw [← hj3, ← hj1, ntIns_apply_succAbove, ntIns_apply_succAbove] at t3
    exact Fin.succAbove_right_injective t3
  · rw [← hj4, ← hj2, ntIns_apply_succAbove, ntIns_apply_succAbove] at t4
    exact Fin.succAbove_right_injective t4
  · intro j f1 f2 f3 f4
    have g1 : (Fin.last m).succAbove j ≠ i1 := by
      intro hcon
      apply f1
      apply Fin.succAbove_right_injective
      rw [hcon, hj1]
    have g2 : (Fin.last m).succAbove j ≠ i2 := by
      intro hcon
      apply f2
      apply Fin.succAbove_right_injective
      rw [hcon, hj2]
    have g3 : (Fin.last m).succAbove j ≠ i3 := by
      intro hcon
      apply f3
      apply Fin.succAbove_right_injective
      rw [hcon, hj3]
    have g4 : (Fin.last m).succAbove j ≠ i4 := by
      intro hcon
      apply f4
      apply Fin.succAbove_right_injective
      rw [hcon, hj4]
    have e := hrest _ g1 g2 g3 g4
    rw [ntIns_apply_succAbove, ntIns_apply_succAbove] at e
    exact Fin.succAbove_right_injective e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_inert_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_inert_zero {m : ℕ} {σ τ : Equiv.Perm (Fin (m + 1))}
  (h0 : σ 0 = Fin.last m) (h : ntMove (m + 1) σ τ ∨ ntMove (m + 1) τ σ) :
  τ 0 = Fin.last m := by
  obtain h | h := h
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, -, -, -, -, -, -, hrest⟩ := h
    have e1 : (0 : Fin (m + 1)) ≠ i1 := by
      intro hcon
      have hs : σ 0 < σ i2 := by rw [hcon]; exact s12
      rw [h0, Fin.lt_def, Fin.val_last] at hs
      have hb := (σ i2).is_lt
      omega
    have e2 : (0 : Fin (m + 1)) ≠ i2 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at h12
      exact Nat.not_lt_zero _ h12
    have e3 : (0 : Fin (m + 1)) ≠ i3 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at h23
      exact Nat.not_lt_zero _ h23
    have e4 : (0 : Fin (m + 1)) ≠ i4 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at h34
      exact Nat.not_lt_zero _ h34
    exact (hrest 0 e1 e2 e3 e4).trans h0
  · obtain ⟨j1, j2, j3, j4, g12, g23, g34, -, -, r34, u1, -, -, -, wrest⟩ := h
    have f1 : (0 : Fin (m + 1)) ≠ j1 := by
      intro hcon
      rw [← hcon, h0] at u1
      rw [← u1, Fin.lt_def, Fin.val_last] at r34
      have hb := (τ j4).is_lt
      omega
    have f2 : (0 : Fin (m + 1)) ≠ j2 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at g12
      exact Nat.not_lt_zero _ g12
    have f3 : (0 : Fin (m + 1)) ≠ j3 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at g23
      exact Nat.not_lt_zero _ g23
    have f4 : (0 : Fin (m + 1)) ≠ j4 := by
      intro hcon
      rw [← hcon, Fin.val_zero] at g34
      exact Nat.not_lt_zero _ g34
    exact ((wrest 0 f1 f2 f3 f4).symm).trans h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_inert_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_inert_last {m : ℕ} {σ τ : Equiv.Perm (Fin (m + 1))}
  (hl : σ (Fin.last m) = 0) (h : ntMove (m + 1) σ τ ∨ ntMove (m + 1) τ σ) :
  τ (Fin.last m) = 0 := by
  obtain h | h := h
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, -, -, s34, -, -, -, -, hrest⟩ := h
    have e4 : Fin.last m ≠ i4 := by
      intro hcon
      have hs : σ i3 < σ (Fin.last m) := by rw [hcon]; exact s34
      rw [hl, Fin.lt_def, Fin.val_zero] at hs
      exact Nat.not_lt_zero _ hs
    have e1 : Fin.last m ≠ i1 := by
      intro hcon
      rw [← hcon, Fin.val_last] at h12
      have hb := i2.is_lt
      omega
    have e2 : Fin.last m ≠ i2 := by
      intro hcon
      rw [← hcon, Fin.val_last] at h23
      have hb := i3.is_lt
      omega
    have e3 : Fin.last m ≠ i3 := by
      intro hcon
      rw [← hcon, Fin.val_last] at h34
      have hb := i4.is_lt
      omega
    exact (hrest (Fin.last m) e1 e2 e3 e4).trans hl
  · obtain ⟨j1, j2, j3, j4, g12, g23, g34, r12, -, -, -, -, -, u4, wrest⟩ := h
    have f4 : Fin.last m ≠ j4 := by
      intro hcon
      rw [← hcon, hl] at u4
      rw [← u4, Fin.lt_def, Fin.val_zero] at r12
      exact Nat.not_lt_zero _ r12
    have f1 : Fin.last m ≠ j1 := by
      intro hcon
      rw [← hcon, Fin.val_last] at g12
      have hb := j2.is_lt
      omega
    have f2 : Fin.last m ≠ j2 := by
      intro hcon
      rw [← hcon, Fin.val_last] at g23
      have hb := j3.is_lt
      omega
    have f3 : Fin.last m ≠ j3 := by
      intro hcon
      rw [← hcon, Fin.val_last] at g34
      have hb := j4.is_lt
      omega
    exact ((wrest (Fin.last m) f1 f2 f3 f4).symm).trans hl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntA_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntA_closed {m : ℕ} : ∀ x ∈ ntA (m + 1), ∀ y,
  (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) → y ∈ ntA (m + 1) := by
  intro x hx y hxy
  exact ntMove_inert_zero hx hxy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntB_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntB_closed {m : ℕ} : ∀ x ∈ ntB (m + 1), ∀ y,
  (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) → y ∈ ntB (m + 1) := by
  intro x hx y hxy
  exact ntMove_inert_last hx hxy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntE_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntE_closed {m : ℕ} : ∀ x ∈ ntE (m + 1), ∀ y,
  (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) → y ∈ ntE (m + 1) := by
  intro x hx y hxy
  refine ⟨?_, ?_⟩
  · intro hy0
    exact hx.1 (ntMove_inert_zero hy0 (Or.symm hxy))
  · intro hyl
    exact hx.2 (ntMove_inert_last hyl (Or.symm hxy))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRange_A](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRange_A {m : ℕ} :
  ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) '' Set.univ = ntA (m + 1) := by
  ext σ
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ntIns_apply_same _ _ _
  · intro hσ
    obtain ⟨ρ, rfl⟩ := ntIns_exists _ _ σ hσ
    exact ⟨ρ, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRange_B](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRange_B {k : ℕ} :
  ntIns (Fin.last k) (0 : Fin (k + 1)) '' Set.univ = ntB k := by
  ext σ
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ntIns_apply_same _ _ _
  · intro hσ
    obtain ⟨ρ, rfl⟩ := ntIns_exists _ _ σ hσ
    exact ⟨ρ, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_last_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_last_castSucc {m : ℕ} (ρ : Equiv.Perm (Fin (m + 1))) :
  (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ) (Fin.last (m + 1)) =
    (ρ (Fin.last m)).castSucc := by
  have hne : Fin.last (m + 1) ≠ (0 : Fin (m + 2)) := by
    intro hcon
    have e := congrArg Fin.val hcon
    rw [Fin.val_last, Fin.val_zero] at e
    omega
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
  have e0 := congrArg Fin.val hj
  simp only [Fin.succAbove_zero, Fin.val_succ, Fin.val_last] at e0
  have hjm : j.val = m := by omega
  have hjlast : j = Fin.last m := Fin.ext_iff.mpr (by rw [Fin.val_last]; exact hjm)
  have e1 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ)
    ((0 : Fin (m + 2)).succAbove j) =
    (Fin.last (m + 1)).succAbove (ρ j) :=
    ntIns_apply_succAbove _ _ _ _
  rwa [hj, hjlast, Fin.succAbove_last] at e1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInter_AB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInter_AB {m : ℕ} :
  ntA (m + 1) ∩ ntB (m + 1) =
    ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) '' ntB m := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨ρ, rfl⟩ := ntIns_exists _ _ σ hσ.1
    refine ⟨ρ, ?_, rfl⟩
    have e2 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ)
      (Fin.last (m + 1)) = 0 := hσ.2
    rw [ntIns_last_castSucc] at e2
    have h2 : (ρ (Fin.last m)).castSucc = (0 : Fin (m + 1)).castSucc :=
      e2.trans (by rfl)
    exact Fin.castSucc_injective _ h2
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ntIns_apply_same _ _ _
    · have hρ' : ρ (Fin.last m) = 0 := hρ
      have e : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ)
        (Fin.last (m + 1)) = 0 := by
        rw [ntIns_last_castSucc, hρ']
        rfl
      exact e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSwap_comm_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSwap_comm_disjoint {α : Type*} [DecidableEq α]
  {a b c d : α} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
  Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  apply Equiv.Perm.ext
  intro x
  by_cases hxa : x = a
  · subst hxa
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]
  · by_cases hxb : x = b
    · subst hxb
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]
    · by_cases hxc : x = c
      · subst hxc
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h3),
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) (Ne.symm h4)]
      · by_cases hxd : x = d
        · subst hxd
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h3),
            Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) (Ne.symm h4)]
        · simp only [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hxa hxb,
          Equiv.swap_apply_of_ne_of_ne hxc hxd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSwap_cancel_mid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSwap_cancel_mid {α : Type*} {b c s1 s2 : Equiv.Perm α}
  (h1 : s1 * s1 = 1) (hc : s1 * s2 = s2 * s1)
  (h : b * s1 * s2 = c * s1) : b * s2 = c := by
  have eLHS : (b * s1 * s2) * s1 = b * s2 := by
    rw [mul_assoc b s1 s2, mul_assoc b (s1 * s2) s1, mul_assoc s1 s2 s1, ← hc,
      ← mul_assoc s1 s1 s2, h1, one_mul]
  have e : (b * s1 * s2) * s1 = c := by
    rw [h, mul_assoc c s1 s1, h1, mul_one]
  rwa [eLHS] at e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSwap_cancel_end](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSwap_cancel_end {α : Type*} {b c s1 s2 : Equiv.Perm α}
  (h2 : s2 * s2 = 1) (h : b * s1 * s2 = c * s2) : b * s1 = c := by
  have eLHS : (b * s1 * s2) * s2 = b * s1 := by
    rw [mul_assoc b s1 s2, mul_assoc b (s1 * s2) s2, mul_assoc s1 s2 s2, h2,
      mul_one]
  have e : (b * s1 * s2) * s2 = c := by
    rw [h, mul_assoc c s2 s2, h2, mul_one]
  rwa [eLHS] at e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntHub_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntHub_val {n j : ℕ} (hj : j + 1 ≤ n) {J N1 : Fin n} (w : Fin n)
  (hwJ : w ≠ J) (hwN : w ≠ N1) :
  ((ntBeta n j hj * Equiv.swap J N1) w).val = ((ntBeta n j hj) w).val := by
  have e : (ntBeta n j hj * Equiv.swap J N1) w = ntBeta n j hj w := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwJ hwN]
  exact congrArg Fin.val e

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEven_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEven_mem (m : ℕ) :
  ntEven (m + 7) ∈ ntE (m + 6) ∧ ntPat (m + 7) (ntEven (m + 7)) ∧
    ntInc5 (m + 7) (ntEven (m + 7)) := by
  have hlast : (Fin.last (m + 6) : Fin (m + 7)).val = m + 6 := Fin.val_last _
  have hid : ∀ x : Fin (m + 7), ntEven (m + 7) x = x := fun x => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hid]
    intro h
    have hv := congrArg Fin.val h
    rw [hlast] at hv
    simp at hv
  · rw [hid]
    intro h
    have hv := congrArg Fin.val h
    rw [hlast] at hv
    simp at hv
  · refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
    by simp, by simp,
    by simp, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
  · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
    ⟨4, by omega⟩, by simp, by simp,
    by simp, by simp, ?_, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOdd_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOdd_mem (m : ℕ) :
  ntOdd (m + 5) ∈ ntE (m + 6) ∧ ntPat (m + 7) (ntOdd (m + 5)) ∧
    ntInc5 (m + 7) (ntOdd (m + 5)) := by
  have hfix : ∀ x : Fin (m + 7), x.val < m + 5 → ntOdd (m + 5) x = x := by
    intro x hx
    unfold ntOdd
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hcon
      have hv := congrArg Fin.val hcon
      change x.val = m + 5 at hv
      omega
    · intro hcon
      have hv := congrArg Fin.val hcon
      change x.val = m + 5 + 1 at hv
      omega
  have hlastB : Fin.last (m + 6) = (⟨m + 5 + 1, by omega⟩ : Fin (m + 7)) := by
    rw [Fin.ext_iff, Fin.val_last, Fin.val_mk]
  have hmove : ntOdd (m + 5) (Fin.last (m + 6)) =
    (⟨m + 5, by omega⟩ : Fin (m + 7)) := by
    rw [hlastB]
    unfold ntOdd
    exact Equiv.swap_apply_right _ _
  have h0side : ((0 : Fin (m + 7))).val < m + 5 := by
    simp only [Fin.val_zero]; omega
  let p0 : Fin (m + 7) := ⟨0, by omega⟩
  let p1 : Fin (m + 7) := ⟨1, by omega⟩
  let p2 : Fin (m + 7) := ⟨2, by omega⟩
  let p3 : Fin (m + 7) := ⟨3, by omega⟩
  let p4 : Fin (m + 7) := ⟨4, by omega⟩
  have s0 : p0.val < m + 5 := by change (0:ℕ) < m + 5; omega
  have s1 : p1.val < m + 5 := by change (1:ℕ) < m + 5; omega
  have s2 : p2.val < m + 5 := by change (2:ℕ) < m + 5; omega
  have s3 : p3.val < m + 5 := by change (3:ℕ) < m + 5; omega
  have s4 : p4.val < m + 5 := by change (4:ℕ) < m + 5; omega
  have q01 : p0.val < p1.val := by change (0:ℕ) < 1; omega
  have q12 : p1.val < p2.val := by change (1:ℕ) < 2; omega
  have q23 : p2.val < p3.val := by change (2:ℕ) < 3; omega
  have q34 : p3.val < p4.val := by change (3:ℕ) < 4; omega
  have v01 : ntOdd (m + 5) p0 < ntOdd (m + 5) p1 := by
    rw [hfix _ s0, hfix _ s1, Fin.lt_def]; exact q01
  have v12 : ntOdd (m + 5) p1 < ntOdd (m + 5) p2 := by
    rw [hfix _ s1, hfix _ s2, Fin.lt_def]; exact q12
  have v23 : ntOdd (m + 5) p2 < ntOdd (m + 5) p3 := by
    rw [hfix _ s2, hfix _ s3, Fin.lt_def]; exact q23
  have v34 : ntOdd (m + 5) p3 < ntOdd (m + 5) p4 := by
    rw [hfix _ s3, hfix _ s4, Fin.lt_def]; exact q34
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hfix _ h0side]
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_last] at hv
    simp only [Fin.val_zero] at hv
    omega
  · rw [hmove]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  · exact Or.inl ⟨p0, p1, p2, p3, q01, q12, q23, v01, v12, v23⟩
  · exact ⟨p0, p1, p2, p3, p4, q01, q12, q23, q34, v01, v12, v23, v34⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_comm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_comm_zero {k : ℕ} (y v : Fin (k + 2)) (μ : Equiv.Perm (Fin k))
  (y' v' : Fin (k + 1)) (hy : y = y'.succ) (hv : v = v'.succ) :
  ntIns y v (ntIns 0 0 μ) = ntIns 0 0 (ntIns y' v' μ) := by
  have hy0 : y ≠ 0 := by rw [hy]; exact Fin.succ_ne_zero _
  have hcast0 : (Fin.castSucc (0 : Fin (k + 1))) = (0 : Fin (k + 2)) := by
    apply Fin.ext_iff.mpr
    simp only [Fin.val_castSucc, Fin.val_zero]
  apply Equiv.Perm.ext
  intro x
  by_cases hxy : x = y
  · rw [hxy]
    have hRHS : ntIns 0 0 (ntIns y' v' μ) y = v := by
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hy0
      have hjy : j = y' := by
        apply Fin.succ_injective _
        rw [← hy, ← hj]
        exact (Fin.succAbove_zero_apply _).symm
      calc ntIns 0 0 (ntIns y' v' μ) y
        = ntIns 0 0 (ntIns y' v' μ) ((0 : Fin (k + 2)).succAbove j) := by
          rw [hj]
        _ = (0 : Fin (k + 2)).succAbove ((ntIns y' v' μ) j) :=
          ntIns_apply_succAbove _ _ _ _
        _ = ((ntIns y' v' μ) j).succ := Fin.succAbove_zero_apply _
        _ = ((ntIns y' v' μ) y').succ := by rw [hjy]
        _ = (v').succ := by rw [ntIns_apply_same]
        _ = v := hv.symm
    rw [ntIns_apply_same, hRHS]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxy
    by_cases hi0 : i = 0
    · rw [hi0] at hi
      have hxi0 : x = y.succAbove (0 : Fin (k + 1)) := hi.symm
      have e : y.succAbove (0 : Fin (k + 1)) = (0 : Fin (k + 2)) := by
        have e' : (y'.succ).succAbove (0 : Fin (k + 1)) =
          (0 : Fin (k + 1)).castSucc :=
          Fin.succAbove_succ_of_le _ _ (Fin.zero_le _)
        rwa [hy, e']
      have hx0 : x = 0 := by rw [hxi0]; exact e
      have hLHS : ntIns y v (ntIns 0 0 μ) x = (0 : Fin (k + 2)) := by
        rw [hxi0, ntIns_apply_succAbove]
        have e2 : (ntIns 0 0 μ) (0 : Fin (k + 1)) = (0 : Fin (k + 1)) :=
          ntIns_apply_same _ _ _
        have e4 : (v'.succ).succAbove (0 : Fin (k + 1)) =
          (0 : Fin (k + 1)).castSucc :=
          Fin.succAbove_succ_of_le _ _ (Fin.zero_le _)
        rwa [e2, hv, e4]
      have hRHS : ntIns 0 0 (ntIns y' v' μ) x = (0 : Fin (k + 2)) := by
        rw [hx0]
        exact ntIns_apply_same _ _ _
      rw [hLHS, hRHS]
    · obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hi0
      have hii : i'.succ = i := by rw [← hi', Fin.succAbove_zero_apply]
      have hmu : (ntIns 0 0 μ) i = ((μ i').succ : Fin (k + 1)) := by
        have e3 : i'.succ = (0 : Fin (k + 1)).succAbove i' :=
          (Fin.succAbove_zero_apply _).symm
        rw [← hii, e3, ntIns_apply_succAbove]
        exact Fin.succAbove_zero_apply _
      have hxs : x = ((y'.succAbove i').succ : Fin (k + 2)) := by
        rw [← hi, hy, ← hii, Fin.succ_succAbove_succ]
      have hx0' : x ≠ 0 := by rw [hxs]; exact Fin.succ_ne_zero _
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx0'
      have hjj : j = y'.succAbove i' := by
        apply Fin.succ_injective _
        have e5 : j.succ = x := by
          rw [← hj]
          exact (Fin.succAbove_zero_apply _).symm
        rw [e5, hxs]
      have hLHS : ntIns y v (ntIns 0 0 μ) x =
        ((v'.succAbove (μ i')).succ : Fin (k + 2)) := by
        rw [← hi, ntIns_apply_succAbove, hmu, hv, Fin.succ_succAbove_succ]
      have hRHS : ntIns 0 0 (ntIns y' v' μ) x =
        ((v'.succAbove (μ i')).succ : Fin (k + 2)) := by
        have e6 : x = (0 : Fin (k + 2)).succAbove j := hj.symm
        rw [e6, ntIns_apply_succAbove, hjj, ntIns_apply_succAbove,
          Fin.succAbove_zero_apply]
      rw [hLHS, hRHS]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_comm_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_comm_last {k : ℕ} (y v : Fin (k + 2)) (μ : Equiv.Perm (Fin k))
  (y' v' : Fin (k + 1)) (hy : y = y'.castSucc) (hv : v = v'.castSucc) :
  ntIns y v (ntIns (Fin.last k) (Fin.last k) μ) =
    ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ) := by
  have hy0 : y ≠ Fin.last (k + 1) := by rw [hy]; exact ne_of_lt (Fin.castSucc_lt_last _)
  have hsuccLast : (Fin.last k).succ = Fin.last (k + 1) := by
    apply Fin.ext_iff.mpr
    simp only [Fin.val_succ, Fin.val_last]
  apply Equiv.Perm.ext
  intro x
  by_cases hxy : x = y
  · rw [hxy]
    have hRHS : ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ) y = v := by
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hy0
      have hjy : j = y' := by
        apply Fin.castSucc_injective _
        rw [← hy, ← hj, Fin.succAbove_last_apply]
      calc ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ) y
        = ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ)
          ((Fin.last (k + 1)).succAbove j) := by rw [hj]
        _ = (Fin.last (k + 1)).succAbove ((ntIns y' v' μ) j) :=
          ntIns_apply_succAbove _ _ _ _
        _ = ((ntIns y' v' μ) j).castSucc := Fin.succAbove_last_apply _
        _ = ((ntIns y' v' μ) y').castSucc := by rw [hjy]
        _ = (v').castSucc := by rw [ntIns_apply_same]
        _ = v := hv.symm
    rw [ntIns_apply_same, hRHS]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxy
    by_cases hi0 : i = Fin.last k
    · rw [hi0] at hi
      have hxi0 : x = y.succAbove (Fin.last k) := hi.symm
      have e : y.succAbove (Fin.last k) = Fin.last (k + 1) := by
        have e' : (y'.castSucc).succAbove (Fin.last k) = (Fin.last k).succ :=
          Fin.succAbove_castSucc_of_le _ _ (Fin.le_last _)
        rw [hy, e', hsuccLast]
      have hx0 : x = Fin.last (k + 1) := by rw [hxi0]; exact e
      have hLHS : ntIns y v (ntIns (Fin.last k) (Fin.last k) μ) x =
        Fin.last (k + 1) := by
        rw [hxi0, ntIns_apply_succAbove]
        have e2 : (ntIns (Fin.last k) (Fin.last k) μ) (Fin.last k) =
          Fin.last k := ntIns_apply_same _ _ _
        have e4 : (v'.castSucc).succAbove (Fin.last k) = (Fin.last k).succ :=
          Fin.succAbove_castSucc_of_le _ _ (Fin.le_last _)
        rw [e2, hv, e4, hsuccLast]
      have hRHS : ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ) x =
        Fin.last (k + 1) := by
        rw [hx0]
        exact ntIns_apply_same _ _ _
      rw [hLHS, hRHS]
    · obtain ⟨i'', hi''⟩ := Fin.exists_succAbove_eq hi0
      have hii : i''.castSucc = i := by rw [← hi'', Fin.succAbove_last_apply]
      have hmu : (ntIns (Fin.last k) (Fin.last k) μ) i =
        ((μ i'').castSucc : Fin (k + 1)) := by
        have e3 : i''.castSucc = (Fin.last k).succAbove i'' :=
          (Fin.succAbove_last_apply _).symm
        rw [← hii, e3, ntIns_apply_succAbove]
        exact Fin.succAbove_last_apply _
      have hxs : x = ((y'.succAbove i'').castSucc : Fin (k + 2)) := by
        rw [← hi, hy, ← hii, Fin.castSucc_succAbove_castSucc]
      have hx0' : x ≠ Fin.last (k + 1) := by
        rw [hxs]; exact ne_of_lt (Fin.castSucc_lt_last _)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx0'
      have hjj : j = y'.succAbove i'' := by
        apply Fin.castSucc_injective _
        have e5 : j.castSucc = x := by
          rw [← hj]
          exact (Fin.succAbove_last_apply _).symm
        rw [e5, hxs]
      have hLHS : ntIns y v (ntIns (Fin.last k) (Fin.last k) μ) x =
        ((v'.succAbove (μ i'')).castSucc : Fin (k + 2)) := by
        rw [← hi, ntIns_apply_succAbove, hmu, hv, Fin.castSucc_succAbove_castSucc]
      have hRHS : ntIns (Fin.last (k + 1)) (Fin.last (k + 1)) (ntIns y' v' μ) x =
        ((v'.succAbove (μ i'')).castSucc : Fin (k + 2)) := by
        have e6 : x = (Fin.last (k + 1)).succAbove j := hj.symm
        rw [e6, ntIns_apply_succAbove, hjj, ntIns_apply_succAbove,
          Fin.succAbove_last_apply]
      rw [hLHS, hRHS]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSuccAbove_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSuccAbove_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
  (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.val < p.val
  · have h' : i.castSucc < p := by
    rwa [Fin.lt_def, Fin.val_castSucc]
    rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.val_castSucc, ite_eq_left h]
  · have h' : p ≤ i.castSucc := by
    rw [Fin.le_iff_val_le_val, Fin.val_castSucc]
    omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.val_succ, ite_eq_right h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInc5_pat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInc5_pat {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : ntInc5 n σ) :
  ntPat n σ := by
  obtain ⟨a, b, c, d, -, h1, h2, h3, -, s1, s2, s3, -⟩ := h
  exact Or.inl ⟨a, b, c, d, h1, h2, h3, s1, s2, s3⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_inc5_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_inc5_of {m : ℕ} (y' v' : Fin (m + 2))
  (μ : Equiv.Perm (Fin (m + 1))) (a b c d e : Fin (m + 1))
  (h1 : a.val < b.val) (h2 : b.val < c.val) (h3 : c.val < d.val)
  (h4 : d.val < e.val)
  (s1 : (μ a).val < (μ b).val) (s2 : (μ b).val < (μ c).val)
  (s3 : (μ c).val < (μ d).val) (s4 : (μ d).val < (μ e).val) :
  ntInc5 (m + 2) (ntIns y' v' μ) := by
  refine ⟨y'.succAbove a, y'.succAbove b, y'.succAbove c, y'.succAbove d,
    y'.succAbove e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.lt_def.mp ((Fin.strictMono_succAbove y') (Fin.lt_def.mpr h1))
  · exact Fin.lt_def.mp ((Fin.strictMono_succAbove y') (Fin.lt_def.mpr h2))
  · exact Fin.lt_def.mp ((Fin.strictMono_succAbove y') (Fin.lt_def.mpr h3))
  · exact Fin.lt_def.mp ((Fin.strictMono_succAbove y') (Fin.lt_def.mpr h4))
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr s1)
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr s2)
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr s3)
  · rw [ntIns_apply_succAbove, ntIns_apply_succAbove]
    exact Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr s4)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_memE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_memE {m : ℕ} (y' v' : Fin (m + 2))
  (μ : Equiv.Perm (Fin (m + 1))) (hμ : μ 0 = 0)
  (hne : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
    (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0)) :
  ntIns y' v' μ ∈ ntE (m + 1) := by
  have hy'lt := y'.is_lt
  have hv'lt := v'.is_lt
  constructor
  · intro hcon
    by_cases hy : (0 : Fin (m + 2)) = y'
    · rw [hy, ntIns_apply_same] at hcon
      obtain h | h := hne.1
      · exact h hy.symm
      · exact h hcon
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hy
      have hvi := congrArg Fin.val hi
      rw [ntSuccAbove_val] at hvi
      simp only [Fin.val_zero] at hvi
      have hi0 : i.val = 0 := by
        by_cases hc : i.val < y'.val
        · rw [ite_eq_left hc] at hvi
          omega
        · rw [ite_eq_right hc] at hvi
          omega
      have hi00 : i = 0 := Fin.ext (by simpa using hi0)
      have hμi : μ i = 0 := by rw [hi00]; exact hμ
      have e : ntIns y' v' μ (y'.succAbove i) = v'.succAbove 0 := by
        rw [ntIns_apply_succAbove, hμi]
      rw [hi] at e
      have hvv := congrArg Fin.val hcon
      rw [e, ntSuccAbove_val, Fin.val_last] at hvv
      by_cases hc : (0 : Fin (m + 1)).val < v'.val
      · rw [ite_eq_left hc] at hvv
        simp only [Fin.val_zero] at hvv
        omega
      · rw [ite_eq_right hc] at hvv
        simp only [Fin.val_zero] at hvv
        simp only [Fin.val_zero] at hc
        have hypos : 0 < y'.val := by
          by_contra hc2
          rw [hi0, ite_eq_right hc2] at hvi
          omega
        have hyv : y'.val = m + 1 := by omega
        have hvv0 : v'.val = 0 := by omega
        obtain h | h := hne.2
        · apply h
          rw [Fin.ext_iff, Fin.val_last]
          omega
        · exact h (Fin.ext (by simpa using hvv0))
  · intro hcon
    by_cases hy : Fin.last (m + 1) = y'
    · rw [hy, ntIns_apply_same] at hcon
      obtain h | h := hne.2
      · exact h hy.symm
      · exact h hcon
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hy
      have hi'lt := i.is_lt
      have hvi := congrArg Fin.val hi
      rw [ntSuccAbove_val, Fin.val_last] at hvi
      have him : i.val = m := by
        by_cases hc : i.val < y'.val
        · rw [ite_eq_left hc] at hvi
          omega
        · rw [ite_eq_right hc] at hvi
          omega
      have e : ntIns y' v' μ (y'.succAbove i) = v'.succAbove (μ i) :=
        ntIns_apply_succAbove _ _ _ _
      rw [hi] at e
      have hvv := congrArg Fin.val hcon
      rw [e, ntSuccAbove_val, Fin.val_zero] at hvv
      by_cases hc : (μ i).val < v'.val
      · rw [ite_eq_left hc] at hvv
        have hμi0 : μ i = 0 := Fin.ext (by simpa using hvv)
        have hi0 : i = 0 := μ.injective (by rw [hμi0]; exact hμ.symm)
        have hi0v : i.val = 0 := by rw [hi0]; exact Fin.val_zero _
        have hm0 : m = 0 := by omega
        have hlastv := congrArg Fin.val hi
        rw [Fin.val_last, ntSuccAbove_val, hi0v] at hlastv
        have hy0v : y'.val = 0 := by
          by_cases hc2 : 0 < y'.val
          · rw [ite_eq_left hc2] at hlastv
            omega
          · omega
        have hv1 : v'.val = m + 1 := by
          rw [hvv] at hc
          omega
        obtain h | h := hne.1
        · exact h (Fin.ext (by simpa using hy0v))
        · apply h
          rw [Fin.ext_iff, Fin.val_last]
          omega
      · rw [ite_eq_right hc] at hvv
        omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntG_sameSign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntG_sameSign {m : ℕ}
  (hIH : ∀ ρ ∈ ntG (m + 1),
    Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
      Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
  {ρ₁ ρ₂ : Equiv.Perm (Fin (m + 2))}
  (h₁ : ρ₁ ∈ ntG (m + 1)) (h₂ : ρ₂ ∈ ntG (m + 1))
  (hs : Equiv.Perm.sign ρ₁ = Equiv.Perm.sign ρ₂) :
  Relation.EqvGen (ntMove (m + 2)) ρ₁ ρ₂ := by
  have hsign_even : Equiv.Perm.sign (ntEven (m + 2)) = 1 := by
    unfold ntEven
    exact Equiv.Perm.sign_one
  have hsign_odd : Equiv.Perm.sign (ntOdd m) = -1 := by
    unfold ntOdd
    apply Equiv.Perm.sign_swap
    intro hcon
    have e2 : m = m + 1 := congrArg Fin.val hcon
    omega
  obtain h1 | h1 <;> rcases hIH ρ₂ h₂ with h2 | h2 := hIH ρ₁ h₁
  · exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)
  · exfalso
    have e1 := ntEqvGen_sign h1
    have e2 := ntEqvGen_sign h2
    rw [hsign_even] at e1
    rw [hsign_odd] at e2
    have hcon : (1 : ℤˣ) = -1 := e1.symm.trans (hs.trans e2)
    exact absurd hcon (by decide)
  · exfalso
    have e1 := ntEqvGen_sign h1
    have e2 := ntEqvGen_sign h2
    rw [hsign_odd] at e1
    rw [hsign_even] at e2
    have hcon : (-1 : ℤˣ) = 1 := e1.symm.trans (hs.trans e2)
    exact absurd hcon (by decide)
  · exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSwap_fix_vals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSwap_fix_vals {n : ℕ} (a b x : Fin n)
  (hxa : x.val ≠ a.val) (hxb : x.val ≠ b.val) :
  (Equiv.swap a b) x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro hcon
    exact hxa (by rw [hcon])
  · intro hcon
    exact hxb (by rw [hcon])

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInc5_id_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInc5_id_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2)) :
  ntInc5 (m + 2) (ntIns y' v' 1) := by
  apply ntIns_inc5_of _ _ _ ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    ⟨3, by omega⟩ ⟨4, Nat.lt_of_lt_of_le (by norm_num) (hm.trans (Nat.le_succ m))⟩
    (by simp) (by simp) (by simp) (by simp) _ _ _ _
  · simp
  · simp
  · simp
  · simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntInc5_swap23_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntInc5_swap23_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2))
  (μ : Equiv.Perm (Fin (m + 1)))
  (hμ : μ = Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) :
  ntInc5 (m + 2) (ntIns y' v' μ) := by
  apply ntIns_inc5_of _ _ _ ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    ⟨4, by omega⟩ ⟨5, by omega⟩ (by simp) (by simp) (by simp) (by simp) _ _ _ _
  · rw [hμ, ntSwap_fix_vals _ _ _ (by simp) (by simp),
    ntSwap_fix_vals _ _ _ (by simp) (by simp)]
    simp
  · rw [hμ, ntSwap_fix_vals _ _ _ (by simp) (by simp), Equiv.swap_apply_left]
    simp
  · rw [hμ, Equiv.swap_apply_left, ntSwap_fix_vals _ _ _ (by simp) (by simp)]
    simp
  · rw [hμ, ntSwap_fix_vals _ _ _ (by simp) (by simp),
    ntSwap_fix_vals _ _ _ (by simp) (by simp)]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEven_zero_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEven_zero_ins {m : ℕ} :
  ntIns (0 : Fin (m + 3)) 0 (ntEven (m + 2)) = ntEven (m + 3) := by
  change ntIns (0 : Fin (m + 3)) 0 (1 : Equiv.Perm (Fin (m + 2))) = 1
  exact ntIns_zero_one

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOdd_zero_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOdd_zero_ins {m : ℕ} :
  ntIns (0 : Fin (m + 3)) 0 (ntOdd m) = ntOdd (m + 1) := by
  have e1 : ntOdd m =
    Equiv.swap (⟨m, by omega⟩ : Fin (m + 2)) ⟨m + 1, by omega⟩ := rfl
  have e2 : ntOdd (m + 1) =
    Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3)) ⟨m + 2, by omega⟩ := rfl
  rw [e1, ntIns_zero_swap, e2]
  congr 1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEven_last_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEven_last_ins {m : ℕ} :
  ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntEven (m + 2)) =
    ntEven (m + 3) := by
  change ntIns (Fin.last (m + 2)) (Fin.last (m + 2))
    (1 : Equiv.Perm (Fin (m + 2))) = 1
  exact ntIns_last_one

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_close_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_close_even {m : ℕ} {w : Equiv.Perm (Fin (m + 3))}
  {inner : Equiv.Perm (Fin (m + 2))}
  (hcongr : Relation.EqvGen (ntMove (m + 3)) w (ntIns 0 0 inner))
  (hI : Relation.EqvGen (ntMove (m + 2)) inner (ntEven (m + 2))) :
  Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1)) := by
  have hlift := ntEqvGen_ins (0 : Fin (m + 3)) (0 : Fin (m + 3)) hI
  rw [ntEven_zero_ins] at hlift
  exact Or.inl (Relation.EqvGen.trans _ _ _ hcongr hlift)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_close_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_close_odd {m : ℕ} {w : Equiv.Perm (Fin (m + 3))}
  {inner : Equiv.Perm (Fin (m + 2))}
  (hcongr : Relation.EqvGen (ntMove (m + 3)) w (ntIns 0 0 inner))
  (hI : Relation.EqvGen (ntMove (m + 2)) inner (ntOdd m)) :
  Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1)) := by
  have hlift := ntEqvGen_ins (0 : Fin (m + 3)) (0 : Fin (m + 3)) hI
  rw [ntOdd_zero_ins] at hlift
  exact Or.inr (Relation.EqvGen.trans _ _ _ hcongr hlift)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_closeLast_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_closeLast_even {m : ℕ} {w : Equiv.Perm (Fin (m + 3))}
  {inner : Equiv.Perm (Fin (m + 2))}
  (hcongr : Relation.EqvGen (ntMove (m + 3)) w
    (ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) inner))
  (hI : Relation.EqvGen (ntMove (m + 2)) inner (ntEven (m + 2))) :
  Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1)) := by
  have hlift := ntEqvGen_ins (Fin.last (m + 2)) (Fin.last (m + 2)) hI
  rw [ntEven_last_ins] at hlift
  exact Or.inl (Relation.EqvGen.trans _ _ _ hcongr hlift)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_transfer {m : ℕ}
  (hIH : ∀ ρ ∈ ntG (m + 1),
    Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
      Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
  {y v : Fin (m + 3)} {ρ μ' : Equiv.Perm (Fin (m + 2))}
  (hρ : ρ ∈ ntG (m + 1)) (hμ' : μ' ∈ ntG (m + 1))
  (hsign : Equiv.Perm.sign ρ = Equiv.Perm.sign μ')
  {w : Equiv.Perm (Fin (m + 3))}
  (hstep : Relation.EqvGen (ntMove (m + 3)) (ntIns y v μ') w)
  (hclose : Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1))) :
  Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  have hρμ := ntG_sameSign hIH hρ hμ' hsign
  have hlift := ntEqvGen_ins y v hρμ
  have hchain := Relation.EqvGen.trans _ _ _ hlift hstep
  obtain h | h := hclose
  · exact Or.inl (Relation.EqvGen.trans _ _ _ hchain h)
  · exact Or.inr (Relation.EqvGen.trans _ _ _ hchain h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntWit1_vals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntWit1_vals {m : ℕ} (hm : 5 ≤ m)
  {y v : Fin (m + 3)} (hyvv : y.val = 1 ∧ v.val = m + 2)
  {μ' : Equiv.Perm (Fin (m + 2))}
  (f0 : μ' (⟨0, by omega⟩ : Fin (m + 2)) =
    (⟨2, Nat.lt_of_lt_of_le (by norm_num) (hm.trans (Nat.le_add_right m 2))⟩ :
      Fin (m + 2)))
  (f1 : μ' (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μ' (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2))) :
  (ntIns y v μ') (⟨0, by omega⟩ : Fin (m + 3)) =
    (⟨2, by omega⟩ : Fin (m + 3)) ∧
    (ntIns y v μ') (⟨1, by omega⟩ : Fin (m + 3)) = v ∧
    (ntIns y v μ') (⟨2, by omega⟩ : Fin (m + 3)) =
      (⟨0, by omega⟩ : Fin (m + 3)) ∧
    (ntIns y v μ') (⟨3, by omega⟩ : Fin (m + 3)) =
      (⟨1, by omega⟩ : Fin (m + 3)) := by
  obtain ⟨hy1, hv2⟩ := hyvv
  have hvF : v = Fin.last (m + 2) := Fin.ext (by rw [Fin.val_last]; exact hv2)
  have hxy0 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ y := by
    intro hcon
    have hvv : (0 : ℕ) = y.val := congrArg Fin.val hcon
    omega
  have hxy2 : (⟨2, by omega⟩ : Fin (m + 3)) ≠ y := by
    intro hcon
    have hvv : (2 : ℕ) = y.val := congrArg Fin.val hcon
    omega
  have hxy3 : (⟨3, by omega⟩ : Fin (m + 3)) ≠ y := by
    intro hcon
    have hvv : (3 : ℕ) = y.val := congrArg Fin.val hcon
    omega
  have hyF : y = (⟨1, by omega⟩ : Fin (m + 3)) := Fin.ext hy1
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxy0
    have hviN : (if i.val < y.val then i.val else i.val + 1) = 0 := by
      have hvi := congrArg Fin.val hi
      rwa [ntSuccAbove_val] at hvi
    have hi0 : i.val = 0 := by
      by_cases hc : i.val < y.val
      · rw [ite_eq_left hc] at hviN
        omega
      · rw [ite_eq_right hc] at hviN
        omega
    have hi00 : i = (⟨0, by omega⟩ : Fin (m + 2)) := Fin.ext hi0
    rw [← hi, ntIns_apply_succAbove, hi00, f0]
    apply Fin.ext
    show (v.succAbove _).val = _
    rw [ntSuccAbove_val]
    have hc : (2 : ℕ) < v.val := by omega
    have hc' : (⟨2, by omega⟩ : Fin (m + 2)).val < v.val := hc
    simp [hc']
  · rw [← hyF]
    exact ntIns_apply_same _ _ _
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxy2
    have hviN : (if i.val < y.val then i.val else i.val + 1) = 2 := by
      have hvi := congrArg Fin.val hi
      rwa [ntSuccAbove_val] at hvi
    have hi1 : i.val = 1 := by
      by_cases hc : i.val < y.val
      · rw [ite_eq_left hc] at hviN
        omega
      · rw [ite_eq_right hc] at hviN
        omega
    have hi11 : i = (⟨1, by omega⟩ : Fin (m + 2)) := Fin.ext hi1
    rw [← hi, ntIns_apply_succAbove, hi11, f1]
    apply Fin.ext
    show (v.succAbove _).val = _
    rw [ntSuccAbove_val]
    have hc : (0 : ℕ) < v.val := by omega
    have hc' : (⟨0, by omega⟩ : Fin (m + 2)).val < v.val := hc
    simp [hc']
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxy3
    have hviN : (if i.val < y.val then i.val else i.val + 1) = 3 := by
      have hvi := congrArg Fin.val hi
      rwa [ntSuccAbove_val] at hvi
    have hi2 : i.val = 2 := by
      by_cases hc : i.val < y.val
      · rw [ite_eq_left hc] at hviN
        omega
      · rw [ite_eq_right hc] at hviN
        omega
    have hi22 : i = (⟨2, by omega⟩ : Fin (m + 2)) := Fin.ext hi2
    rw [← hi, ntIns_apply_succAbove, hi22, f2]
    apply Fin.ext
    show (v.succAbove _).val = _
    rw [ntSuccAbove_val]
    have hc : (1 : ℕ) < v.val := by omega
    have hc' : (⟨1, by omega⟩ : Fin (m + 2)).val < v.val := hc
    simp [hc']

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntHeqP1e](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntHeqP1e {m : ℕ} (hm : 5 ≤ m)
  {y v : Fin (m + 3)} (hyvv : y.val = 1 ∧ v.val = m + 2)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  (ntIns y v μe) * Equiv.swap (⟨0, by omega⟩ : Fin (m + 3))
    (⟨2, by omega⟩ : Fin (m + 3)) *
    Equiv.swap (⟨1, by omega⟩ : Fin (m + 3))
      (⟨3, by omega⟩ : Fin (m + 3)) =
    ntIns (⟨3, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3))
      1 := by
  obtain ⟨hy1, hv2⟩ := hyvv
  obtain ⟨hWa, hWb, hWc, hWd⟩ := ntWit1_vals hm ⟨hy1, hv2⟩ f0 f1 f2
  have n01 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ (⟨1, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n03 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ (⟨3, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n10 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ (⟨0, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n12 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ (⟨2, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n13 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ (⟨3, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n21 : (⟨2, by omega⟩ : Fin (m + 3)) ≠ (⟨1, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n23 : (⟨2, by omega⟩ : Fin (m + 3)) ≠ (⟨3, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n30 : (⟨3, by omega⟩ : Fin (m + 3)) ≠ (⟨0, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  have n32 : (⟨3, by omega⟩ : Fin (m + 3)) ≠ (⟨2, by omega⟩ : Fin (m + 3)) :=
    Fin.ne_of_val_ne (by simp)
  apply Equiv.Perm.ext
  intro x
  by_cases hxa : x = (⟨0, by omega⟩ : Fin (m + 3))
  · subst hxa
    have eL : ((ntIns y v μe) * Equiv.swap (⟨0, by omega⟩ : Fin (m + 3))
      (⟨2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨1, by omega⟩ : Fin (m + 3))
        (⟨3, by omega⟩ : Fin (m + 3))) (⟨0, by omega⟩ : Fin (m + 3)) =
      (⟨0, by omega⟩ : Fin (m + 3)) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne n01 n03,
        Equiv.swap_apply_left, hWc]
    have eR : ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3)) 1
      (⟨0, by omega⟩ : Fin (m + 3)) = (⟨0, by omega⟩ : Fin (m + 3)) := by
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq n03
      conv_lhs => rw [← hi]
      rw [ntIns_apply_succAbove]
      have h1 : ((1 : Equiv.Perm (Fin (m + 2)))) i = i := rfl
      rw [h1]
      have hi0 : i = (⟨0, by omega⟩ : Fin (m + 2)) := by
        apply Fin.ext
        have hvi := congrArg Fin.val hi
        rw [ntSuccAbove_val] at hvi
        have hviN : (if i.val < 3 then i.val else i.val + 1) = 0 := hvi
        by_cases hc : i.val < 3
        · rw [ite_eq_left hc] at hviN
          omega
        · rw [ite_eq_right hc] at hviN
          omega
      rw [hi0]
      apply Fin.ext
      rw [ntSuccAbove_val]
      change (if (0 : ℕ) < m + 2 then 0 else 0 + 1) = 0
      have hc0 : (0 : ℕ) < m + 2 := by omega
      rw [ite_eq_left hc0]
    exact eL.trans eR.symm
  · by_cases hxb : x = (⟨1, by omega⟩ : Fin (m + 3))
    · subst hxb
      have eL : ((ntIns y v μe) * Equiv.swap (⟨0, by omega⟩ : Fin (m + 3))
        (⟨2, by omega⟩ : Fin (m + 3)) *
        Equiv.swap (⟨1, by omega⟩ : Fin (m + 3))
          (⟨3, by omega⟩ : Fin (m + 3))) (⟨1, by omega⟩ : Fin (m + 3)) =
        (⟨1, by omega⟩ : Fin (m + 3)) := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne n30 n32,
          hWd]
      have eR : ntIns (⟨3, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3)) 1
        (⟨1, by omega⟩ : Fin (m + 3)) = (⟨1, by omega⟩ : Fin (m + 3)) := by
        obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq n13
        conv_lhs => rw [← hi]
        rw [ntIns_apply_succAbove]
        have h1 : ((1 : Equiv.Perm (Fin (m + 2)))) i = i := rfl
        rw [h1]
        have hi1 : i = (⟨1, by omega⟩ : Fin (m + 2)) := by
          apply Fin.ext
          have hvi := congrArg Fin.val hi
          rw [ntSuccAbove_val] at hvi
          have hviN : (if i.val < 3 then i.val else i.val + 1) = 1 := hvi
          by_cases hc : i.val < 3
          · rw [ite_eq_left hc] at hviN
            omega
          · rw [ite_eq_right hc] at hviN
            omega
        rw [hi1]
        apply Fin.ext
        rw [ntSuccAbove_val]
        change (if (1 : ℕ) < m + 2 then 1 else 1 + 1) = 1
        have hc1 : (1 : ℕ) < m + 2 := by omega
        rw [ite_eq_left hc1]
      exact eL.trans eR.symm
    · by_cases hxc : x = (⟨2, by omega⟩ : Fin (m + 3))
      · subst hxc
        have eL : ((ntIns y v μe) * Equiv.swap (⟨0, by omega⟩ : Fin (m + 3))
          (⟨2, by omega⟩ : Fin (m + 3)) *
          Equiv.swap (⟨1, by omega⟩ : Fin (m + 3))
            (⟨3, by omega⟩ : Fin (m + 3))) (⟨2, by omega⟩ : Fin (m + 3)) =
          (⟨2, by omega⟩ : Fin (m + 3)) := by
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne n21 n23,
            Equiv.swap_apply_right, hWa]
        have eR : ntIns (⟨3, by omega⟩ : Fin (m + 3))
          (⟨m + 2, by omega⟩ : Fin (m + 3)) 1
          (⟨2, by omega⟩ : Fin (m + 3)) = (⟨2, by omega⟩ : Fin (m + 3)) := by
          obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq n23
          conv_lhs => rw [← hi]
          rw [ntIns_apply_succAbove]
          have h1 : ((1 : Equiv.Perm (Fin (m + 2)))) i = i := rfl
          rw [h1]
          have hi2 : i = (⟨2, by omega⟩ : Fin (m + 2)) := by
            apply Fin.ext
            have hvi := congrArg Fin.val hi
            rw [ntSuccAbove_val] at hvi
            have hviN : (if i.val < 3 then i.val else i.val + 1) = 2 := hvi
            by_cases hc : i.val < 3
            · rw [ite_eq_left hc] at hviN
              omega
            · rw [ite_eq_right hc] at hviN
              omega
          rw [hi2]
          apply Fin.ext
          rw [ntSuccAbove_val]
          change (if (2 : ℕ) < m + 2 then 2 else 2 + 1) = 2
          have hc2 : (2 : ℕ) < m + 2 := by omega
          rw [ite_eq_left hc2]
        exact eL.trans eR.symm
      · by_cases hxd : x = (⟨3, by omega⟩ : Fin (m + 3))
        · subst hxd
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
            Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne n10 n12,
            hWb, ntIns_apply_same]
          exact Fin.ext hv2
        · have hxv0 : x.val ≠ 0 := fun h => hxa (Fin.ext h)
          have hxv1 : x.val ≠ 1 := fun h => hxb (Fin.ext h)
          have hxv2 : x.val ≠ 2 := fun h => hxc (Fin.ext h)
          have hxv3 : x.val ≠ 3 := fun h => hxd (Fin.ext h)
          have hxy : x ≠ y := fun hcon => hxb (hcon.trans (Fin.ext hy1))
          obtain ⟨i0, hi0⟩ := Fin.exists_succAbove_eq hxy
          obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hxd
          have eLHS : ((ntIns y v μe) * Equiv.swap (⟨0, by omega⟩ : Fin (m + 3))
            (⟨2, by omega⟩ : Fin (m + 3)) *
            Equiv.swap (⟨1, by omega⟩ : Fin (m + 3))
              (⟨3, by omega⟩ : Fin (m + 3))) x =
            v.succAbove (μe i0) := by
            rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              Equiv.swap_apply_of_ne_of_ne hxb hxd,
              Equiv.swap_apply_of_ne_of_ne hxa hxc, ← hi0,
              ntIns_apply_succAbove]
          have eRHS : ntIns (⟨3, by omega⟩ : Fin (m + 3))
            (⟨m + 2, by omega⟩ : Fin (m + 3)) 1 x =
            (⟨m + 2, by omega⟩ : Fin (m + 3)).succAbove i := by
            rw [← hi, ntIns_apply_succAbove]
            have h1 : ((1 : Equiv.Perm (Fin (m + 2)))) i = i := rfl
            rw [h1]
          rw [eLHS, eRHS]
          apply Fin.ext
          rw [ntSuccAbove_val, ntSuccAbove_val]
          have hvi0 := congrArg Fin.val hi0
          rw [ntSuccAbove_val] at hvi0
          have hvi0N : (if i0.val < y.val then i0.val else i0.val + 1) =
            x.val := hvi0
          have hvi := congrArg Fin.val hi
          rw [ntSuccAbove_val] at hvi
          have hviN : (if i.val < 3 then i.val else i.val + 1) = x.val := hvi
          by_cases hc0 : i0.val < y.val
          · rw [ite_eq_left hc0] at hvi0N
            omega
          · rw [ite_eq_right hc0] at hvi0N
            by_cases hcI : i.val < 3
            · rw [ite_eq_left hcI] at hviN
              omega
            · rw [ite_eq_right hcI] at hviN
              have hfi0 : μe i0 = i0 := hfix _ (by omega)
              have eμ : (μe i0).val = i0.val := congrArg Fin.val hfi0
              have hxlt := x.is_lt
              have hi0lt := i0.is_lt
              have hilt := i.is_lt
              change (if (μe i0).val < v.val then (μe i0).val
                else (μe i0).val + 1) =
                (if i.val < m + 2 then i.val else i.val + 1)
              by_cases hcL : (μe i0).val < v.val
              · rw [ite_eq_left hcL]
                by_cases hcR : i.val < m + 2
                · rw [ite_eq_left hcR]
                  omega
                · rw [ite_eq_right hcR]
                  omega
              · omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntHeqP1o](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntHeqP1o {m : ℕ} (hm : 5 ≤ m)
  {y v : Fin (m + 3)} (hyvv : y.val = 1 ∧ v.val = m + 2)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  (ntIns y v (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2)))) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) =
    ntIns (⟨3, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3))
      (ntOdd m) := by
  have hyA : y.succAbove (⟨m, by omega⟩ : Fin (m + 2)) =
    (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    rw [ntSuccAbove_val]
    change (if m < y.val then m else m + 1) = m + 1
    rw [ite_eq_right (by omega)]
  have hyB : y.succAbove (⟨m + 1, by omega⟩ : Fin (m + 2)) =
    (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    rw [ntSuccAbove_val]
    change (if m + 1 < y.val then m + 1 else m + 2) = m + 2
    rw [ite_eq_right (by omega)]
  have h3A : (⟨3, by omega⟩ : Fin (m + 3)).succAbove
    (⟨m, by omega⟩ : Fin (m + 2)) = (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    rw [ntSuccAbove_val]
    change (if m < 3 then m else m + 1) = m + 1
    rw [ite_eq_right (by omega)]
  have h3B : (⟨3, by omega⟩ : Fin (m + 3)).succAbove
    (⟨m + 1, by omega⟩ : Fin (m + 2)) =
      (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    rw [ntSuccAbove_val]
    change (if m + 1 < 3 then m + 1 else m + 2) = m + 2
    rw [ite_eq_right (by omega)]
  have hcomm1 : Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
    (⟨m + 2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) =
    Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3)) :=
    ntSwap_comm_disjoint
      (a := (⟨m + 1, by omega⟩ : Fin (m + 3)))
      (b := (⟨m + 2, by omega⟩ : Fin (m + 3)))
      (c := (⟨0, by omega⟩ : Fin (m + 3)))
      (d := (⟨2, by omega⟩ : Fin (m + 3)))
      (by
        intro h
        have h' : m + 1 = 0 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 1 = 2 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 2 = 0 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 2 = 2 := congrArg Fin.val h
        omega)
  have hcomm2 : Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
    (⟨m + 2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) =
    Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3)) :=
    ntSwap_comm_disjoint
      (a := (⟨m + 1, by omega⟩ : Fin (m + 3)))
      (b := (⟨m + 2, by omega⟩ : Fin (m + 3)))
      (c := (⟨1, by omega⟩ : Fin (m + 3)))
      (d := (⟨3, by omega⟩ : Fin (m + 3)))
      (by
        intro h
        have h' : m + 1 = 1 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 1 = 3 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 2 = 1 := congrArg Fin.val h
        omega)
      (by
        intro h
        have h' : m + 2 = 3 := congrArg Fin.val h
        omega)
  have he := ntHeqP1e hm hyvv f0 f1 f2 hfix
  calc
    (ntIns y v (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2)))) *
        Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
        Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) =
      (ntIns y v μe * Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3))) *
          Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
          Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) := by
            rw [ntIns_mul_swap, hyA, hyB]
    _ = (ntIns y v μe *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
      Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3))) *
      Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
          rw [mul_assoc (ntIns y v μe), hcomm1, ← mul_assoc,
            mul_assoc (ntIns y v μe * _), hcomm2]
          simp only [mul_assoc]
    _ = ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3)) 1 *
      Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 3))
        (⟨m + 2, by omega⟩ : Fin (m + 3)) := by rw [he]
    _ = ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3))
      ((1 : Equiv.Perm (Fin (m + 2))) *
        Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
          (⟨m + 1, by omega⟩ : Fin (m + 2))) := by
            rw [ntIns_mul_swap, h3A, h3B]
    _ = ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3)) (ntOdd m) := by
        simp [ntOdd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntPair1e_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntPair1e_step {m : ℕ} (hm : 5 ≤ m)
  {y v : Fin (m + 3)} (hyvv : y.val = 1 ∧ v.val = m + 2)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  Relation.EqvGen (ntMove (m + 3)) (ntIns y v μe)
    (ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3)) 1) := by
  obtain ⟨hWa, hWb, hWc, hWd⟩ := ntWit1_vals hm hyvv f0 f1 f2
  have hmove := ntMove_of_3412 (n := m + 3) (τ := ntIns y v μe)
    (i1 := (⟨0, by omega⟩ : Fin (m + 3)))
    (i2 := (⟨1, by omega⟩ : Fin (m + 3)))
    (i3 := (⟨2, by omega⟩ : Fin (m + 3)))
    (i4 := (⟨3, by omega⟩ : Fin (m + 3)))
    (by simp) (by simp) (by simp)
    (by rw [hWc, hWd]; simp)
    (by rw [hWd, hWa]; change (1 : ℕ) < 2; omega)
    (by rw [hWa, hWb, Fin.lt_def]; omega)
  rw [ntHeqP1e hm hyvv f0 f1 f2 hfix] at hmove
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOdd_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOdd_sign (m : ℕ) : Equiv.Perm.sign (ntOdd m) = -1 := by
  apply Equiv.Perm.sign_swap
  intro h
  have h' : m = m + 1 := congrArg Fin.val h
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRC_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_one (n : ℕ) : ntRC (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Equiv.Perm.ext
  intro i
  simp [ntRC_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRC_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_swap {n : ℕ} (a b : Fin n) :
  ntRC (Equiv.swap a b) = Equiv.swap a.rev b.rev := by
  rw [ntRC, Equiv.mul_swap_eq_swap_mul, mul_assoc, ntRev_mul_self, mul_one]
  simp only [Fin.revPerm_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOdd_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOdd_symm (m : ℕ) : (ntOdd m).symm = ntOdd m :=
Equiv.symm_swap _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRC_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRC_odd (m : ℕ) :
  ntRC (ntOdd m) = Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨1, by omega⟩ := by
  rw [ntOdd, ntRC_swap]
  have hm : (⟨m, by omega⟩ : Fin (m + 2)).rev = (⟨1, by omega⟩ : Fin (m + 2)) := by
    apply Fin.ext
    simp
  have hm1 : (⟨m + 1, by omega⟩ : Fin (m + 2)).rev =
    (⟨0, by omega⟩ : Fin (m + 2)) := by
    apply Fin.ext
    simp
  rw [hm, hm1, Equiv.swap_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMuP1e_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMuP1e_inc {m : ℕ} (hm : 5 ≤ m)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  ntInc5 (m + 2) μe := by
  refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
    ⟨5, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · rw [f1, f2, Fin.lt_def]
    simp
  · rw [f2, hfix _ (by norm_num)]
    change (1 : ℕ) < 3
    omega
  · rw [hfix _ (by norm_num), hfix _ (by norm_num), Fin.lt_def]
    simp
  · rw [hfix _ (by norm_num), hfix _ (by norm_num), Fin.lt_def]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMuP1o_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMuP1o_inc {m : ℕ} (hm : 5 ≤ m)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  ntInc5 (m + 2) (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) := by
  have hswap : ∀ x : Fin (m + 2), x.val ≠ m → x.val ≠ m + 1 →
    Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2)) x = x := by
    intro x hxm hxm1
    exact ntSwap_fix_vals _ _ _ hxm hxm1
  have g1 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨1, by omega⟩ : Fin (m + 2)) =
    (⟨0, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply,
      hswap _ (by change 1 ≠ m; omega) (by change 1 ≠ m + 1; omega), f1]
  have g2 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨2, by omega⟩ : Fin (m + 2)) =
    (⟨1, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply,
      hswap _ (by change 2 ≠ m; omega) (by change 2 ≠ m + 1; omega), f2]
  have g3 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨3, by omega⟩ : Fin (m + 2)) =
    (⟨3, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply,
      hswap _ (by change 3 ≠ m; omega) (by change 3 ≠ m + 1; omega),
      hfix _ (by norm_num)]
  have g4 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨4, by omega⟩ : Fin (m + 2)) =
    (⟨4, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply,
      hswap _ (by change 4 ≠ m; omega) (by change 4 ≠ m + 1; omega),
      hfix _ (by norm_num)]
  have gm : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨m, by omega⟩ : Fin (m + 2)) =
    (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      hfix _ (show (3 : ℕ) ≤ m + 1 from by omega)]
  refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
    ⟨m, by omega⟩, by simp, by simp, by simp, (by change 4 < m; omega),
    ?_, ?_, ?_, ?_⟩
  · rw [g1, g2, Fin.lt_def]
    simp
  · rw [g2, g3]
    change (1 : ℕ) < 3
    omega
  · rw [g3, g4, Fin.lt_def]
    simp
  · rw [g4, gm]
    change 4 < m + 1
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntPair1o_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntPair1o_step {m : ℕ} (hm : 5 ≤ m)
  {y v : Fin (m + 3)} (hyvv : y.val = 1 ∧ v.val = m + 2)
  {μe : Equiv.Perm (Fin (m + 2))}
  (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
  (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
  (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
  (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
  Relation.EqvGen (ntMove (m + 3))
    (ntIns y v (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2))))
    (ntIns (⟨3, by omega⟩ : Fin (m + 3))
      (⟨m + 2, by omega⟩ : Fin (m + 3)) (ntOdd m)) := by
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hswap : ∀ x : Fin (m + 2), x.val ≤ 2 →
    Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2)) x = x := by
    intro x hx
    exact ntSwap_fix_vals _ _ _ (by change x.val ≠ m; omega)
      (by change x.val ≠ m + 1; omega)
  have g0 : μo (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply, hswap _ (by norm_num), f0]
  have g1 : μo (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply, hswap _ (by norm_num), f1]
  have g2 : μo (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)) := by
    rw [Equiv.Perm.mul_apply, hswap _ (by norm_num), f2]
  obtain ⟨hWa, hWb, hWc, hWd⟩ := ntWit1_vals hm hyvv g0 g1 g2
  have hmove := ntMove_of_3412 (n := m + 3) (τ := ntIns y v μo)
    (i1 := (⟨0, by omega⟩ : Fin (m + 3)))
    (i2 := (⟨1, by omega⟩ : Fin (m + 3)))
    (i3 := (⟨2, by omega⟩ : Fin (m + 3)))
    (i4 := (⟨3, by omega⟩ : Fin (m + 3)))
    (by simp) (by simp) (by simp)
    (by rw [hWc, hWd]; simp)
    (by rw [hWd, hWa]; change (1 : ℕ) < 2; omega)
    (by rw [hWa, hWb, Fin.lt_def]; omega)
  change ntMove (m + 3)
    ((ntIns y v (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2)))) *
        Equiv.swap (⟨0, by omega⟩ : Fin (m + 3)) (⟨2, by omega⟩ : Fin (m + 3)) *
        Equiv.swap (⟨1, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)))
      (ntIns y v (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
        (⟨m + 1, by omega⟩ : Fin (m + 2)))) at hmove
  rw [ntHeqP1o hm hyvv f0 f1 f2 hfix] at hmove
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntIns_parity_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntIns_parity_transfer {m : ℕ}
  (hIH : ∀ ρ ∈ ntG (m + 1),
    Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
      Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
  {y v : Fin (m + 3)} {ρ μe μo : Equiv.Perm (Fin (m + 2))}
  (hρ : ρ ∈ ntG (m + 1))
  (hμe : μe ∈ ntG (m + 1)) (hse : Equiv.Perm.sign μe = 1)
  (hμo : μo ∈ ntG (m + 1)) (hso : Equiv.Perm.sign μo = -1)
  {we wo : Equiv.Perm (Fin (m + 3))}
  (hste : Relation.EqvGen (ntMove (m + 3)) (ntIns y v μe) we)
  (hsto : Relation.EqvGen (ntMove (m + 3)) (ntIns y v μo) wo)
  (hce : Relation.EqvGen (ntMove (m + 3)) we (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) we (ntOdd (m + 1)))
  (hco : Relation.EqvGen (ntMove (m + 3)) wo (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) wo (ntOdd (m + 1))) :
  Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  obtain he | ho := hIH ρ hρ
  · have hsρ : Equiv.Perm.sign ρ = 1 := by
    simpa [ntEven] using ntEqvGen_sign he
    exact ntIns_transfer hIH hρ hμe (hsρ.trans hse.symm) hste hce
  · have hsρ : Equiv.Perm.sign ρ = -1 := (ntEqvGen_sign ho).trans (ntOdd_sign m)
    exact ntIns_transfer hIH hρ hμo (hsρ.trans hso.symm) hsto hco

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_mem_breaks_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_mem_breaks_iff {n : ℕ} [NeZero n]
  (π : Equiv.Perm (Fin n)) (i : Fin n) :
  i ∈ ntBreaks π ↔ π (finRotate n i) ≠ (finRotate n).symm (π i) := by
  simp only [ntBreaks, Finset.mem_map, Equiv.coe_toEmbedding,
    Equiv.Perm.mem_support]
  constructor
  · rintro ⟨x, hx, hxi⟩
    subst i
    rw [finRotate_symm_apply, ne_eq, eq_sub_iff_add_eq]
    simpa [ntDefect, Equiv.Perm.mul_apply] using hx
  · intro h
    rw [finRotate_symm_apply, ne_eq, eq_sub_iff_add_eq] at h
    refine ⟨π i, ?_, by simp⟩
    simpa [ntDefect, Equiv.Perm.mul_apply] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_card_breaks](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_card_breaks {n : ℕ} (π : Equiv.Perm (Fin n)) :
  (ntBreaks π).card = (ntDefect π).support.card := by
  simp [ntBreaks]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_card_breaks_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_card_breaks_ne_one {n : ℕ} (π : Equiv.Perm (Fin n)) :
  (ntBreaks π).card ≠ 1 := by
  rw [nt_card_breaks]
  exact Equiv.Perm.card_support_ne_one _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_succAbove](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_succAbove {m : ℕ} (hm : 0 < m) (p : Fin (m + 1)) (a : Fin m)
  (hskip : finRotate (m + 1) (p.succAbove a) ≠ p) :
  finRotate (m + 1) (p.succAbove a) = p.succAbove (finRotate m a) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  by_cases hx : p.succAbove a = Fin.last (q + 1)
  · have hpL : p ≠ Fin.last (q + 1) := by
    intro hp
    exact Fin.succAbove_ne p a (hx.trans hp.symm)
    have hp0 : p ≠ 0 := by
      intro hp
      apply hskip
      rw [hx, finRotate_last, hp]
    have hxv := congrArg Fin.val hx
    rw [ntSuccAbove_val] at hxv
    simp only [Fin.val_last] at hxv
    have hav : a.val = q := by
      split_ifs at hxv <;> omega
    have ha : a = Fin.last q := Fin.ext (by simpa using hav)
    rw [hx, finRotate_last, ha, finRotate_last]
    apply Fin.ext
    rw [ntSuccAbove_val]
    change 0 = if (0 : ℕ) < p.val then 0 else 0 + 1
    rw [ite_eq_left (by
      have hp := p.is_lt
      have hpv : p.val ≠ 0 := fun h => hp0 (Fin.ext h)
      omega)]
  · have ha : a ≠ Fin.last q := by
    intro ha
    subst a
    by_cases hap : (Fin.last q).val < p.val
    · apply hskip
      have hp : p = Fin.last (q + 1) := by
        apply Fin.ext
        simp only [Fin.val_last] at hap ⊢
        have hplt := p.is_lt
        omega
      rw [hp, Fin.succAbove_last_apply]
      apply Fin.ext
      have hx' : (Fin.last q).castSucc ≠ Fin.last (q + 1) := by
        intro h
        have h' := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_last] at h'
        omega
      rw [coe_finRotate_of_ne_last hx']
      simp only [Fin.val_castSucc, Fin.val_last]
    · apply hx
      apply Fin.ext
      rw [ntSuccAbove_val, ite_eq_right hap]
      simp only [Fin.val_last]
    have hbig := coe_finRotate_of_ne_last hx
    have hsmall := coe_finRotate_of_ne_last ha
    have hskipv : (p.succAbove a).val + 1 ≠ p.val := by
      intro h
      apply hskip
      apply Fin.ext
      rwa [hbig]
    rw [ntSuccAbove_val] at hskipv
    apply Fin.ext
    rw [hbig]
    simp only [ntSuccAbove_val]
    rw [hsmall]
    split_ifs at hskipv ⊢ <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_succAbove_cross](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_succAbove_cross {m : ℕ} (hm : 0 < m)
  (p : Fin (m + 1)) (a : Fin m)
  (hcross : finRotate (m + 1) (p.succAbove a) = p) :
  p.succAbove (finRotate m a) = finRotate (m + 1) p := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hsa := coe_finRotate (p.succAbove a)
  have hp := coe_finRotate p
  have ha := coe_finRotate a
  have hcrossv := congrArg Fin.val hcross
  rw [hsa] at hcrossv
  simp only [Fin.ext_iff, ntSuccAbove_val, Fin.val_last] at hcrossv
  apply Fin.ext
  rw [hp]
  simp only [Fin.ext_iff, ntSuccAbove_val, Fin.val_last]
  rw [ha]
  simp only [Fin.ext_iff, Fin.val_last] at hcrossv ⊢
  split_ifs at hcrossv ⊢ <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_symm_succAbove](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_symm_succAbove {m : ℕ} (hm : 0 < m)
  (p : Fin (m + 1)) (z : Fin m)
  (hcross : p.succAbove z ≠ finRotate (m + 1) p) :
  p.succAbove ((finRotate m).symm z) =
    (finRotate (m + 1)).symm (p.succAbove z) := by
  let a := (finRotate m).symm z
  have hza : finRotate m a = z := by
    exact (finRotate m).apply_symm_apply z
  have hskip : finRotate (m + 1) (p.succAbove a) ≠ p := by
    intro h
    apply hcross
    have hc := ntRotate_succAbove_cross hm p a h
    rwa [hza] at hc
  have h := ntRotate_succAbove hm p a hskip
  rw [hza] at h
  apply (finRotate (m + 1)).injective
  rwa [(finRotate (m + 1)).apply_symm_apply]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_symm_zero {m : ℕ} [NeZero m] :
  (finRotate m).symm 0 = (⟨m - 1, by have := NeZero.ne m; omega⟩ : Fin m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  apply (finRotate (r + 1)).injective
  rw [(finRotate (r + 1)).apply_symm_apply]
  have hlast : (⟨r.succ - 1, by omega⟩ : Fin (r + 1)) = Fin.last r := by
    apply Fin.ext
    simp
  rw [hlast, finRotate_last]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntSuccAbove_straddle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntSuccAbove_straddle {m : ℕ} (hm : 0 < m)
  (v : Fin (m + 1)) (u w : Fin m)
  (hu : v.succAbove u = finRotate (m + 1) v)
  (hw : v.succAbove w = (finRotate (m + 1)).symm v) :
  w = (finRotate m).symm u := by
  let _ : NeZero m := ⟨by omega⟩
  have hu' := congrArg Fin.val hu
  have hw' := congrArg Fin.val hw
  rw [ntSuccAbove_val, coe_finRotate] at hu'
  rw [ntSuccAbove_val] at hw'
  by_cases hvlast : v = Fin.last m
  · have hv : v.val = m := by simp [hvlast]
    have hu0 : u.val = 0 := by
      simp only [hvlast, Fin.val_last, ite_true] at hu'
      split_ifs at hu'
      all_goals omega
    have hvzero : v ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    rw [coe_finRotate_symm_of_ne_zero hvzero] at hw'
    have hwlast : w.val = m - 1 := by
      split_ifs at hw' <;> omega
    have huEq : u = 0 := Fin.ext hu0
    rw [huEq, ntRotate_symm_zero]
    apply Fin.ext
    exact hwlast
  · have hvlt : v.val < m := by
    have hv := v.is_lt
    have hvne : v.val ≠ m := by
      intro h
      apply hvlast
      apply Fin.ext
      simpa only [Fin.val_last] using h
    omega
    simp only [ite_eq_right hvlast] at hu'
    by_cases hvzero : v = 0
    · have hv : v.val = 0 := by simp [hvzero]
      have hu0 : u.val = 0 := by
        rw [hv] at hu'
        split_ifs at hu' <;> omega
      rw [hvzero, ntRotate_symm_zero] at hw'
      have hwlast : w.val = m - 1 := by
        change (if w.val < 0 then w.val else w.val + 1) = m at hw'
        split_ifs at hw' <;> omega
      have huEq : u = 0 := Fin.ext hu0
      rw [huEq, ntRotate_symm_zero]
      apply Fin.ext
      exact hwlast
    · have hvpos : 0 < v.val := by
      have : v.val ≠ 0 := fun h => hvzero (Fin.ext h)
      omega
      have huval : u.val = v.val := by
        split_ifs at hu' <;> omega
      rw [coe_finRotate_symm_of_ne_zero hvzero] at hw'
      have hwval : w.val = v.val - 1 := by
        split_ifs at hw' <;> omega
      have hune : u ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero] at this
        omega
      apply Fin.ext
      rwa [coe_finRotate_symm_of_ne_zero hune, huval]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreak_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreak_lift {m : ℕ} (hm : 0 < m)
  (y v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) {z : Fin m}
  (hz : z ∈ ntBreaks ρ)
  (hcross : finRotate (m + 1) (y.succAbove z) ≠ y) :
  y.succAbove z ∈ ntBreaks (ntIns y v ρ) := by
  let _ : NeZero m := ⟨by omega⟩
  rw [nt_mem_breaks_iff] at hz ⊢
  rw [ntRotate_succAbove hm y z hcross, ntIns_apply_succAbove,
    ntIns_apply_succAbove]
  by_cases hv : v.succAbove (ρ z) = finRotate (m + 1) v
  · rw [hv, (finRotate (m + 1)).symm_apply_apply]
    exact Fin.succAbove_ne v (ρ (finRotate m z))
  · rw [← ntRotate_symm_succAbove hm v (ρ z) hv]
    intro h
    exact hz (Fin.succAbove_right_injective h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreak_cross_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreak_cross_lift {m : ℕ} (hm : 0 < m)
  (y v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) {z : Fin m}
  (hz : z ∈ ntBreaks ρ)
  (hcross : finRotate (m + 1) (y.succAbove z) = y) :
  y.succAbove z ∈ ntBreaks (ntIns y v ρ) ∨
    y ∈ ntBreaks (ntIns y v ρ) := by
  let _ : NeZero m := ⟨by omega⟩
  by_contra h
  simp only [not_or] at h
  have hgoodw : ntIns y v ρ (finRotate (m + 1) (y.succAbove z)) =
    (finRotate (m + 1)).symm (ntIns y v ρ (y.succAbove z)) := by
    by_contra hne
    exact h.1 ((nt_mem_breaks_iff (ntIns y v ρ) (y.succAbove z)).2 hne)
  have hgoodw' : v = (finRotate (m + 1)).symm (v.succAbove (ρ z)) := by
    simpa only [hcross, ntIns_apply_same, ntIns_apply_succAbove] using hgoodw
  have hu : v.succAbove (ρ z) = finRotate (m + 1) v := by
    have heq := congrArg (finRotate (m + 1)) hgoodw'
    rwa [(finRotate (m + 1)).apply_symm_apply] at heq
  have hgoody : ntIns y v ρ (finRotate (m + 1) y) =
    (finRotate (m + 1)).symm (ntIns y v ρ y) := by
    by_contra hne
    exact h.2 ((nt_mem_breaks_iff (ntIns y v ρ) y).2 hne)
  have hpos := ntRotate_succAbove_cross hm y z hcross
  have hw : v.succAbove (ρ (finRotate m z)) =
    (finRotate (m + 1)).symm v := by
    calc
      v.succAbove (ρ (finRotate m z)) =
        ntIns y v ρ (y.succAbove (finRotate m z)) :=
        (ntIns_apply_succAbove y v ρ (finRotate m z)).symm
      _ = ntIns y v ρ (finRotate (m + 1) y) := by rw [hpos]
      _ = (finRotate (m + 1)).symm (ntIns y v ρ y) := hgoody
      _ = (finRotate (m + 1)).symm v := by rw [ntIns_apply_same]
  have hzneq := (nt_mem_breaks_iff ρ z).1 hz
  exact hzneq (ntSuccAbove_straddle hm v (ρ z) (ρ (finRotate m z)) hu hw)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreakMap_eq_succAbove_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreakMap_eq_succAbove_of_ne {m : ℕ} (y v : Fin (m + 1))
  (ρ : Equiv.Perm (Fin m)) (z : Fin m) (h : ntBreakMap y v ρ z ≠ y) :
  ntBreakMap y v ρ z = y.succAbove z := by
  unfold ntBreakMap at h ⊢
  dsimp only at h ⊢
  by_cases hc : finRotate (m + 1) (y.succAbove z) = y
  · rw [ite_eq_left hc] at h ⊢
    by_cases hmemb : y.succAbove z ∈ ntBreaks (ntIns y v ρ)
    · rw [ite_eq_left hmemb] at h ⊢
    · rw [ite_eq_right hmemb] at h ⊢
      exact False.elim (h rfl)
  · rw [ite_eq_right hc] at h ⊢

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreakMap_cross_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreakMap_cross_of_eq {m : ℕ} (y v : Fin (m + 1))
  (ρ : Equiv.Perm (Fin m)) (z : Fin m) (h : ntBreakMap y v ρ z = y) :
  finRotate (m + 1) (y.succAbove z) = y := by
  unfold ntBreakMap at h
  dsimp only at h
  by_cases hc : finRotate (m + 1) (y.succAbove z) = y
  · exact hc
  · rw [ite_eq_right hc] at h
    exact False.elim (Fin.succAbove_ne y z h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreakMap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreakMap_mem {m : ℕ} (hm : 0 < m)
  (y v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) {z : Fin m}
  (hz : z ∈ ntBreaks ρ) :
  ntBreakMap y v ρ z ∈ ntBreaks (ntIns y v ρ) := by
  unfold ntBreakMap
  dsimp only
  by_cases hcross : finRotate (m + 1) (y.succAbove z) = y
  · rw [ite_eq_left hcross]
    by_cases hw : y.succAbove z ∈ ntBreaks (ntIns y v ρ)
    · rw [ite_eq_left hw]
      exact hw
    · rw [ite_eq_right hw]
      obtain h | h := ntBreak_cross_lift hm y v ρ hz hcross
      · exact False.elim (hw h)
      · exact h
  · rw [ite_eq_right hcross]
    exact ntBreak_lift hm y v ρ hz hcross

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreakMap_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreakMap_injOn {m : ℕ}
  (y v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
  (ntBreaks ρ : Set (Fin m)).InjOn (ntBreakMap y v ρ) := by
  intro z₁ _ z₂ _ heq
  have hnot_out (z : Fin m) (h : ntBreakMap y v ρ z ≠ y) :
    ntBreakMap y v ρ z = y.succAbove z := by
    unfold ntBreakMap at h ⊢
    dsimp only at h ⊢
    by_cases hc : finRotate (m + 1) (y.succAbove z) = y
    · rw [ite_eq_left hc] at h ⊢
      by_cases hmemb : y.succAbove z ∈ ntBreaks (ntIns y v ρ)
      · rw [ite_eq_left hmemb] at h ⊢
      · rw [ite_eq_right hmemb] at h ⊢
        exact False.elim (h rfl)
    · rw [ite_eq_right hc] at h ⊢
  have hcross_out (z : Fin m) (h : ntBreakMap y v ρ z = y) :
    finRotate (m + 1) (y.succAbove z) = y := by
    unfold ntBreakMap at h
    dsimp only at h
    by_cases hc : finRotate (m + 1) (y.succAbove z) = y
    · exact hc
    · rw [ite_eq_right hc] at h
      exact False.elim (Fin.succAbove_ne y z h)
  apply Fin.succAbove_right_injective (p := y)
  by_cases h₁ : ntBreakMap y v ρ z₁ = y
  · have h₂ : ntBreakMap y v ρ z₂ = y := by rw [← heq]; exact h₁
    apply (finRotate (m + 1)).injective
    rw [hcross_out z₁ h₁, hcross_out z₂ h₂]
  · have h₂ : ntBreakMap y v ρ z₂ ≠ y := by
    intro h
    apply h₁
    rw [heq, h]
    change y.succAbove z₁ = y.succAbove z₂
    rwa [← hnot_out z₁ h₁, ← hnot_out z₂ h₂]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreaks_delete_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreaks_delete_card_le {m : ℕ} (hm : 0 < m)
  (y v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
  (ntBreaks ρ).card ≤ (ntBreaks (ntIns y v ρ)).card := by
  apply Finset.card_le_card_of_injOn (ntBreakMap y v ρ)
  · intro z hz
    exact ntBreakMap_mem hm y v ρ hz
  · exact ntBreakMap_injOn y v ρ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreaks_ins_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreaks_ins_cases {m : ℕ} (hm : 0 < m)
  (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m))
  (hρ : ntBreaks ρ = ∅) {i : Fin (m + 1)}
  (hi : i ∈ ntBreaks (ntIns p v ρ)) :
  i = (finRotate (m + 1)).symm p ∨ i = p ∨
    i = (ntIns p v ρ).symm (finRotate (m + 1) v) := by
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  by_contra hcases
  simp only [not_or] at hcases
  obtain ⟨hiprev, hip, hicross⟩ := hcases
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hip
  have hskip : finRotate (m + 1) (p.succAbove a) ≠ p := by
    intro h
    apply hiprev
    apply (finRotate (m + 1)).injective
    rwa [(finRotate (m + 1)).apply_symm_apply]
  have hpos := ntRotate_succAbove hm p a hskip
  have hvalcross : v.succAbove (ρ a) ≠ finRotate (m + 1) v := by
    intro h
    apply hicross
    apply (ntIns p v ρ).injective
    rwa [ntIns_apply_succAbove, (ntIns p v ρ).apply_symm_apply]
  have hρgood : ρ (finRotate m a) = (finRotate m).symm (ρ a) := by
    by_contra h
    have ha : a ∈ ntBreaks ρ := (nt_mem_breaks_iff ρ a).2 h
    rw [hρ] at ha
    simp at ha
  have hgood : (ntIns p v ρ) (finRotate (m + 1) (p.succAbove a)) =
    (finRotate (m + 1)).symm ((ntIns p v ρ) (p.succAbove a)) := by
    rw [hpos, ntIns_apply_succAbove, ntIns_apply_succAbove, hρgood,
      ntRotate_symm_succAbove hm v (ρ a) hvalcross]
  exact (nt_mem_breaks_iff (ntIns p v ρ) (p.succAbove a)).1 hi hgood

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDefect_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDefect_sign {n : ℕ} (π : Equiv.Perm (Fin n)) :
  Equiv.Perm.sign (ntDefect π) = 1 := by
  have hsq : ∀ τ : Equiv.Perm (Fin n),
    Equiv.Perm.sign τ * Equiv.Perm.sign τ = 1 := by
    intro τ
    rw [← Equiv.Perm.sign_symm τ, ← Equiv.Perm.sign_mul]
    simp
  rw [ntDefect, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_symm]
  calc
    Equiv.Perm.sign (finRotate n) * Equiv.Perm.sign π *
      Equiv.Perm.sign (finRotate n) * Equiv.Perm.sign π =
      (Equiv.Perm.sign (finRotate n) * Equiv.Perm.sign (finRotate n)) *
        (Equiv.Perm.sign π * Equiv.Perm.sign π) := by ac_rfl
    _ = 1 := by rw [hsq, hsq, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_card_breaks_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_card_breaks_ne_two {n : ℕ} (π : Equiv.Perm (Fin n)) :
  (ntBreaks π).card ≠ 2 := by
  intro h
  have hsupp : (ntDefect π).support.card = 2 := by
    rwa [← nt_card_breaks]
  have hswap : (ntDefect π).IsSwap := Equiv.Perm.card_support_eq_two.mp hsupp
  have hs := hswap.sign_eq
  rw [ntDefect_sign] at hs
  norm_num at hs

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBreaks_ins_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBreaks_ins_subset {m : ℕ} (hm : 0 < m)
  (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m))
  (hρ : ntBreaks ρ = ∅) :
  ntBreaks (ntIns p v ρ) ⊆
    {(finRotate (m + 1)).symm p, p,
      (ntIns p v ρ).symm (finRotate (m + 1) v)} := by
  intro i hi
  obtain h | h | h := ntBreaks_ins_cases hm p v ρ hρ hi
  · simp [h]
  · simp [h]
  · simp [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_symm_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_symm_ne_self {n : ℕ} (hn : 2 ≤ n) (y : Fin n) :
  (finRotate n).symm y ≠ y := by
  intro h
  have h' := congrArg (finRotate n) h
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h'
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hc : y + 0 = y + 1 := by simpa only [add_zero] using h'
  have h01 : (0 : Fin (2 + r)) = 1 := add_left_cancel hc
  apply (show (0 : Fin (2 + r)) ≠ 1 from ?_) h01
  intro e
  have e' := congrArg Fin.val e
  norm_num at e'
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_symm_sq_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_symm_sq_ne_self {n : ℕ} (hn : 3 ≤ n) (y : Fin n) :
  (finRotate n).symm ((finRotate n).symm y) ≠ y := by
  intro h
  have h' := congrArg (finRotate n) h
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h'
  have h'' := congrArg (finRotate n) h'
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h''
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hc : y + 0 = y + (1 + 1) := by simpa only [add_zero, add_assoc] using h''
  have h02 : (0 : Fin (3 + r)) = 1 + 1 := add_left_cancel hc
  have hsum : (1 + 1 : Fin (3 + r)) = ⟨2, by omega⟩ := by
    apply Fin.ext
    have hsmall : 1 < 3 + r := by omega
    have hone : ((1 : Fin (3 + r)) : ℕ) = 1 := Nat.mod_eq_of_lt hsmall
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hone]
    · rw [hone]
      omega
  rw [hsum] at h02
  have h02' := congrArg Fin.val h02
  norm_num at h02'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntRotate_symm_cube_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntRotate_symm_cube_ne_self {n : ℕ} (hn : 4 ≤ n) (y : Fin n) :
  (finRotate n).symm ((finRotate n).symm ((finRotate n).symm y)) ≠ y := by
  intro h
  have h' := congrArg (finRotate n) h
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h'
  have h'' := congrArg (finRotate n) h'
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h''
  have h''' := congrArg (finRotate n) h''
  simp only [(finRotate n).apply_symm_apply, finRotate_apply] at h'''
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hc : y + 0 = y + (1 + 1 + 1) := by
    simpa only [add_zero, add_assoc] using h'''
  have h03 : (0 : Fin (4 + r)) = 1 + 1 + 1 := add_left_cancel hc
  have hsum2 : (1 + 1 : Fin (4 + r)) = ⟨2, by omega⟩ := by
    apply Fin.ext
    have hsmall : 1 < 4 + r := by omega
    have hone : ((1 : Fin (4 + r)) : ℕ) = 1 := Nat.mod_eq_of_lt hsmall
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hone]
    · rw [hone]
      omega
  have hsum3 : (1 + 1 + 1 : Fin (4 + r)) = ⟨3, by omega⟩ := by
    rw [hsum2]
    apply Fin.ext
    have hsmall : 1 < 4 + r := by omega
    have hone : ((1 : Fin (4 + r)) : ℕ) = 1 := Nat.mod_eq_of_lt hsmall
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hone]
    · rw [hone]
      change 2 + 1 < 4 + r
      omega
  rw [hsum3] at h03
  have h03' := congrArg Fin.val h03
  norm_num at h03'

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_mem_DSemi_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_mem_DSemi_iff {m : ℕ} (α : Equiv.Perm (Fin (m + 1)))
  (y : Fin (m + 1)) :
  y ∈ ntDSemi α ↔
    ∃ ρ : Equiv.Perm (Fin m), α = ntIns y (α y) ρ ∧ ntSemi ρ := by
  classical
  simp [ntDSemi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOccurrence_positions_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOccurrence_positions_card {n : ℕ} {σ : Equiv.Perm (Fin n)}
  (o : ntOccurrence σ) : o.positions.card = 4 := by
  have hab : o.a ≠ o.b := by intro h; have := o.hab; rw [h] at this; omega
  have hac : o.a ≠ o.c := by intro h; have := lt_trans o.hab o.hbc; rw [h] at this; omega
  have had : o.a ≠ o.d := by
    intro h
    have := lt_trans o.hab (lt_trans o.hbc o.hcd)
    rw [h] at this
    omega
  have hbc : o.b ≠ o.c := by intro h; have := o.hbc; rw [h] at this; omega
  have hbd : o.b ≠ o.d := by intro h; have := lt_trans o.hbc o.hcd; rw [h] at this; omega
  have hcd : o.c ≠ o.d := by intro h; have := o.hcd; rw [h] at this; omega
  simp [ntOccurrence.positions, hab, hac, had, hbc, hbd, hcd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntChoose_occurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntChoose_occurrence {k : ℕ} (hk : 6 ≤ k)
  {σ : Equiv.Perm (Fin (k + 2))}
  (hE : σ 0 ≠ Fin.last (k + 1) ∧ σ (Fin.last (k + 1)) ≠ 0)
  (hpat : ntPat (k + 2) σ) :
  ∃ o : ntOccurrence σ,
    (σ 0 = ⟨k, by omega⟩ ∧ σ 1 = Fin.last (k + 1) →
      (0 : Fin (k + 2)) ∈ o.positions ∧ (1 : Fin (k + 2)) ∈ o.positions) ∧
    (σ ⟨k, by omega⟩ = 0 ∧ σ (Fin.last (k + 1)) = 1 →
      (⟨k, by omega⟩ : Fin (k + 2)) ∈ o.positions ∧
        Fin.last (k + 1) ∈ o.positions) := by
  let N2 : Fin (k + 2) := ⟨k, by omega⟩
  let N1 : Fin (k + 2) := Fin.last (k + 1)
  have hEfirst : σ 0 ≠ N1 := by simpa only [N1] using hE.1
  have hElast : σ N1 ≠ 0 := by simpa only [N1] using hE.2
  by_cases hs : σ 0 = N2 ∧ σ 1 = N1
  · by_cases he : σ N2 = 0 ∧ σ N1 = 1
    · let o : ntOccurrence σ :=
      { a := 0
        b := 1
        c := N2
        d := N1
        hab := by norm_num
        hbc := by change 1 < k; omega
        hcd := by change k < k + 1; omega
        hpat := Or.inr ⟨by rw [he.1, he.2]; norm_num,
          by rw [he.2, hs.1]; change 1 < k; omega,
          by rw [hs.1, hs.2]; change k < k + 1; omega⟩ }
      refine ⟨o, ?_, ?_⟩
      · intro _
        simp [o, ntOccurrence.positions, N2, N1]
      · intro _
        simp [o, ntOccurrence.positions, N2, N1]
    · let C : Fin (k + 2) := σ.symm 0
      have hσC : σ C = 0 := by simp [C]
      have hC0 : C ≠ 0 := by
        intro h
        have hp : (0 : Fin (k + 2)) = N2 :=
          hσC.symm.trans ((congrArg σ h).trans hs.1)
        have hv := congrArg Fin.val hp
        change 0 = k at hv
        omega
      have hC1 : C ≠ 1 := by
        intro h
        have hp : (0 : Fin (k + 2)) = N1 :=
          hσC.symm.trans ((congrArg σ h).trans hs.2)
        have hv := congrArg Fin.val hp
        change 0 = k + 1 at hv
        omega
      have hCN1 : C ≠ N1 := by
        intro h
        apply hElast
        rwa [← h]
      have hlastN2 : σ N1 ≠ N2 := by
        intro h
        have hp : N1 = 0 := σ.injective (h.trans hs.1.symm)
        have hv := congrArg Fin.val hp
        change k + 1 = 0 at hv
        omega
      have hlastN1 : σ N1 ≠ N1 := by
        intro h
        have hp : N1 = 1 := σ.injective (h.trans hs.2.symm)
        have hv := congrArg Fin.val hp
        change k + 1 = 1 at hv
        omega
      have h0last : (0 : Fin (k + 2)) < σ N1 := by
        change 0 < (σ N1).val
        have hz : (σ N1).val ≠ 0 := fun e => hElast (Fin.ext e)
        omega
      have hlastTop : σ N1 < N2 := by
        rw [Fin.lt_def]
        have hv := (σ N1).is_lt
        simp only [N2]
        by_contra h
        have hor : (σ N1).val = k ∨ (σ N1).val = k + 1 := by omega
        obtain hor | hor := hor
        · exact hlastN2 (Fin.ext hor)
        · exact hlastN1 (Fin.ext (by simpa only [N1, Fin.val_last] using hor))
      let o : ntOccurrence σ :=
        { a := 0
          b := 1
          c := C
          d := N1
          hab := by norm_num
          hbc := by
            change 1 < C.val
            have hC0v : C.val ≠ 0 := fun h => hC0 (Fin.ext h)
            have hC1v : C.val ≠ 1 := fun h => hC1 (Fin.ext h)
            omega
          hcd := by
            have hCv := C.is_lt
            change C.val < k + 1
            have hCN1v : C.val ≠ k + 1 := by
              intro h
              apply hCN1
              apply Fin.ext
              simpa only [N1, Fin.val_last] using h
            omega
          hpat := Or.inr ⟨by rw [hσC]; exact h0last,
            by rw [hs.1]; exact hlastTop,
            by rw [hs.1, hs.2]; change k < k + 1; omega⟩ }
      refine ⟨o, ?_, ?_⟩
      · intro _
        simp [o, ntOccurrence.positions, N1]
      · intro h
        exact False.elim (he h)
  · by_cases he : σ N2 = 0 ∧ σ N1 = 1
    · let B : Fin (k + 2) := σ.symm N1
      have hσB : σ B = N1 := by simp [B]
      have hB0 : B ≠ 0 := by
        intro h
        apply hEfirst
        rwa [← h]
      have hBN2 : B ≠ N2 := by
        intro h
        have hp : N1 = (0 : Fin (k + 2)) :=
          hσB.symm.trans ((congrArg σ h).trans he.1)
        have hv := congrArg Fin.val hp
        change k + 1 = 0 at hv
        omega
      have hBN1 : B ≠ N1 := by
        intro h
        have hp : N1 = (1 : Fin (k + 2)) :=
          hσB.symm.trans ((congrArg σ h).trans he.2)
        have hv := congrArg Fin.val hp
        change k + 1 = 1 at hv
        omega
      have hσ0zero : σ 0 ≠ 0 := by
        intro h
        have hp : (0 : Fin (k + 2)) = N2 := σ.injective (h.trans he.1.symm)
        have hv := congrArg Fin.val hp
        change 0 = k at hv
        omega
      have hσ0one : σ 0 ≠ 1 := by
        intro h
        have hp : (0 : Fin (k + 2)) = N1 := σ.injective (h.trans he.2.symm)
        have hv := congrArg Fin.val hp
        change 0 = k + 1 at hv
        omega
      have hσ0pos : (1 : Fin (k + 2)) < σ 0 := by
        rw [Fin.lt_def]
        have hv := (σ 0).is_lt
        have hz : (σ 0).val ≠ 0 := fun e => hσ0zero (Fin.ext e)
        have ho : (σ 0).val ≠ 1 := fun e => hσ0one (Fin.ext e)
        change 1 < (σ 0).val
        omega
      let o : ntOccurrence σ :=
        { a := 0
          b := B
          c := N2
          d := N1
          hab := by
            change 0 < B.val
            have hB0v : B.val ≠ 0 := fun h => hB0 (Fin.ext h)
            omega
          hbc := by
            have hBv := B.is_lt
            change B.val < k
            have hBN2v : B.val ≠ k := by
              intro h
              apply hBN2
              apply Fin.ext
              simpa only [N2] using h
            have hBN1v : B.val ≠ k + 1 := by
              intro h
              apply hBN1
              apply Fin.ext
              simpa only [N1, Fin.val_last] using h
            omega
          hcd := by change k < k + 1; omega
          hpat := Or.inr ⟨by rw [he.1, he.2]; norm_num,
            by rw [he.2]; exact hσ0pos,
            by rw [hσB]; exact lt_of_le_of_ne (Fin.le_last _) hEfirst⟩ }
      refine ⟨o, ?_, ?_⟩
      · intro h
        exact False.elim (hs h)
      · intro _
        simp [o, ntOccurrence.positions, N2, N1]
    · rcases hpat with hp | hp
      · obtain ⟨a, b, c, d, hab, hbc, hcd, hvab, hvbc, hvcd⟩ := hp
        let o : ntOccurrence σ := ⟨a, b, c, d, hab, hbc, hcd,
          Or.inl ⟨hvab, hvbc, hvcd⟩⟩
        exact ⟨o, fun h => False.elim (hs h), fun h => False.elim (he h)⟩
      · obtain ⟨a, b, c, d, hab, hbc, hcd, hvcd, hvda, hvab⟩ := hp
        let o : ntOccurrence σ := ⟨a, b, c, d, hab, hbc, hcd,
          Or.inr ⟨hvcd, hvda, hvab⟩⟩
        exact ⟨o, fun h => False.elim (hs h), fun h => False.elim (he h)⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOccurrence_delete_data](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOccurrence_delete_data {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))}
  (o : ntOccurrence σ) {y : Fin (m + 1)} {ρ : Equiv.Perm (Fin m)}
  (hσρ : σ = ntIns y (σ y) ρ) (hy : y ∉ o.positions) :
  ∃ o' : ntOccurrence ρ,
    y.succAbove o'.a = o.a ∧ y.succAbove o'.b = o.b ∧
      y.succAbove o'.c = o.c ∧ y.succAbove o'.d = o.d := by
  have hya : o.a ≠ y := by
    intro h
    apply hy
    simp [ntOccurrence.positions, h]
  have hyb : o.b ≠ y := by
    intro h
    apply hy
    simp [ntOccurrence.positions, h]
  have hyc : o.c ≠ y := by
    intro h
    apply hy
    simp [ntOccurrence.positions, h]
  have hyd : o.d ≠ y := by
    intro h
    apply hy
    simp [ntOccurrence.positions, h]
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hya
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hyb
  obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hyc
  obtain ⟨d, hd⟩ := Fin.exists_succAbove_eq hyd
  have hab : a.val < b.val := by
    rw [← Fin.lt_def]
    rw [← Fin.succAbove_lt_succAbove_iff (p := y), ha, hb]
    exact Fin.lt_def.mpr o.hab
  have hbc : b.val < c.val := by
    rw [← Fin.lt_def]
    rw [← Fin.succAbove_lt_succAbove_iff (p := y), hb, hc]
    exact Fin.lt_def.mpr o.hbc
  have hcd : c.val < d.val := by
    rw [← Fin.lt_def]
    rw [← Fin.succAbove_lt_succAbove_iff (p := y), hc, hd]
    exact Fin.lt_def.mpr o.hcd
  have hva : σ o.a = (σ y).succAbove (ρ a) := by
    calc
      σ o.a = ntIns y (σ y) ρ o.a := congrArg (fun τ => τ o.a) hσρ
      _ = (σ y).succAbove (ρ a) := by rw [← ha, ntIns_apply_succAbove]
  have hvb : σ o.b = (σ y).succAbove (ρ b) := by
    calc
      σ o.b = ntIns y (σ y) ρ o.b := congrArg (fun τ => τ o.b) hσρ
      _ = (σ y).succAbove (ρ b) := by rw [← hb, ntIns_apply_succAbove]
  have hvc : σ o.c = (σ y).succAbove (ρ c) := by
    calc
      σ o.c = ntIns y (σ y) ρ o.c := congrArg (fun τ => τ o.c) hσρ
      _ = (σ y).succAbove (ρ c) := by rw [← hc, ntIns_apply_succAbove]
  have hvd : σ o.d = (σ y).succAbove (ρ d) := by
    calc
      σ o.d = ntIns y (σ y) ρ o.d := congrArg (fun τ => τ o.d) hσρ
      _ = (σ y).succAbove (ρ d) := by rw [← hd, ntIns_apply_succAbove]
  obtain h1234 | h3412 := o.hpat
  · refine ⟨⟨a, b, c, d, hab, hbc, hcd, Or.inl ⟨?_, ?_, ?_⟩⟩,
    ha, hb, hc, hd⟩
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hva, hvb] using h1234.1)
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hvb, hvc] using h1234.2.1)
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hvc, hvd] using h1234.2.2)
  · refine ⟨⟨a, b, c, d, hab, hbc, hcd, Or.inr ⟨?_, ?_, ?_⟩⟩,
    ha, hb, hc, hd⟩
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hvc, hvd] using h3412.1)
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hvd, hva] using h3412.2.1)
    · exact (Fin.succAbove_lt_succAbove_iff (p := σ y)).mp
      (by simpa [hva, hvb] using h3412.2.2)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntOccurrence_delete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntOccurrence_delete {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))}
  (o : ntOccurrence σ) {y : Fin (m + 1)} {ρ : Equiv.Perm (Fin m)}
  (hσρ : σ = ntIns y (σ y) ρ) (hy : y ∉ o.positions) : ntPat m ρ := by
  obtain ⟨o', -, -, -, -⟩ := ntOccurrence_delete_data o hσρ hy
  obtain h | h := o'.hpat
  · exact Or.inl ⟨o'.a, o'.b, o'.c, o'.d, o'.hab, o'.hbc, o'.hcd,
    h.1, h.2.1, h.2.2⟩
  · exact Or.inr ⟨o'.a, o'.b, o'.c, o'.d, o'.hab, o'.hbc, o'.hcd,
    h.1, h.2.1, h.2.2⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDoubleSwap_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDoubleSwap_support {n : ℕ} {a b c d : Fin n}
  (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
  (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n)).support =
    {a, b, c, d} := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac : a ≠ c := by intro h; subst c; omega
  have had : a ≠ d := by intro h; subst d; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hbd : b ≠ d := by intro h; subst d; omega
  have hcd' : c ≠ d := by intro h; subst d; omega
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hout
    simp only [not_or] at hout
    apply hx
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hout.2.1 hout.2.2.2,
      Equiv.swap_apply_of_ne_of_ne hout.1 hout.2.2.1]
  · intro hx
    obtain rfl | rfl | rfl | rfl := hx
    · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hab' had, Equiv.swap_apply_left]
      exact hac.symm
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hcd')]
      exact hbd.symm
    · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hbc') hcd', Equiv.swap_apply_right]
      exact hac
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hab') hbc']
      exact hbd

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_mem_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_mem_boundary_iff {n : ℕ} [NeZero n]
  (P : Finset (Fin n)) (i : Fin n) :
  i ∈ ntBoundary P ↔ (i ∈ P ↔ finRotate n i ∉ P) := by
  simp only [ntBoundary, Finset.mem_union, Finset.mem_sdiff, Finset.mem_map,
    Equiv.coe_toEmbedding]
  have hmap : (∃ x ∈ P, (finRotate n).symm x = i) ↔ finRotate n i ∈ P := by
    constructor
    · rintro ⟨x, hx, hxi⟩
      rwa [← hxi, (finRotate n).apply_symm_apply]
    · intro hi
      exact ⟨finRotate n i, hi, (finRotate n).symm_apply_apply i⟩
  rw [hmap]
  tauto

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBoundary_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBoundary_card_even {n : ℕ} (P : Finset (Fin n)) :
  ∃ t : ℕ, (ntBoundary P).card = 2 * t := by
  let Q := P.map (finRotate n).symm.toEmbedding
  have hcardQ : Q.card = P.card := Finset.card_map _
  have hdiff : (P \ Q).card = (Q \ P).card := by
    rwa [Finset.card_sdiff_eq_card_sdiff_iff]
  have hdis : Disjoint (P \ Q) (Q \ P) := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_sdiff.mp hxQ).1
  refine ⟨(P \ Q).card, ?_⟩
  rw [ntBoundary, show P.map (finRotate n).symm.toEmbedding = Q from rfl,
    Finset.card_union_of_disjoint hdis, hdiff]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntBoundary_nonempty {n : ℕ} [NeZero n] (P : Finset (Fin n))
  {x₀ : Fin n} (hx₀ : x₀ ∈ P) (hcard : P.card < n) :
  (ntBoundary P).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hinv (i : Fin n) : i ∈ P ↔ finRotate n i ∈ P := by
    have hi : i ∉ ntBoundary P := by rw [hempty]; simp
    by_cases hiP : i ∈ P
    · refine ⟨fun _ => ?_, fun _ => hiP⟩
      by_contra hriP
      apply hi
      exact (nt_mem_boundary_iff P i).2 ⟨fun _ => hriP, fun _ => hiP⟩
    · refine ⟨fun h => False.elim (hiP h), fun hriP => ?_⟩
      exact False.elim (hi ((nt_mem_boundary_iff P i).2
        ⟨fun h => False.elim (hiP h), fun h => False.elim (h hriP)⟩))
  have hiter : ∀ t : ℕ, ((finRotate n)^[t]) x₀ ∈ P := by
    intro t
    induction t with
    | zero => simpa using hx₀
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (hinv _).mp ih
  have hall : ∀ x : Fin n, x ∈ P := by
    intro x
    let z : Fin n := x - x₀
    have hx : ((finRotate n)^[z.val]) x₀ = x := by
      rw [← finCycle_eq_finRotate_iterate (k := z)]
      simp [finCycle_apply, z]
    rw [← hx]
    exact hiter z.val
  have hPuniv : P = Finset.univ := Finset.eq_univ_of_forall hall
  have : P.card = n := by rw [hPuniv, Finset.card_univ, Fintype.card_fin]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntUnswap_not_semi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntUnswap_not_semi {n : ℕ} {σ : Equiv.Perm (Fin n)}
  (hpat : ntPat n σ)
  (hout : ∀ j : ℕ, ∀ hj : j + 1 ≤ n, σ ∉ ntK n j hj)
  {x z : Fin n} (hxz : x ≠ z) : ¬ntSemi (σ * Equiv.swap x z) := by
  rintro ⟨j, hj, hsemi⟩
  apply hout j hj
  refine ⟨?_, hpat⟩
  refine ⟨x, z, hxz, ?_⟩
  calc
    σ = (σ * Equiv.swap x z) * Equiv.swap x z := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    _ = ntBeta n j hj * Equiv.swap x z := by rw [hsemi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_mem_DSemi_unswap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_mem_DSemi_unswap {m j : ℕ} (hj : j + 1 ≤ m)
  (y : Fin (m + 1)) (v : Fin (m + 1)) (A B : Fin m)
  {σ : Equiv.Perm (Fin (m + 1))}
  (hσ : σ = ntIns y v (ntBeta m j hj * Equiv.swap A B)) :
  y ∈ ntDSemi (σ * Equiv.swap (y.succAbove A) (y.succAbove B)) := by
  rw [nt_mem_DSemi_iff]
  refine ⟨ntBeta m j hj, ?_, ⟨j, hj, rfl⟩⟩
  have hv : (σ * Equiv.swap (y.succAbove A) (y.succAbove B)) y = v := by
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_succAbove y A) (Fin.ne_succAbove y B),
      hσ, ntIns_apply_same]
  calc
    σ * Equiv.swap (y.succAbove A) (y.succAbove B) =
      ntIns y v (ntBeta m j hj * Equiv.swap A B) *
        Equiv.swap (y.succAbove A) (y.succAbove B) := by rw [hσ]
    _ = (ntIns y v (ntBeta m j hj) *
      Equiv.swap (y.succAbove A) (y.succAbove B)) *
      Equiv.swap (y.succAbove A) (y.succAbove B) := by
      rw [ntIns_mul_swap]
    _ = ntIns y v (ntBeta m j hj) := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    _ = ntIns y ((σ * Equiv.swap (y.succAbove A) (y.succAbove B)) y)
      (ntBeta m j hj) := by rw [hv]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletion_memE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletion_memE {k : ℕ}
  {σ : Equiv.Perm (Fin (k + 2))} (hE : σ ∈ ntE (k + 1))
  {y : Fin (k + 2)} {ρ : Equiv.Perm (Fin (k + 1))}
  (hσρ : σ = ntIns y (σ y) ρ)
  (hs0 : ¬(y = 0 ∧ σ 1 = Fin.last (k + 1)))
  (hs1 : ¬(σ 0 = (⟨k, by omega⟩ : Fin (k + 2)) ∧
    y = σ.symm (Fin.last (k + 1))))
  (he0 : ¬(y = Fin.last (k + 1) ∧ σ (⟨k, by omega⟩ : Fin (k + 2)) = 0))
  (he1 : ¬(σ (Fin.last (k + 1)) = 1 ∧ y = σ.symm 0)) :
  ρ ∈ ntE k := by
  constructor
  · intro hbad
    have heval : σ (y.succAbove (0 : Fin (k + 1))) =
      (σ y).succAbove (ρ 0) := by
      calc
        σ (y.succAbove 0) = ntIns y (σ y) ρ (y.succAbove 0) :=
          congrArg (fun τ => τ (y.succAbove 0)) hσρ
        _ = (σ y).succAbove (ρ 0) := ntIns_apply_succAbove _ _ _ _
    rw [hbad] at heval
    by_cases hy0 : y = 0
    · have hpos : y.succAbove (0 : Fin (k + 1)) = 1 := by
      apply Fin.ext
      rw [ntSuccAbove_val]
      simp [hy0]
      have heval' := congrArg Fin.val heval
      rw [hpos, ntSuccAbove_val] at heval'
      simp only [Fin.val_last] at heval'
      have hv := (σ y).is_lt
      have hvlast : (σ y).val ≠ k + 1 := by
        intro h
        apply hE.1
        apply Fin.ext
        simpa [hy0] using h
      have hcmp : ¬k < (σ y).val := by omega
      simp only [ite_eq_right hcmp] at heval'
      apply hs0
      refine ⟨hy0, Fin.ext ?_⟩
      simpa using heval'
    · have hypos : 0 < y.val := by
      have hyne : y.val ≠ 0 := fun h => hy0 (Fin.ext h)
      omega
      have hpos : y.succAbove (0 : Fin (k + 1)) = 0 := by
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp only [Fin.val_zero]
        simp [hypos]
      have heval' := congrArg Fin.val heval
      rw [hpos, ntSuccAbove_val] at heval'
      simp only [Fin.val_last] at heval'
      have hv := (σ y).is_lt
      have hfirst : (σ 0).val ≠ k + 1 := by
        intro h
        apply hE.1
        exact Fin.ext (by simpa using h)
      have hcmp : k < (σ y).val := by
        by_contra h
        simp only [ite_eq_right h] at heval'
        exact hfirst heval'
      simp only [ite_eq_left hcmp] at heval'
      have hvlast : σ y = Fin.last (k + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      apply hs1
      refine ⟨Fin.ext (by simpa using heval'), ?_⟩
      rw [← hvlast]
      simp
  · intro hbad
    have heval : σ (y.succAbove (Fin.last k)) =
      (σ y).succAbove (ρ (Fin.last k)) := by
      calc
        σ (y.succAbove (Fin.last k)) =
          ntIns y (σ y) ρ (y.succAbove (Fin.last k)) :=
          congrArg (fun τ => τ (y.succAbove (Fin.last k))) hσρ
        _ = (σ y).succAbove (ρ (Fin.last k)) := ntIns_apply_succAbove _ _ _ _
    rw [hbad] at heval
    by_cases hylast : y = Fin.last (k + 1)
    · have hpos : y.succAbove (Fin.last k) = (⟨k, by omega⟩ : Fin (k + 2)) := by
      apply Fin.ext
      rw [ntSuccAbove_val]
      simp only [Fin.val_last]
      rw [hylast]
      simp only [Fin.val_last]
      split <;> omega
      have heval' := congrArg Fin.val heval
      rw [hpos, ntSuccAbove_val] at heval'
      simp only [Fin.val_zero] at heval'
      change (σ (⟨k, by omega⟩ : Fin (k + 2))).val =
        if 0 < (σ y).val then 0 else 1 at heval'
      have hvzero : (σ y).val ≠ 0 := by
        intro h
        apply hE.2
        apply Fin.ext
        simpa [hylast] using h
      have hcmp : 0 < (σ y).val := by omega
      simp only [ite_eq_left hcmp] at heval'
      apply he0
      refine ⟨hylast, Fin.ext ?_⟩
      simpa using heval'
    · have hylt : y.val < k + 1 := by
      have hy := y.is_lt
      have hyne : y.val ≠ k + 1 := by
        intro h
        apply hylast
        apply Fin.ext
        simpa only [Fin.val_last] using h
      omega
      have hpos : y.succAbove (Fin.last k) = Fin.last (k + 1) := by
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp only [Fin.val_last]
        split <;> omega
      have heval' := congrArg Fin.val heval
      rw [hpos, ntSuccAbove_val] at heval'
      simp only [Fin.val_zero] at heval'
      change (σ (Fin.last (k + 1))).val =
        if 0 < (σ y).val then 0 else 1 at heval'
      have hv := (σ y).is_lt
      have hlastzero : (σ (Fin.last (k + 1))).val ≠ 0 := by
        intro h
        apply hE.2
        exact Fin.ext h
      have hcmp : ¬0 < (σ y).val := by
        intro h
        simp only [ite_eq_left h] at heval'
        exact hlastzero heval'
      simp only [ite_eq_right hcmp] at heval'
      have hvzero : σ y = 0 := by
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      apply he1
      refine ⟨Fin.ext (by simpa using heval'), ?_⟩
      rw [← hvzero]
      simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntStartBad_sdiff_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntStartBad_sdiff_card {k : ℕ} {σ : Equiv.Perm (Fin (k + 2))}
  (o : ntOccurrence σ)
  (htop : (σ 0 = (⟨k, by omega⟩ : Fin (k + 2)) ∧
    σ 1 = Fin.last (k + 1)) → 0 ∈ o.positions ∧ 1 ∈ o.positions) :
  (ntStartBad σ \ o.positions).card ≤ 1 := by
  by_cases h1 : σ 1 = Fin.last (k + 1)
  · by_cases h0 : σ 0 = (⟨k, by omega⟩ : Fin (k + 2))
    · have hp := htop ⟨h0, h1⟩
      have hinv : σ.symm (Fin.last (k + 1)) = 1 := by
        apply σ.injective
        simp [h1]
      have hempty : ntStartBad σ \ o.positions = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := (Finset.mem_sdiff.mp hx)
        simp only [ntStartBad, h1, h0, ite_true, Finset.union_singleton,
          Finset.mem_insert, Finset.mem_singleton, hinv] at hx'
        obtain rfl | rfl := hx'.1
        · exact hx'.2 hp.2
        · exact hx'.2 hp.1
      rw [hempty]
      simp
    · calc
      (ntStartBad σ \ o.positions).card ≤ (ntStartBad σ).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ ≤ 1 := by simp [ntStartBad, h1, h0]
  · by_cases h0 : σ 0 = (⟨k, by omega⟩ : Fin (k + 2))
    · calc
      (ntStartBad σ \ o.positions).card ≤ (ntStartBad σ).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ ≤ 1 := by simp [ntStartBad, h1, h0]
    · simp [ntStartBad, h1, h0]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEndBad_sdiff_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEndBad_sdiff_card {k : ℕ} {σ : Equiv.Perm (Fin (k + 2))}
  (o : ntOccurrence σ)
  (hbottom : (σ (⟨k, by omega⟩ : Fin (k + 2)) = 0 ∧
    σ (Fin.last (k + 1)) = 1) →
      (⟨k, by omega⟩ : Fin (k + 2)) ∈ o.positions ∧
        Fin.last (k + 1) ∈ o.positions) :
  (ntEndBad σ \ o.positions).card ≤ 1 := by
  by_cases h0 : σ (⟨k, by omega⟩ : Fin (k + 2)) = 0
  · by_cases h1 : σ (Fin.last (k + 1)) = 1
    · have hp := hbottom ⟨h0, h1⟩
      have hinv : σ.symm 0 = (⟨k, by omega⟩ : Fin (k + 2)) := by
        apply σ.injective
        simp [h0]
      have hempty : ntEndBad σ \ o.positions = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := Finset.mem_sdiff.mp hx
        simp only [ntEndBad, h0, h1, ite_true, Finset.union_singleton,
          Finset.mem_insert, Finset.mem_singleton, hinv] at hx'
        obtain rfl | rfl := hx'.1
        · exact hx'.2 hp.1
        · exact hx'.2 hp.2
      rw [hempty]
      simp
    · calc
      (ntEndBad σ \ o.positions).card ≤ (ntEndBad σ).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ ≤ 1 := by simp [ntEndBad, h0, h1]
  · by_cases h1 : σ (Fin.last (k + 1)) = 1
    · calc
      (ntEndBad σ \ o.positions).card ≤ (ntEndBad σ).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ ≤ 1 := by simp [ntEndBad, h0, h1]
    · simp [ntEndBad, h0, h1]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEBad_sdiff_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEBad_sdiff_card {k : ℕ} {σ : Equiv.Perm (Fin (k + 2))}
  (o : ntOccurrence σ)
  (htop : (σ 0 = (⟨k, by omega⟩ : Fin (k + 2)) ∧
    σ 1 = Fin.last (k + 1)) → 0 ∈ o.positions ∧ 1 ∈ o.positions)
  (hbottom : (σ (⟨k, by omega⟩ : Fin (k + 2)) = 0 ∧
    σ (Fin.last (k + 1)) = 1) →
      (⟨k, by omega⟩ : Fin (k + 2)) ∈ o.positions ∧
        Fin.last (k + 1) ∈ o.positions) :
  (ntEBad σ \ o.positions).card ≤ 2 := by
  have hs := ntStartBad_sdiff_card o htop
  have he := ntEndBad_sdiff_card o hbottom
  have hsub : ntEBad σ \ o.positions ⊆
    (ntStartBad σ \ o.positions) ∪ (ntEndBad σ \ o.positions) := by
    intro x hx
    simp only [ntEBad, Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    obtain hxS | hxE := hx.1
    · exact Or.inl ⟨hxS, hx.2⟩
    · exact Or.inr ⟨hxE, hx.2⟩
  calc
    (ntEBad σ \ o.positions).card ≤
      ((ntStartBad σ \ o.positions) ∪ (ntEndBad σ \ o.positions)).card :=
      Finset.card_le_card hsub
    _ ≤ (ntStartBad σ \ o.positions).card +
      (ntEndBad σ \ o.positions).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletion_memE_of_not_bad](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletion_memE_of_not_bad {k : ℕ}
  {σ : Equiv.Perm (Fin (k + 2))} (hE : σ ∈ ntE (k + 1))
  {y : Fin (k + 2)} {ρ : Equiv.Perm (Fin (k + 1))}
  (hσρ : σ = ntIns y (σ y) ρ) (hy : y ∉ ntEBad σ) : ρ ∈ ntE k := by
  apply ntDeletion_memE hE hσρ
  · rintro ⟨rfl, h⟩
    apply hy
    simp [ntEBad, ntStartBad, h]
  · rintro ⟨h, hyinv⟩
    apply hy
    simp [ntEBad, ntStartBad, h, hyinv]
  · rintro ⟨rfl, h⟩
    apply hy
    simp [ntEBad, ntEndBad, h]
  · rintro ⟨h, hyinv⟩
    apply hy
    simp [ntEBad, ntEndBad, h, hyinv]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_getD](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_getD {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) (hi : i < n) :
  (ntCode σ).getD i 0 = (σ ⟨i, hi⟩).val := by
  rw [List.getD_eq_getElem]
  · simp [ntCode]
  · simpa [ntCode] using hi

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_injective {n : ℕ} :
  Function.Injective (ntCode : Equiv.Perm (Fin n) → List ℕ) := by
  intro σ τ h
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  have hf : (fun i : Fin n => (σ i).val) = fun i : Fin n => (τ i).val :=
    List.ofFn_injective h
  exact congrFun hf i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_mem_permutations'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_mem_permutations' {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  ntCode σ ∈ List.permutations' (List.range n) := by
  rw [List.mem_permutations']
  have hnodup : (ntCode σ).Nodup := by
    unfold ntCode
    apply List.nodup_ofFn.mpr
    intro i j h
    exact σ.injective (Fin.ext h)
  apply (List.perm_ext_iff_of_nodup hnodup List.nodup_range).2
  intro a
  unfold ntCode
  rw [List.mem_ofFn']
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_range.mpr (σ i).is_lt
  · intro ha
    have ha' := List.mem_range.mp ha
    obtain ⟨i, hi⟩ := σ.surjective ⟨a, ha'⟩
    exact ⟨i, congrArg Fin.val hi⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntQuad_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntQuad_mem {n : ℕ} {a b c d : Fin n}
  (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
  (a.val, b.val, c.val, d.val) ∈ ntQuads n := by
  simp [ntQuads, a.is_lt, b.is_lt, c.is_lt, d.is_lt, hab, hbc, hcd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nt_mem_quads_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma nt_mem_quads_iff {n a b c d : ℕ} :
  (a, b, c, d) ∈ ntQuads n ↔
    a < n ∧ b < n ∧ c < n ∧ d < n ∧ a < b ∧ b < c ∧ c < d := by
  simp [ntQuads]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntHasPatB_of_pat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntHasPatB_of_pat {n : ℕ} {σ : Equiv.Perm (Fin n)}
  (hσ : ntPat n σ) : ntHasPatB (ntQuads n) (ntCode σ) = true := by
  unfold ntHasPatB
  rw [List.any_eq_true]
  obtain ⟨a, b, c, d, hab, hbc, hcd, hvab, hvbc, hvcd⟩ | := hσ
    ⟨a, b, c, d, hab, hbc, hcd, hvcd, hvda, hvab⟩
  · refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
    dsimp only
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨⟨hvab, hvbc⟩, hvcd⟩
  · refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
    dsimp only
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨⟨hvcd, hvda⟩, hvab⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntHasPatB_sound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntHasPatB_sound {n : ℕ} {σ : Equiv.Perm (Fin n)}
  (hσ : ntHasPatB (ntQuads n) (ntCode σ) = true) : ntPat n σ := by
  unfold ntHasPatB at hσ
  rw [List.any_eq_true] at hσ
  obtain ⟨⟨a, b, c, d⟩, hquad, hpat⟩ := hσ
  obtain ⟨ha, hb, hc, hd, hab, hbc, hcd⟩ := nt_mem_quads_iff.mp hquad
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpat
  rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
    ntCode_getD σ c hc, ntCode_getD σ d hd] at hpat
  obtain h1234 | h3412 := hpat
  · exact Or.inl ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩,
    hab, hbc, hcd, h1234.1.1, h1234.1.2, h1234.2⟩
  · exact Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩,
    hab, hbc, hcd, h3412.1.1, h3412.1.2, h3412.2⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_double_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_double_swap {n : ℕ} (σ : Equiv.Perm (Fin n))
  {a b c d : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
  (hcd : c.val < d.val) :
  ntCode (σ * Equiv.swap a c * Equiv.swap b d) =
    ((((ntCode σ).set a.val (σ c).val).set c.val (σ a).val).set b.val
      (σ d).val).set d.val (σ b).val := by
  apply List.ext_getElem
  · simp [ntCode]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [ntCode] using hi₁
    have hac : a ≠ c := by
      intro h
      subst c
      omega
    have had : a ≠ d := by
      intro h
      subst d
      omega
    have hbc' : b ≠ c := by
      intro h
      subst c
      omega
    have hbd : b ≠ d := by
      intro h
      subst d
      omega
    have hcd' : c ≠ d := by
      intro h
      subst d
      omega
    have hab' : a ≠ b := by
      intro h
      subst b
      omega
    simp only [List.getElem_set]
    simp only [ntCode, List.getElem_ofFn]
    simp only [Equiv.Perm.mul_apply]
    by_cases hia : i = a.val
    · have hiA : (⟨i, hi⟩ : Fin n) = a := Fin.ext hia
      subst hiA
      rw [Equiv.swap_apply_of_ne_of_ne hab' had, Equiv.swap_apply_left]
      split_ifs <;> try omega
    · by_cases hib : i = b.val
      · have hiB : (⟨i, hi⟩ : Fin n) = b := Fin.ext hib
        subst hiB
        rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hcd')]
        split_ifs <;> try omega
      · by_cases hic : i = c.val
        · have hiC : (⟨i, hi⟩ : Fin n) = c := Fin.ext hic
          subst hiC
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hbc') hcd',
            Equiv.swap_apply_right]
          split_ifs <;> try omega
        · by_cases hid : i = d.val
          · have hiD : (⟨i, hi⟩ : Fin n) = d := Fin.ext hid
            subst hiD
            rw [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne (Ne.symm hab') hbc']
            split_ifs <;> try omega
          · have hiA : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (congrArg Fin.val h)
            have hiB : (⟨i, hi⟩ : Fin n) ≠ b := fun h => hib (congrArg Fin.val h)
            have hiC : (⟨i, hi⟩ : Fin n) ≠ c := fun h => hic (congrArg Fin.val h)
            have hiD : (⟨i, hi⟩ : Fin n) ≠ d := fun h => hid (congrArg Fin.val h)
            rw [Equiv.swap_apply_of_ne_of_ne hiB hiD,
              Equiv.swap_apply_of_ne_of_ne hiA hiC]
            simp only [ite_eq_right (Ne.symm hid), ite_eq_right (Ne.symm hib),
              ite_eq_right (Ne.symm hic), ite_eq_right (Ne.symm hia)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntNbrs_sound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntNbrs_sound {n : ℕ} {σ : Equiv.Perm (Fin n)} {t : List ℕ}
  (ht : t ∈ ntNbrs (ntQuads n) (ntCode σ)) :
  ∃ τ : Equiv.Perm (Fin n), ntCode τ = t ∧
    (ntMove n σ τ ∨ ntMove n τ σ) := by
  unfold ntNbrs at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨⟨a, b, c, d⟩, hquad, hstep⟩ := ht
  unfold ntNbrAt at hstep
  obtain ⟨ha, hb, hc, hd, hab, hbc, hcd⟩ := nt_mem_quads_iff.mp hquad
  have hpat :
    (((ntCode σ).getD a 0 < (ntCode σ).getD b 0 &&
      (ntCode σ).getD b 0 < (ntCode σ).getD c 0 &&
      (ntCode σ).getD c 0 < (ntCode σ).getD d 0) ||
      ((ntCode σ).getD c 0 < (ntCode σ).getD d 0 &&
        (ntCode σ).getD d 0 < (ntCode σ).getD a 0 &&
        (ntCode σ).getD a 0 < (ntCode σ).getD b 0)) = true := by
    by_contra hfalse
    have heq :
      (((ntCode σ).getD a 0 < (ntCode σ).getD b 0 &&
        (ntCode σ).getD b 0 < (ntCode σ).getD c 0 &&
        (ntCode σ).getD c 0 < (ntCode σ).getD d 0) ||
        ((ntCode σ).getD c 0 < (ntCode σ).getD d 0 &&
          (ntCode σ).getD d 0 < (ntCode σ).getD a 0 &&
          (ntCode σ).getD a 0 < (ntCode σ).getD b 0)) = false :=
      Bool.eq_false_iff.mpr hfalse
    simp only [heq, Bool.false_eq_true, ↓reduceIte] at hstep
    contradiction
  have hresult : t =
    (((((ntCode σ).set a ((ntCode σ).getD c 0)).set c
      ((ntCode σ).getD a 0)).set b ((ntCode σ).getD d 0)).set d
        ((ntCode σ).getD b 0)) := by
    simpa only [hpat, ↓reduceIte, Option.some.injEq] using hstep.symm
  let A : Fin n := ⟨a, ha⟩
  let B : Fin n := ⟨b, hb⟩
  let C : Fin n := ⟨c, hc⟩
  let D : Fin n := ⟨d, hd⟩
  let τ := σ * Equiv.swap A C * Equiv.swap B D
  refine ⟨τ, ?_, ?_⟩
  · rw [hresult]
    change ntCode (σ * Equiv.swap A C * Equiv.swap B D) = _
    rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
      ntCode_getD σ c hc, ntCode_getD σ d hd]
    exact ntCode_double_swap σ hab hbc hcd
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpat
    rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
      ntCode_getD σ c hc, ntCode_getD σ d hd] at hpat
    obtain h1234 | h3412 := hpat
    · exact Or.inl (ntMove_of_1234 hab hbc hcd h1234.1.1 h1234.1.2 h1234.2)
    · exact Or.inr (ntMove_of_3412 hab hbc hcd h3412.1.1 h3412.1.2 h3412.2)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_code_mem_nbrs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_code_mem_nbrs {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
  (h : ntMove n σ τ) : ntCode τ ∈ ntNbrs (ntQuads n) (ntCode σ) := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hvab, hvbc, hvcd,
    ht1, ht2, ht3, ht4, hrest⟩ := h
  have hτ := ntMove_eq hab hbc hcd hvab hvbc hvcd ht1 ht2 ht3 ht4 hrest
  rw [hτ]
  unfold ntNbrs
  rw [List.mem_filterMap]
  refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
  unfold ntNbrAt
  have hcond :
    (((ntCode σ).getD a.val 0 < (ntCode σ).getD b.val 0 &&
      (ntCode σ).getD b.val 0 < (ntCode σ).getD c.val 0 &&
      (ntCode σ).getD c.val 0 < (ntCode σ).getD d.val 0) ||
      ((ntCode σ).getD c.val 0 < (ntCode σ).getD d.val 0 &&
        (ntCode σ).getD d.val 0 < (ntCode σ).getD a.val 0 &&
        (ntCode σ).getD a.val 0 < (ntCode σ).getD b.val 0)) = true := by
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨⟨hvab, hvbc⟩, hvcd⟩
  simp only [hcond, ↓reduceIte, Option.some.injEq]
  rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
    ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
  exact (ntCode_double_swap σ hab hbc hcd).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCertificate5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCertificate5 :
  (List.permutations' (List.range 5)).all
    (ntClassOk 5 9 ntRepCodes5 ntLabel5 ntDistance5) = true := by
  native_decide
set_option maxRecDepth 100000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCertificate6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCertificate6 :
  (List.permutations' (List.range 6)).all
    (ntClassOk 6 26 ntRepCodes6 ntLabel6 ntDistance6) = true := by
  native_decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntClassOk_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntClassOk_parts (n m : ℕ) (reps : List (List ℕ))
  (label distance : List ℕ → ℕ) {s : List ℕ}
  (h : ntClassOk n m reps label distance s = true) :
  (!ntHasPatB (ntQuads n) s || label s < m) = true ∧
    (ntNbrs (ntQuads n) s).all (fun t => label t == label s) = true ∧
    (label s ≥ m || distance s < 15 &&
      if distance s = 0 then s == reps.getD (label s) []
      else (ntNbrs (ntQuads n) s).any fun t =>
        distance t + 1 == distance s) = true := by
  dsimp only [ntClassOk] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntClassOk_code](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntClassOk_code {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ}
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true)
  (σ : Equiv.Perm (Fin n)) :
  ntClassOk n m reps label distance (ntCode σ) = true :=
  (List.all_eq_true.mp hcert) _ (ntCode_mem_permutations' σ)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntPat_label_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntPat_label_lt {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ}
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true)
  {σ : Equiv.Perm (Fin n)} (hσ : ntPat n σ) : label (ntCode σ) < m := by
  have hparts := ntClassOk_parts n m reps label distance
    (ntClassOk_code hcert σ)
  have hpat := ntHasPatB_of_pat hσ
  rw [hpat] at hparts
  simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq] using hparts.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntMove_label_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntMove_label_eq {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ}
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true)
  {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
  label (ntCode σ) = label (ntCode τ) := by
  have hparts := ntClassOk_parts n m reps label distance
    (ntClassOk_code hcert σ)
  have hlabel := (List.all_eq_true.mp hparts.2.1) (ntCode τ)
    (ntMove_code_mem_nbrs h)
  exact (beq_iff_eq.mp hlabel).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntEqvGen_label_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntEqvGen_label_eq {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ}
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true)
  {σ τ : Equiv.Perm (Fin n)} (h : Relation.EqvGen (ntMove n) σ τ) :
  label (ntCode σ) = label (ntCode τ) := by
  induction h with
  | rel a b hab => exact ntMove_label_eq hcert hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDistance_reaches_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDistance_reaches_aux {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ} (rep : Fin m → Equiv.Perm (Fin n))
  (hcode : ∀ k, ntCode (rep k) = reps.getD k.val [])
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true) (d : ℕ) :
  ∀ (σ : Equiv.Perm (Fin n)) (k : Fin m),
    label (ntCode σ) = k.val → distance (ntCode σ) = d →
      Relation.EqvGen (ntMove n) σ (rep k) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro σ k hlabel hdist
    have hparts := ntClassOk_parts n m reps label distance
      (ntClassOk_code hcert σ)
    have hthird := hparts.2.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hthird
    rw [hlabel, hdist] at hthird
    obtain ⟨hdsmall, hbranch⟩ : d < 15 ∧
      (if d = 0 then ntCode σ == reps.getD k.val []
        else (ntNbrs (ntQuads n) (ntCode σ)).any fun t =>
          distance t + 1 == d) = true := by
      obtain hlarge | hsmall := hthird
      · omega
      · exact hsmall
    by_cases hd0 : d = 0
    · rw [ite_eq_left hd0] at hbranch
      have hroot : ntCode σ = reps.getD k.val [] := beq_iff_eq.mp hbranch
      have hσ : σ = rep k := ntCode_injective (hroot.trans (hcode k).symm)
      rw [hσ]
      exact Relation.EqvGen.refl _
    · rw [ite_eq_right hd0] at hbranch
      rw [List.any_eq_true] at hbranch
      obtain ⟨t, ht, htd⟩ := hbranch
      rw [beq_iff_eq] at htd
      obtain ⟨τ, hτcode, hmove⟩ := ntNbrs_sound ht
      have hτlabelRaw := (List.all_eq_true.mp hparts.2.1) t ht
      have hτlabel : label (ntCode τ) = k.val := by
        rw [hτcode]
        exact (beq_iff_eq.mp hτlabelRaw).trans hlabel
      have hτdist : distance (ntCode τ) < d := by
        rw [hτcode]
        omega
      have hτreach := ih (distance (ntCode τ)) hτdist τ k hτlabel rfl
      have hστ : Relation.EqvGen (ntMove n) σ τ := by
        obtain hmove | hmove := hmove
        · exact Relation.EqvGen.rel _ _ hmove
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)
      exact Relation.EqvGen.trans _ _ _ hστ hτreach

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDistance_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDistance_reaches {n m : ℕ} {reps : List (List ℕ)}
  {label distance : List ℕ → ℕ} (rep : Fin m → Equiv.Perm (Fin n))
  (hcode : ∀ k, ntCode (rep k) = reps.getD k.val [])
  (hcert : (List.permutations' (List.range n)).all
    (ntClassOk n m reps label distance) = true)
  (σ : Equiv.Perm (Fin n)) (k : Fin m)
  (hlabel : label (ntCode σ) = k.val) :
  Relation.EqvGen (ntMove n) σ (rep k) :=
  ntDistance_reaches_aux rep hcode hcert (distance (ntCode σ)) σ k hlabel rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntPat_move](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntPat_move {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : ntPat n σ) :
  ∃ y, ntMove n σ y ∨ ntMove n y σ := by
  obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩ | := h
    ⟨i1, i2, i3, i4, h12, h23, h34, s31, s42, s13⟩
  · exact ⟨_, Or.inl (ntMove_of_1234 h12 h23 h34 s12 s23 s34)⟩
  · exact ⟨_, Or.inr (ntMove_of_3412 h12 h23 h34 s31 s42 s13)⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_ins_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_ins_zero (v : Fin 8) (ρ : Equiv.Perm (Fin 7)) :
  ntCode (ntIns 0 v ρ) = ntInsertCodeZero v.val (ntCode ρ) := by
  unfold ntCode ntInsertCodeZero
  rw [List.ofFn_succ, ntIns_apply_same]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hi : i < 7 := by simpa using hi₂
    let I : Fin 7 := ⟨i, hi⟩
    simp only [List.getElem_map, List.getElem_ofFn]
    have hpos : (Fin.succ I : Fin 8) = (0 : Fin 8).succAbove I := by
      apply Fin.ext
      simp
    rw [hpos, ntIns_apply_succAbove, ntSuccAbove_val]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeleteCode_ins](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeleteCode_ins (y v : Fin 8) (ρ : Equiv.Perm (Fin 7)) :
  ntDeleteCode (ntCode (ntIns y v ρ)) y.val = ntCode ρ := by
  have hyval : (ntCode (ntIns y v ρ)).getD y.val 0 = v.val := by
    rw [ntCode_getD (ntIns y v ρ) y.val y.is_lt]
    have hy : (⟨y.val, y.is_lt⟩ : Fin 8) = y := Fin.ext rfl
    rw [hy, ntIns_apply_same]
  unfold ntDeleteCode
  rw [hyval]
  apply List.ext_getElem
  · simp [ntCode, List.length_eraseIdx, y.is_lt]
  · intro i hi₁ hi₂
    have hi : i < 7 := by simpa [ntCode] using hi₂
    let I : Fin 7 := ⟨i, hi⟩
    simp only [List.getElem_map]
    have hiErase : i < ((ntCode (ntIns y v ρ)).eraseIdx y.val).length := by
      simpa using hi₁
    have herase :
      ((ntCode (ntIns y v ρ)).eraseIdx y.val)[i]'hiErase =
        (ntIns y v ρ (y.succAbove I)).val := by
      rw [List.getElem_eraseIdx]
      by_cases hiy : i < y.val
      · simp only [hiy, dite_true, ntCode, List.getElem_ofFn]
        apply congrArg Fin.val
        apply congrArg (ntIns y v ρ)
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp [I, hiy]
      · simp only [hiy, dite_false, ntCode, List.getElem_ofFn]
        apply congrArg Fin.val
        apply congrArg (ntIns y v ρ)
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp [I, hiy]
    rw [herase, ntIns_apply_succAbove, ntSuccAbove_val]
    simp only [ntCode, List.getElem_ofFn]
    change (if v.val < (if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1)
      then (if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1) - 1
      else if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1) = (ρ I).val
    split_ifs <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCertificate7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCertificate7 :
  (List.permutations' (List.range 7)).all ntOk7 = true := by
  native_decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_even7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_even7 : ntCode (ntEven 7) = List.range 7 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntCode_odd5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntCode_odd5 : ntCode (ntOdd 5) = List.range 5 ++ [6, 5] := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDist7_reaches_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDist7_reaches_aux (d : ℕ) :
  ∀ σ : Equiv.Perm (Fin 7), ntDist7 (ntCode σ) = d → d < 15 →
    Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
      Relation.EqvGen (ntMove 7) σ (ntOdd 5) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro σ hdist hd
    have hok := (List.all_eq_true.mp ntCertificate7) (ntCode σ)
      (ntCode_mem_permutations' σ)
    dsimp only [ntOk7] at hok
    rw [Bool.and_eq_true] at hok
    have hbranch := hok.2
    change (ntDist7 (ntCode σ) ≥ 15 ||
      if ntDist7 (ntCode σ) = 0 then
        (ntCode σ == List.range 7 || ntCode σ == List.range 5 ++ [6, 5])
      else ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length &&
        match ntNbrAt (ntCode σ)
          ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16) (0, 0, 0, 0)) with
        | some t => ntDist7 t + 1 == ntDist7 (ntCode σ)
        | none => false) = true at hbranch
    rw [Bool.or_eq_true] at hbranch
    have hnext :
      (if ntDist7 (ntCode σ) = 0 then
        (ntCode σ == List.range 7 || ntCode σ == List.range 5 ++ [6, 5])
        else ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length &&
          match ntNbrAt (ntCode σ)
            ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16)
              (0, 0, 0, 0)) with
          | some t => ntDist7 t + 1 == ntDist7 (ntCode σ)
          | none => false) = true := by
      obtain hlarge | hnext := hbranch
      · have hlarge' : 15 ≤ ntDist7 (ntCode σ) := by
        simpa only [decide_eq_true_eq] using hlarge
        rw [hdist] at hlarge'
        omega
      · exact hnext
    by_cases hd0 : d = 0
    · rw [hdist, ite_eq_left hd0] at hnext
      simp only [Bool.or_eq_true, beq_iff_eq] at hnext
      obtain heven | hodd := hnext
      · have hσ : σ = ntEven 7 := ntCode_injective (heven.trans ntCode_even7.symm)
        rw [hσ]
        exact Or.inl (Relation.EqvGen.refl _)
      · have hσ : σ = ntOdd 5 := ntCode_injective (hodd.trans ntCode_odd5.symm)
        rw [hσ]
        exact Or.inr (Relation.EqvGen.refl _)
    · rw [hdist, ite_eq_right hd0] at hnext
      rw [Bool.and_eq_true] at hnext
      have hi : ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length := by
        simpa only [decide_eq_true_eq] using hnext.1
      have hstep :
        (match ntNbrAt (ntCode σ)
          ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16) (0, 0, 0, 0)) with
          | some t => ntDist7 t + 1 == d
          | none => false) = true := hnext.2
      rw [List.getD_eq_getElem _ _ hi] at hstep
      cases hopt : ntNbrAt (ntCode σ)
        (ntQuads 7)[ntCert7Entry (ntCode σ) / 16] with
      | none => simp [hopt] at hstep
      | some t =>
        have htd : ntDist7 t + 1 = d := by
          simpa only [hopt, beq_iff_eq] using hstep
        have hquad :
          (ntQuads 7)[ntCert7Entry (ntCode σ) / 16] ∈ ntQuads 7 :=
          List.getElem_mem _
        have ht : t ∈ ntNbrs (ntQuads 7) (ntCode σ) := by
          unfold ntNbrs
          rw [List.mem_filterMap]
          exact ⟨_, hquad, hopt⟩
        obtain ⟨τ, hτcode, hmove⟩ := ntNbrs_sound ht
        have hτd : ntDist7 (ntCode τ) < d := by
          rw [hτcode]
          omega
        have hτsmall : ntDist7 (ntCode τ) < 15 := by omega
        have hτreach := ih (ntDist7 (ntCode τ)) hτd τ rfl hτsmall
        have hστ : Relation.EqvGen (ntMove 7) σ τ := by
          obtain hmove | hmove := hmove
          · exact Relation.EqvGen.rel _ _ hmove
          · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)
        obtain heven | hodd := hτreach
        · exact Or.inl (Relation.EqvGen.trans _ _ _ hστ heven)
        · exact Or.inr (Relation.EqvGen.trans _ _ _ hστ hodd)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDist7_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDist7_reaches (σ : Equiv.Perm (Fin 7))
  (hσ : ntDist7 (ntCode σ) < 15) :
  Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
    Relation.EqvGen (ntMove 7) σ (ntOdd 5) :=
  ntDist7_reaches_aux (ntDist7 (ntCode σ)) σ rfl hσ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate0 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 0) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate1 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 1) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate2 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 2) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate3 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 3) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate4 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 4) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate5 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 5) = true := by
  native_decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate6 :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk 6) = true := by
  native_decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntDeletionCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntDeletionCertificate (v : Fin 7) :
  (List.permutations' (List.range 7)).all (ntDeletionSliceOk v.val) = true := by
  fin_cases v <;>
    first
    | simpa using ntDeletionCertificate0
    | simpa using ntDeletionCertificate1
    | simpa using ntDeletionCertificate2
    | simpa using ntDeletionCertificate3
    | simpa using ntDeletionCertificate4
    | simpa using ntDeletionCertificate5
    | simpa using ntDeletionCertificate6

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntNoTrunc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntNoTrunc (n : ℕ) (hn : 5 ≤ n) : 55 * n ≤ n ^ 3 + 6 * n ^ 2 := by
  have h2 : 25 ≤ n ^ 2 := by
    have h := Nat.mul_le_mul hn hn
    simpa [pow_two] using h
  have h6 : 30 ≤ 6 * n := by omega
  have h55 : 55 ≤ n ^ 2 + 6 * n := by omega
  have hmul := Nat.mul_le_mul (le_refl n) h55
  rwa [mul_comm 55 n, show n ^ 3 + 6 * n ^ 2 = n * (n ^ 2 + 6 * n) from by ring]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntNum_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntNum_cast (k : ℕ) (hk : 5 ≤ k) :
  (((k ^ 3 + 6 * k ^ 2 - 55 * k + 54 : ℕ)) : ℤ) =
    (k : ℤ) ^ 3 + 6 * (k : ℤ) ^ 2 - 55 * (k : ℤ) + 54 := by
  have hle := ntNoTrunc k hk
  rw [Nat.cast_add, Nat.cast_sub hle]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ntPoly_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma ntPoly_step (n : ℕ) :
  2 * ((((n + 6 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 6 : ℕ)) : ℤ) ^ 2 -
    55 * (((n + 6 : ℕ)) : ℤ) + 54) -
    ((((n + 5 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 5 : ℕ)) : ℤ) ^ 2 -
      55 * (((n + 5 : ℕ)) : ℤ) + 54) +
    6 * ((((n : ℕ)) : ℤ) + 8) =
    ((((n + 7 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 7 : ℕ)) : ℤ) ^ 2 -
      55 * (((n + 7 : ℕ)) : ℤ) + 54) := by
  push_cast
  ring

end MetaMathlibExt

/--
[card_nontrivial_1234_3412_classes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma card_nontrivial_1234_3412_classes_eq :
-- imply
  ∀ (n : ℕ), 7 ≤ n →
    let OneMove : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
      fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
        i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
          σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
          τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
          ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j;
    Nat.card (Subtype fun C : Set (Equiv.Perm (Fin n)) =>
        ∃ σ, C = { τ | Relation.EqvGen OneMove σ τ } ∧ 1 < Nat.card ↥C) =
      (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 := by
-- proof
  apply MetaMathlibExt.card_nontrivial_1234_3412_classes


-- created on 2026-10-20
-- updated on 2026-10-23
