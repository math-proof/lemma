import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped nonZeroDivisors


private lemma exists_mul_isIdempotentElem_ne_zero
  {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A] (a : A) (ha : a ≠ 0) :
  ∃ b : A, IsIdempotentElem (b * a) ∧ b * a ≠ 0 := by
  classical
  let e := IsArtinianRing.equivPi A
  have hone : ∀ i : MaximalSpectrum A, (1 : A ⧸ i.asIdeal) ≠ 0 := by
    intro i h
    have := (Ideal.Quotient.eq_zero_iff_mem).1 h
    exact i.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hex : ∃ i, e a i ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    apply e.injective
    rw [map_zero]
    ext i
    rw [h i, Pi.zero_apply]
  obtain ⟨i, hi⟩ := hex
  obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hi
  refine ⟨e.symm (Pi.single i c), ?_, ?_⟩
  ·
    have hba : e (e.symm (Pi.single i c) * a) = Pi.single i 1 := by
      rw [map_mul, e.apply_symm_apply]
      ext k
      rw [Pi.mul_apply]
      if hk : k = i then
        subst hk
        rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm, hc]
      else
        rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, zero_mul]
    show e.symm (Pi.single i c) * a * (e.symm (Pi.single i c) * a) = e.symm (Pi.single i c) * a
    apply e.injective
    rw [map_mul, hba]
    ext k
    rw [Pi.mul_apply]
    if hk : k = i then
      subst hk
      rw [Pi.single_eq_same, mul_one]
    else
      rw [Pi.single_eq_of_ne hk, mul_zero]
  ·
    intro h0
    have h1 : e (e.symm (Pi.single i c) * a) = 0 := by rw [h0, map_zero]
    rw [map_mul, e.apply_symm_apply] at h1
    have h2 := congrFun h1 i
    rw [Pi.mul_apply, Pi.single_eq_same, Pi.zero_apply, mul_comm, hc] at h2
    exact hone i h2

private lemma trace_ne_zero_of_isIdempotentElem
  {K : Type*} [Field K] [CharZero K] {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
  (ε : A) (hε : IsIdempotentElem ε) (hε0 : ε ≠ 0) : Algebra.trace K A ε ≠ 0 := by
  rw [Algebra.trace_apply]
  set f : A →ₗ[K] A := Algebra.lmul K A ε with hf
  have hfx : ∀ x, f x = ε * x := fun x => rfl
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    { map_mem := fun x => LinearMap.mem_range_self f x
      map_id := by
        rintro x ⟨y, rfl⟩
        rw [hfx, hfx, ← mul_assoc, hε.eq] }
  rw [hproj.trace]
  have hpos : 0 < Module.finrank K ↥(LinearMap.range f) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨ε, ⟨1, by rw [hfx, mul_one]⟩⟩, ?_⟩
    intro h
    exact hε0 (congrArg Subtype.val h)
  exact_mod_cast hpos.ne'

private lemma exists_trace_mul_ne_zero_field
  {K : Type*} [Field K] [CharZero K] {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
  [IsReduced A] (a : A) (ha : a ≠ 0) : ∃ t : A, Algebra.trace K A (a * t) ≠ 0 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨b, hid, hne⟩ := exists_mul_isIdempotentElem_ne_zero a ha
  refine ⟨b, ?_⟩
  rw [mul_comm]
  exact trace_ne_zero_of_isIdempotentElem (b * a) hid hne
/--
[FixedPart_exists_trace_mul_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FixedPart_exists_trace_mul_ne_zero.lean)
-/
@[path]
private lemma main
  [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R] [IsReduced R]
  {r : R}
-- given
  (hr : r ≠ 0) :
-- imply
  ∃ s : R, Algebra.trace ℤ R (r * s) ≠ 0 := by
-- proof
  classical
  let S : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)
  have hSint : ∀ x : R, x ∈ S → ∃ n : ℤ, n ≠ 0 ∧ x = n := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := (Submonoid.mem_map).1 hx
    exact ⟨n, nonZeroDivisors.ne_zero hn, by rw [← hnx, eq_intCast]⟩
  have hS : S ≤ nonZeroDivisors R := by
    intro x hx
    obtain ⟨n, hn0, hxn⟩ := hSint x hx
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hy' : n • y = 0 := by
      rwa [zsmul_eq_mul, ← hxn, mul_comm]
    refine (smul_eq_zero_iff_right hn0).1 hy'
  let A := Localization S
  let K := FractionRing ℤ
  have : IsReduced A := isReduced_localizationPreserves S A inferInstance
  have : Module.Finite K A := Module.Finite.of_isLocalization ℤ R (nonZeroDivisors ℤ)
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hS
  have ha : algebraMap R A r ≠ 0 := fun h => hr (hinj (h.trans (map_zero _).symm))
  obtain ⟨t, ht⟩ := exists_trace_mul_ne_zero_field (K := K) (algebraMap R A r) ha
  obtain ⟨⟨s, u⟩, hsu⟩ := IsLocalization.mk'_surjective S t
  obtain ⟨n, hn0, hun⟩ := hSint u.1 u.2
  refine ⟨s, ?_⟩
  intro hzero
  have h1 : Algebra.trace K A (algebraMap R A (r * s)) = 0 := by
    rw [Algebra.trace_localization ℤ (nonZeroDivisors ℤ) (r * s), hzero, map_zero]
  have h2 : algebraMap R A (r * s) = (algebraMap R A r * t) * algebraMap R A (u : R) := by
    rw [map_mul, mul_assoc, ← hsu]
    congr 1
    exact (IsLocalization.mk'_spec A s u).symm
  have h3 : algebraMap R A (u : R) = algebraMap K A (n : K) := by
    rw [hun, map_intCast, map_intCast]
  rw [h2, h3, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_zero] at h1
  obtain h1 | h1 := h1
  · exact hn0 (by exact_mod_cast h1)
  · exact ht h1


-- created on 2026-10-24
