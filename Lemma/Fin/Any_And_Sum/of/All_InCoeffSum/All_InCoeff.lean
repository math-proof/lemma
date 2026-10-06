import Mathlib
import sympy.Basic


/--
[PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.lean)
-/
@[main]
private lemma main
  [Field L]
  {K₀ : Subfield L}
  {n : ℕ}
  {g : Fin n → PowerSeries L}
  {c : Fin n → L}
-- given
  (hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀)
  (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
-- imply
  ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by
-- proof
  classical

  let ι : K₀ →ₗ[K₀] L := (Algebra.linearMap K₀ L)
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by simpa [ι] using h)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hι)
  have hπι : ∀ z : K₀, π (z : L) = z := fun z => by
    have := congrArg (fun f => f z) hπ
    simp [ι] at this
    exact this
  refine ⟨fun i => (π (c i) : L), fun i => (π (c i)).2, ?_⟩
  ext m
  simp only [map_sum, map_smul, smul_eq_mul]

  have hm := h m
  simp only [map_sum, map_smul, smul_eq_mul] at hm

  have key : (π (∑ i, c i * (g i).coeff m) : L) = ∑ i, (π (c i) : L) * (g i).coeff m := by
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * (g i).coeff m = ((⟨(g i).coeff m, hg i m⟩ : K₀) : K₀) • c i := by
      rw [Subfield.smul_def]; exact mul_comm _ _
    rw [this, map_smul]

    rw [show (((⟨(g i).coeff m, hg i m⟩ : K₀) • π (c i) : K₀) : L) = ((g i).coeff m) * (π (c i) : L) from rfl]
    exact mul_comm _ _
  rw [← key, hπι ⟨_, hm⟩]


-- created on 2026-10-05
