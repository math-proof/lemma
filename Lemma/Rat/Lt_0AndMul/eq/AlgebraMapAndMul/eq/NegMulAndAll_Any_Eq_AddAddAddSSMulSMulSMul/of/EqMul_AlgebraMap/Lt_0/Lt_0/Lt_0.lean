import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Quaternion
open QuaternionAlgebra


private lemma linearIndependent_of_relations
  {c d : ℚ}
  (y z w : ℍ[ℚ,c,d]) (t c' : ℚ) (ht : t ≠ 0) (hc' : c' ≠ 0)
  (hyre : y.re = 0) (hzre : z.re = 0) (hwre : w.re = 0)
  (hyy : y * y = t • (1 : ℍ[ℚ,c,d])) (hzz : z * z = c' • (1 : ℍ[ℚ,c,d]))
  (hyz : y * z = w) (hyw : y * w = t • z) (hwz : w * z = c' • y) (hww : w * w = (-(t * c')) • (1 : ℍ[ℚ,c,d])) :
  LinearIndependent ℚ ![(1 : ℍ[ℚ,c,d]), y, z, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hS : g 0 • (1 : ℍ[ℚ,c,d]) + g 1 • y + g 2 • z + g 3 • w = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have e0 : g 0 = 0 := by
    have := congrArg QuaternionAlgebra.re hS
    simpa [hyre, hzre, hwre] using this
  have e1 : g 1 = 0 := by
    have h1 : y * (g 0 • (1 : ℍ[ℚ,c,d]) + g 1 • y + g 2 • z + g 3 • w) = 0 := by rw [hS, mul_zero]
    simp only [mul_add, mul_smul_comm, mul_one, hyy, hyz, hyw] at h1
    have := congrArg QuaternionAlgebra.re h1
    simp [hyre, hzre, hwre] at this
    obtain h | h := this
    · exact h
    · exact absurd h ht
  have e2 : g 2 = 0 := by
    have h2 : (g 0 • (1 : ℍ[ℚ,c,d]) + g 1 • y + g 2 • z + g 3 • w) * z = 0 := by rw [hS, zero_mul]
    simp only [add_mul, smul_mul_assoc, one_mul, hzz, hyz, hwz] at h2
    have := congrArg QuaternionAlgebra.re h2
    simp [hyre, hzre, hwre] at this
    obtain h | h := this
    · exact h
    · exact absurd h hc'
  have e3 : g 3 = 0 := by
    rw [e0, e1, e2, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add] at hS
    obtain h | h := smul_eq_zero.1 hS
    · exact h
    ·
      exfalso
      have := congrArg QuaternionAlgebra.re hww
      rw [h, mul_zero] at this
      simp at this
      obtain h' | h' := this
      · exact ht h'
      · exact hc' h'
  intro i
  fin_cases i <;> assumption

private lemma span_of_linearIndependent
  {c d : ℚ}
  (y z w : ℍ[ℚ,c,d]) (hli : LinearIndependent ℚ ![(1 : ℍ[ℚ,c,d]), y, z, w]) :
  ∀ u : ℍ[ℚ,c,d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • w := by
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [QuaternionAlgebra.finrank_eq_four])
  intro u
  have hu : u ∈ Submodule.span ℚ Set.range ![(1 : ℍ[ℚ,c,d]), y, z, w] := by rw [hspan]; trivial
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hu
  refine ⟨f 0, f 1, f 2, f 3, ?_⟩
  rw [← hf]
  simp [Fin.sum_univ_four]

private lemma helper_main
  {c d : ℚ}
  (hc : c < 0) (hd : d < 0) (y : ℍ[ℚ,c,d]) (t : ℚ) (ht : t < 0)
  (hy : y * y = algebraMap ℚ ℍ[ℚ,c,d] t) :
  ∃ (z : ℍ[ℚ,c,d]) (c' : ℚ), c' < 0 ∧ z * z = algebraMap ℚ ℍ[ℚ,c,d] c' ∧ y * z = -(z * y) ∧
    ∀ u : ℍ[ℚ,c,d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • (y * z) := by
  obtain ⟨y₁, y₂, y₃, y₄⟩ := y
  have hre := congrArg QuaternionAlgebra.re hy
  have hI := congrArg QuaternionAlgebra.imI hy
  have hJ := congrArg QuaternionAlgebra.imJ hy
  have hK := congrArg QuaternionAlgebra.imK hy
  simp [algebraMap_eq] at hre hI hJ hK
  have hy₁ : y₁ = 0 := by
    by_contra h
    have h2 : y₂ = 0 := by
      obtain h' | h' := mul_eq_zero.1 (by linarith [hI] : y₁ * y₂ = 0) <;> [exact absurd h' h; exact h']
    have h3 : y₃ = 0 := by
      obtain h' | h' := mul_eq_zero.1 (by linarith [hJ] : y₁ * y₃ = 0) <;> [exact absurd h' h; exact h']
    have h4 : y₄ = 0 := by
      obtain h' | h' := mul_eq_zero.1 (by linarith [hK] : y₁ * y₄ = 0) <;> [exact absurd h' h; exact h']
    subst h2 h3 h4
    nlinarith [hre, sq_nonneg y₁]
  subst hy₁
  simp at hre
  if hJK : y₃ = 0 ∧ y₄ = 0 then
    obtain ⟨rfl, rfl⟩ := hJK
    have hy₂ : y₂ ≠ 0 := by rintro rfl; simp at hre; linarith
    refine ⟨⟨0, 0, 1, 0⟩, d, hd, ?_, ?_, ?_⟩
    · ext <;> simp [algebraMap_eq]
    · ext <;> simp <;> ring
    ·
      refine span_of_linearIndependent _ _ _ (linearIndependent_of_relations _ _ _ t d ht.ne hd.ne
      rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_)
      · simp
      · ext <;> simp <;> (subst t; ring)
      · ext <;> simp
      · ext <;> simp <;> (subst t; ring)
      · ext <;> simp <;> ring
      · ext <;> simp <;> (subst t; ring)
  else
    have hpos : 0 < y₃ * y₃ - c * y₄ * y₄ := by
      obtain h | h := not_and_or.1 hJK
      ·
        have : 0 < y₃ * y₃ := mul_self_pos.2 h
        nlinarith [mul_self_nonneg y₄]
      ·
        have : 0 < y₄ * y₄ := mul_self_pos.2 h
        nlinarith [mul_self_nonneg y₃]
    refine ⟨⟨0, 0, c * y₄, y₃⟩, c * d * (c * y₄ * y₄ - y₃ * y₃), ?_, ?_, ?_, ?_⟩
    ·
      have hcd : 0 < c * d := mul_pos_of_neg_of_neg hc hd
      nlinarith
    · ext <;> simp [algebraMap_eq] <;> ring
    · ext <;> simp <;> ring
    ·
      refine span_of_linearIndependent _ _ _ (linearIndependent_of_relations _ _ _ t
      (c * d * (c * y₄ * y₄ - y₃ * y₃)) ht.ne ?_ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_)
      ·
        have hcd : 0 < c * d := mul_pos_of_neg_of_neg hc hd
        nlinarith
      ·
        simp; ring
      · ext <;> simp <;> (subst t; ring)
      · ext <;> simp <;> ring
      · ext <;> simp <;> (subst t; ring)
      · ext <;> simp <;> ring
      · ext <;> simp <;> (subst t; ring)
/--
[QuaternionAlgebra_exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuaternionAlgebra_exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg.lean)
-/
@[path]
private lemma main
  {c d : ℚ}
  {y : ℍ[ℚ, c, d]}
  {t : ℚ}
-- given
  (hc : c < 0)
  (hd : d < 0)
  (ht : t < 0)
  (hy : y * y = algebraMap ℚ ℍ[ℚ, c, d] t) :
-- imply
  ∃ (z : ℍ[ℚ, c, d]) (c' : ℚ), c' < 0 ∧ z * z = algebraMap ℚ ℍ[ℚ, c, d] c' ∧ y * z = -(z * y) ∧
      ∀ u : ℍ[ℚ, c, d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • (y * z) :=
-- proof
  helper_main hc hd y t ht hy


-- created on 2026-10-23
