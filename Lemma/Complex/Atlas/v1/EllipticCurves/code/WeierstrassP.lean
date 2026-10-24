import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.WeierstrassP
open Complex PeriodPair ComplexLattice


namespace ComplexLattice

/--
[weierstrassPFun_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_differentiableOn
  {L : ComplexLattice} :
-- imply
  DifferentiableOn ℂ L.weierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
-- proof
  L.differentiableOn_weierstrassP

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_differentiableAt
  {L : ComplexLattice}
  {z₀ : ℂ}
-- given
  (hz₀ : z₀ ∉ (L.lattice : Set ℂ)) :
-- imply
  DifferentiableAt ℂ L.weierstrassPFun z₀ :=
-- proof
  (L.weierstrassPFun_differentiableOn z₀ hz₀).differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz₀)

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_analyticOnNhd
  {L : ComplexLattice} :
-- imply
  AnalyticOnNhd ℂ L.weierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
-- proof
  L.analyticOnNhd_weierstrassP

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_meromorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_meromorphic
  {L : ComplexLattice} :
-- imply
  Meromorphic L.weierstrassPFun :=
-- proof
  L.meromorphic_weierstrassP

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_order
  {L : ComplexLattice}
  {l₀ : ℂ}
-- given
  (h : l₀ ∈ L.lattice) :
-- imply
  meromorphicOrderAt L.weierstrassPFun l₀ = -2 :=
-- proof
  L.order_weierstrassP l₀ h

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_even
  {L : ComplexLattice}
  {z : ℂ} :
-- imply
  L.weierstrassPFun (-z) = L.weierstrassPFun z :=
-- proof
  L.weierstrassP_neg z

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_laurentExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_laurentExpansion
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖) :
-- imply
  HasSum (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.eisensteinSeries (2 * n + 4) * z ^ (2 * n + 2)) (L.weierstrassPFun z - 1 / z ^ 2) := by
-- proof
  show HasSum (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.G (2 * n + 4) * z ^ (2 * n + 2))
    (L.weierstrassP z - 1 / z ^ 2)
  have hsum : HasSum (fun i ↦ (L.weierstrassPExceptSeries 0 0).coeff i * z ^ i)
    (L.weierstrassPExcept 0 z) := by
    have h := L.weierstrassPExceptSeries_hasSum 0 z 0 (fun l hl => by simpa using hz l hl)
    simpa using h
  have heq : L.weierstrassP z - 1 / z ^ 2 = L.weierstrassPExcept 0 z := by
    have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
    have h := L.weierstrassPExcept_add ⟨0, h0⟩ z
    simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      one_div, inv_zero, sub_zero] at h
    rw [one_div]; linear_combination -h
  rw [heq]
  rw [show (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.G (2 * n + 4) * z ^ (2 * n + 2)) =
    (fun i ↦ (L.weierstrassPExceptSeries 0 0).coeff i * z ^ i) ∘ (fun n ↦ 2 * n + 2) from by
    ext n
    congr 1
    simp only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
      show (2 * n + 2 : ℕ) ≠ 0 from by omega, ↓reduceIte,
      L.lattice.zero_mem, sub_zero, zero_pow (by omega : (2 * n + 2) + 2 ≠ 0),
      inv_zero, sub_zero]
    rw [congrFun L.sumInvPow_zero]
    push_cast; ring]
  rw [Function.Injective.hasSum_iff (fun a b h => by omega)]
  · exact hsum
  · intro x hx
    simp only [Set.mem_range, not_exists] at hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars]
    · have hodd : Odd x := by
      by_contra h
      have heven := Nat.not_odd_iff_even.mp h
      obtain ⟨m, hm⟩ := heven
      exact absurd (show 2 * (m - 1) + 2 = x by omega) (hx (m - 1))
      have hodd2 : Odd (x + 2) := hodd.add_even even_two
      simp only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars, hx0,
        ↓reduceIte, L.lattice.zero_mem, sub_zero, zero_pow (by omega : x + 2 ≠ 0),
        inv_zero, sub_zero]
      rw [congrFun L.sumInvPow_zero, L.G_eq_zero_of_odd _ hodd2, mul_zero, zero_mul]

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_meromorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma derivWeierstrassPFun_meromorphic
  {L : ComplexLattice} :
-- imply
  Meromorphic L.derivWeierstrassPFun :=
-- proof
  L.meromorphic_derivWeierstrassP

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma derivWeierstrassPFun_odd
  {L : ComplexLattice}
  {z : ℂ} :
-- imply
  L.derivWeierstrassPFun (-z) = - L.derivWeierstrassPFun z :=
-- proof
  L.derivWeierstrassP_neg z

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma derivWeierstrassPFun_analyticOnNhd
  {L : ComplexLattice} :
-- imply
  AnalyticOnNhd ℂ L.derivWeierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
-- proof
  L.analyticOnNhd_derivWeierstrassP

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma derivWeierstrassPFun_order
  {L : ComplexLattice}
  {l₀ : ℂ}
-- given
  (h : l₀ ∈ L.lattice) :
-- imply
  meromorphicOrderAt L.derivWeierstrassPFun l₀ = -3 := by
-- proof
  show meromorphicOrderAt L.derivWeierstrassP l₀ = -3
  rw [show (-3 : WithTop ℤ) = ((-3 : ℤ) : WithTop ℤ) from rfl]
  rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_derivWeierstrassP l₀)]
  refine ⟨fun z ↦ (z - l₀) ^ 3 * L.derivWeierstrassPExcept l₀ z - 2, ?_, ?_, ?_⟩
  · have : AnalyticAt ℂ (L.derivWeierstrassPExcept l₀) l₀ := by
    apply L.analyticOnNhd_derivWeierstrassPExcept l₀
    simp [Set.mem_compl_iff, Set.mem_diff, h]
    fun_prop
  · simp [sub_self]
  · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ l₀)
    have hne3 : (z - l₀) ^ 3 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hsub := L.derivWeierstrassPExcept_sub ⟨l₀, h⟩ z
    rw [← hsub]
    simp only [smul_eq_mul, zpow_neg, zpow_ofNat]
    rw [mul_sub, inv_mul_cancel_left₀ hne3]
    ring

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_add_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_add_lattice
  {L : ComplexLattice}
  {z : ℂ}
  {ω : ℂ}
-- given
  (hω : ω ∈ L.lattice) :
-- imply
  L.weierstrassPFun (z + ω) = L.weierstrassPFun z :=
-- proof
  L.weierstrassP_add_coe z ⟨ω, hω⟩

end ComplexLattice

namespace ComplexLattice

/--
[derivWeierstrassPFun_add_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma derivWeierstrassPFun_add_lattice
  {L : ComplexLattice}
  {z : ℂ}
  {ω : ℂ}
-- given
  (hω : ω ∈ L.lattice) :
-- imply
  L.derivWeierstrassPFun (z + ω) = L.derivWeierstrassPFun z :=
-- proof
  L.derivWeierstrassP_add_coe z ⟨ω, hω⟩

end ComplexLattice

namespace ComplexLattice

variable (L : ComplexLattice)
/--
[g₂Fun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma g₂Fun_eq : L.g₂Fun = L.g₂ :=
  rfl

end ComplexLattice

namespace ComplexLattice

variable (L : ComplexLattice)
/--
[g₃Fun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma g₃Fun_eq : L.g₃Fun = L.g₃ :=
  rfl

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassPFun_differentialEquation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
lemma weierstrassPFun_differentialEquation
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz : z ∉ (L.lattice : Set ℂ)) :
-- imply
  L.derivWeierstrassPFun z ^ 2 = 4 * L.weierstrassPFun z ^ 3 - L.g₂Fun * L.weierstrassPFun z - L.g₃Fun :=
-- proof
  L.derivWeierstrassP_sq z hz
end ComplexLattice


/--
[g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
private lemma g_eq
  {L : ComplexLattice} :
-- imply
  L.g₂Fun = L.g₂ := by
-- proof
  apply ComplexLattice.g L

/--
[g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean)
-/
@[path]
private lemma g_eq_2
  {L : ComplexLattice} :
-- imply
  L.g₃Fun = L.g₃ := by
-- proof
  apply ComplexLattice.g L


-- created on 2026-10-23
