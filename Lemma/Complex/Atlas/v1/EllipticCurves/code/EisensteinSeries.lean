import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.EisensteinSeries
open Complex ComplexLattice
open scoped UpperHalfPlane
open ComplexLattice Pointwise


namespace ComplexLattice

/--
[eisensteinSeries_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma eisensteinSeries_def
  {L : ComplexLattice}
  {k : ℕ} :
-- imply
  L.eisensteinSeries k = ∑' l : L.lattice, ((↑l : ℂ) ^ k)⁻¹ :=
-- proof
  rfl

end ComplexLattice

namespace ComplexLattice

/--
[hasSum_eisensteinSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma hasSum_eisensteinSeries
  {L : ComplexLattice}
  {k : ℕ}
-- given
  (hk : 2 < k) :
-- imply
  HasSum (fun l : L.lattice ↦ ((↑l : ℂ) ^ k)⁻¹) (L.eisensteinSeries k) := by
-- proof
  have h := L.hasSum_sumInvPow 0 hk
  simp only [sub_zero] at h
  rwa [congrFun L.sumInvPow_zero k] at h

end ComplexLattice

namespace ComplexLattice

/--
[summable_eisensteinSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma summable_eisensteinSeries
  {L : ComplexLattice}
  {k : ℕ}
-- given
  (hk : 2 < k) :
-- imply
  Summable (fun l : L.lattice ↦ ((↑l : ℂ) ^ k)⁻¹) :=
-- proof
  (L.hasSum_eisensteinSeries hk).summable

end ComplexLattice

namespace ComplexLattice

/--
[summable_norm_eisensteinSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma summable_norm_eisensteinSeries
  {L : ComplexLattice}
  {k : ℕ}
-- given
  (hk : 2 < k) :
-- imply
  Summable (fun l : L.lattice ↦ ‖((↑l : ℂ) ^ k)⁻¹‖) :=
-- proof
  (L.summable_eisensteinSeries hk).norm

end ComplexLattice

/--
[lattice_ofUpperHalfPlane_eq_addOne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma lattice_ofUpperHalfPlane_eq_addOne
  {τ : ℍ} :
-- imply
  (ofUpperHalfPlane τ).lattice = (ofUpperHalfPlane τ.addOne).lattice := by
-- proof
  ext x
  simp only [mem_lattice_iff, UpperHalfPlane.addOne]
  simp only [ofUpperHalfPlane, mk']
  constructor
  · rintro ⟨n₁, n₂, rfl⟩
    exact ⟨n₁ - n₂, n₂, by push_cast; ring⟩
  · rintro ⟨n₁, n₂, rfl⟩
    exact ⟨n₁ + n₂, n₂, by push_cast; ring⟩

/--
[isHomothetic_ofUpperHalfPlane_negInv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma isHomothetic_ofUpperHalfPlane_negInv
  {τ : ℍ} :
-- imply
  IsHomothetic (ofUpperHalfPlane τ) (ofUpperHalfPlane τ.negInv) := by
-- proof
  have hτne : (τ : ℂ) ≠ 0 := by
    intro h; have := τ.2; rw [h] at this; simp at this
  refine ⟨(τ : ℂ)⁻¹, inv_ne_zero hτne, ?_⟩
  ext x
  simp only [Set.mem_smul_set]
  constructor
  · intro hx
    rw [SetLike.mem_coe, mem_lattice_iff] at hx
    obtain ⟨n₁, n₂, rfl⟩ := hx
    refine ⟨(-n₂ : ℂ) * 1 + (n₁ : ℂ) * (τ : ℂ), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_lattice_iff]
      exact ⟨-n₂, n₁, by simp [ofUpperHalfPlane, mk']⟩
    · simp only [smul_eq_mul, ofUpperHalfPlane, mk', UpperHalfPlane.negInv]
      field_simp
      ring
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_lattice_iff] at hy
    obtain ⟨n₁, n₂, rfl⟩ := hy
    rw [SetLike.mem_coe, mem_lattice_iff]
    refine ⟨n₂, -n₁, ?_⟩
    simp only [smul_eq_mul, Int.cast_neg, ofUpperHalfPlane, mk', UpperHalfPlane.negInv]
    field_simp
    ring

/--
[ComplexLattice.jInvariantLattice_eq_of_lattice_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma ComplexLattice.jInvariantLattice_eq_of_lattice_eq
  {L L' : ComplexLattice}
-- given
  (h : L.lattice = L'.lattice) :
-- imply
  L.jInvariantLattice = L'.jInvariantLattice := by
-- proof
  have hG : ∀ k, L.G k = L'.G k := by
    intro k
    show ∑' l : L.lattice, ((l : ℂ) ^ k)⁻¹ = ∑' l : L'.lattice, ((l : ℂ) ^ k)⁻¹
    rw [h]
  have hg₂ : L.g₂ = L'.g₂ := by rw [g₂_eq, g₂_eq]; exact congrArg (60 * ·) (hG 4)
  have hg₃ : L.g₃ = L'.g₃ := by rw [g₃_eq, g₃_eq]; exact congrArg (140 * ·) (hG 6)
  have hΔ : L.discriminantLattice = L'.discriminantLattice := by
    simp only [discriminantLattice_def, hg₂, hg₃]
  unfold jInvariantLattice
  rw [hg₂, hΔ]

/--
[ComplexLattice.jInvariantLattice_eq_of_isHomothetic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma ComplexLattice.jInvariantLattice_eq_of_isHomothetic
  {L L' : ComplexLattice}
-- given
  (h : IsHomothetic L L') :
-- imply
  L'.jInvariantLattice = L.jInvariantLattice := by
-- proof
  obtain ⟨c, hc, hlat⟩ := h
  have hfwd : ∀ (l' : L'.lattice), c⁻¹ * (l' : ℂ) ∈ L.lattice := by
    intro l'
    have hl' : (l' : ℂ) ∈ (L'.lattice : Set ℂ) := l'.2
    rw [hlat] at hl'
    obtain ⟨w, hw, hwval⟩ := hl'
    have : (l' : ℂ) = c * w := by rw [← hwval]; simp [smul_eq_mul]
    rwa [this, show c⁻¹ * (c * w) = w from by field_simp]
  have hbwd : ∀ (l : L.lattice), c * (l : ℂ) ∈ L'.lattice := by
    intro l
    have hl : (l : ℂ) ∈ (L.lattice : Set ℂ) := l.2
    have : c * (l : ℂ) ∈ (L'.lattice : Set ℂ) := by
      rw [hlat]; exact ⟨(l : ℂ), hl, by simp [smul_eq_mul]⟩
    exact this
  let hequiv : L'.lattice ≃ L.lattice :=
    ⟨fun l' => ⟨c⁻¹ * (l' : ℂ), hfwd l'⟩,
    fun l => ⟨c * (l : ℂ), hbwd l⟩,
    fun l' => Subtype.ext (by field_simp),
    fun l => Subtype.ext (by field_simp)⟩
  have hG : ∀ k, L'.eisensteinSeries k = c⁻¹ ^ k * L.eisensteinSeries k := by
    intro k
    simp only [eisensteinSeries_def]
    rw [← Equiv.tsum_eq hequiv, ← tsum_mul_left]
    congr 1; ext l'
    simp only [hequiv, Equiv.coe_fn_mk]
    rw [mul_pow, mul_inv, inv_pow, inv_inv, inv_mul_cancel_left₀ (pow_ne_zero k hc)]
  have hg₂ : L'.g₂ = c⁻¹ ^ 4 * L.g₂ := by
    rw [g₂_eq, g₂_eq, hG 4]; ring
  have hg₃ : L'.g₃ = c⁻¹ ^ 6 * L.g₃ := by
    rw [g₃_eq, g₃_eq, hG 6]; ring
  simp only [jInvariantLattice_def, hg₂, hg₃]
  have hc_ne : c⁻¹ ^ 12 ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  have hnum : 1728 * (c⁻¹ ^ 4 * L.g₂) ^ 3 = c⁻¹ ^ 12 * (1728 * L.g₂ ^ 3) := by ring
  have hden : (c⁻¹ ^ 4 * L.g₂) ^ 3 - 27 * (c⁻¹ ^ 6 * L.g₃) ^ 2 =
    c⁻¹ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hc_ne]

/--
[jFunction_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma jFunction_add_one
  {τ : ℍ} :
-- imply
  jFunction τ.addOne = jFunction τ := by
-- proof
  unfold jFunction
  exact (ComplexLattice.jInvariantLattice_eq_of_lattice_eq
    (lattice_ofUpperHalfPlane_eq_addOne τ)).symm

/--
[jFunction_neg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma jFunction_neg_inv
  {τ : ℍ} :
-- imply
  jFunction τ.negInv = jFunction τ := by
-- proof
  unfold jFunction
  exact ComplexLattice.jInvariantLattice_eq_of_isHomothetic
    (isHomothetic_ofUpperHalfPlane_negInv τ)

/--
[jFunction_ext_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma jFunction_ext_eq
  {z : ℂ}
-- given
  (hz : 0 < z.im) :
-- imply
  (if h : 0 < z.im then jFunction ⟨z, h⟩ else 0) = 1728 * g₂Ext z ^ 3 / (g₂Ext z ^ 3 - 27 * g₃Ext z ^ 2) := by
-- proof
  simp only [hz, dite_true, g₂Ext, g₃Ext, jFunction, ComplexLattice.jInvariantLattice,
    ComplexLattice.discriminantLattice, g₂Function, g₃Function]

/--
[discriminant_ext_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma discriminant_ext_ne_zero
  {z : ℂ}
-- given
  (hz : 0 < z.im) :
-- imply
  g₂Ext z ^ 3 - 27 * g₃Ext z ^ 2 ≠ 0 := by
-- proof
  simp only [g₂Ext, g₃Ext, hz, dite_true, g₂Function, g₃Function]
  exact (ComplexLattice.ofUpperHalfPlane ⟨z, hz⟩).discriminantLattice_ne_zero'

/--
[jFunction_holomorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EisensteinSeries.lean)
-/
@[path]
lemma jFunction_holomorphic
-- imply
  DifferentiableOn ℂ (fun z : ℂ => if h : 0 < z.im then jFunction ⟨z, h⟩ else 0) {z : ℂ | 0 < z.im} := by
-- proof
  have hg₂ := g₂Ext_differentiableOn
  have hg₃ := g₃Ext_differentiableOn
  have hj : DifferentiableOn ℂ
    (fun z => 1728 * g₂Ext z ^ 3 / (g₂Ext z ^ 3 - 27 * g₃Ext z ^ 2))
    {z : ℂ | 0 < z.im} := by
    apply DifferentiableOn.div
    · exact (differentiableOn_const 1728).mul (hg₂.pow 3)
    · exact (hg₂.pow 3).sub ((differentiableOn_const 27).mul (hg₃.pow 2))
    · intro z hz
      exact discriminant_ext_ne_zero z hz
  exact hj.congr (fun z hz => jFunction_ext_eq z hz)


-- created on 2026-10-23
