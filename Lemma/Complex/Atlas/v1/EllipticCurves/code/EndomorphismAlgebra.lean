import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
open NumberField Module ConductorOrder
open scoped Quaternion
open Module
open TensorProduct
open WeierstrassCurve.Affine


/--
[ringOfIntegers_isOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma ringOfIntegers_isOrder
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  IsOrder K (integralClosure ℤ K).toSubring where fg_zmul := by
-- proof
  rw [show (integralClosure ℤ K).toSubring.toAddSubgroup.toIntSubmodule =
    Subalgebra.toSubmodule (integralClosure ℤ K) from by
    ext x; simp [AddSubgroup.toIntSubmodule]]
  have hfg := Submodule.fg_range (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap
  convert hfg using 1
  ext x
  constructor
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact hy
  span_eq_top := by
    rw [eq_top_iff]
    intro x _
    have hbasis := (integralBasis K).mem_span x
    apply Submodule.span_mono _ hbasis
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    rw [integralBasis_apply]
    exact (RingOfIntegers.basis K i).2
universe u
namespace ConductorOrder
variable {d : ℤ}

namespace ConductorOrder

/--
[mem_conductorOrder_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma mem_conductorOrder_iff
  {d : ℤ}
  {f : ℕ}
  {z : ℤ√d} :
-- imply
  z ∈ conductorOrder d f ↔ (f : ℤ) ∣ z.im :=
-- proof
  Iff.rfl

end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma conductorOrder_le_of_dvd
  {d : ℤ}
  {f₁ f₂ : ℕ}
-- given
  (h : f₂ ∣ f₁) :
-- imply
  conductorOrder d f₁ ≤ conductorOrder d f₂ := by
-- proof
  intro z hz
  simp only [mem_conductorOrder_iff] at *
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hz

end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma conductorOrder_fg
  {d : ℤ}
  {f : ℕ} :
-- imply
  (conductorOrder d f).toAddSubgroup.toIntSubmodule.FG := by
-- proof
  refine ⟨{(1 : ℤ√d), ⟨0, ↑f⟩}, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain rfl | rfl := hx
    · show (↑f : ℤ) ∣ (1 : ℤ√d).im; simp
    · show (↑f : ℤ) ∣ (⟨0, ↑f⟩ : ℤ√d).im; simp
  · intro z hz
    change (↑f : ℤ) ∣ z.im at hz
    obtain ⟨k, hk⟩ := hz
    have : z = z.re • (1 : ℤ√d) + k • (⟨0, ↑f⟩ : ℤ√d) := by
      ext <;> simp [hk, mul_comm]
    rw [this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end ConductorOrder

namespace ConductorOrder

/--
[intCast_mem_subring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma intCast_mem_subring
  {d : ℤ}
  {S : Subring (ℤ√d)}
  {n : ℤ} :
-- imply
  (n : ℤ√d) ∈ S := by
-- proof
  have : (n : ℤ√d) = n • (1 : ℤ√d) := by simp
  rw [this]; exact S.zsmul_mem S.one_mem n

end ConductorOrder

namespace ConductorOrder

/--
[mem_subring_of_dvd_im](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma mem_subring_of_dvd_im
  {d : ℤ}
  {S : Subring (ℤ√d)}
  {a : ℤ}
  {z : ℤ√d}
-- given
  (ha : (⟨0, a⟩ : ℤ√d) ∈ S)
  (hdvd : a ∣ z.im) :
-- imply
  z ∈ S := by
-- proof
  obtain ⟨k, hk⟩ := hdvd
  have h1 : z = (z.re : ℤ√d) + k • (⟨0, a⟩ : ℤ√d) := by
    ext <;> simp [hk, mul_comm]
  rw [h1]
  exact S.add_mem (intCast_mem_subring S z.re) (S.zsmul_mem ha k)

end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_isOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma conductorOrder_isOrder
  {d : ℤ}
  {f : ℕ}
-- given
  (hf : 0 < f) :
-- imply
  (conductorOrder d f).toAddSubgroup.toIntSubmodule.FG ∧ (∃ z ∈ conductorOrder d f, z.im ≠ 0) :=
-- proof
  ⟨conductorOrder_fg f, ⟨⟨0, f⟩, dvd_refl _, by positivity⟩⟩

end ConductorOrder

namespace ConductorOrder

/--
[exists_conductor_of_subring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma exists_conductor_of_subring
  {d : ℤ}
  {S : Subring (ℤ√d)}
-- given
  (hS : ∃ z ∈ S, z.im ≠ 0) :
-- imply
  ∃ f : ℕ, 0 < f ∧ S = conductorOrder d f := by
-- proof
  let H := S.toAddSubgroup.map (imAddHom d)
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic H
  have ha_ne : a ≠ 0 := by
    intro ha0
    obtain ⟨z, hzS, hzim⟩ := hS
    have : z.im ∈ H := ⟨z, hzS, rfl⟩
    rw [ha, ha0, AddSubgroup.closure_singleton_zero] at this
    exact hzim (AddSubgroup.mem_bot.mp this)
  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha_ne, ?_⟩
  ext z
  simp only [mem_conductorOrder_iff]
  constructor
  ·
    intro hz
    have : z.im ∈ H := ⟨z, hz, rfl⟩
    rw [ha, ← AddSubgroup.zmultiples_eq_closure, Int.mem_zmultiples_iff] at this
    rwa [Int.natAbs_dvd]
  ·
    intro hdvd
    have : a ∈ H := by
      rw [ha, ← AddSubgroup.zmultiples_eq_closure]
      exact AddSubgroup.mem_zmultiples a
    obtain ⟨w, hwS, hwim⟩ := this
    have him : w.im = a := hwim
    have h0a : (⟨0, a⟩ : ℤ√d) ∈ S := by
      have hw_eq : w - (w.re : ℤ√d) = ⟨0, w.im⟩ := by ext <;> simp
      have : (⟨0, w.im⟩ : ℤ√d) ∈ S :=
        hw_eq ▸ S.sub_mem hwS (intCast_mem_subring S w.re)
      rwa [him] at this
    exact mem_subring_of_dvd_im S h0a (Int.natAbs_dvd.mp hdvd)

end ConductorOrder

namespace ConductorOrder

/--
[orders_eq_conductorOrders](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma orders_eq_conductorOrders
  {d : ℤ} :
-- imply
  ∀ S : Subring (ℤ√d), (S.toAddSubgroup.toIntSubmodule.FG ∧ ∃ z ∈ S, z.im ≠ 0) ↔ ∃ f : ℕ, 0 < f ∧ S = conductorOrder d f := by
-- proof
  intro S
  constructor
  · exact fun ⟨_, h⟩ => exists_conductor_of_subring S h
  · rintro ⟨f, hf, rfl⟩
    exact conductorOrder_isOrder hf

end ConductorOrder

/--
[qI_mul_qI](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma qI_mul_qI
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qI a b * qI a b = (a : ℍ[k, a, b]) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[qJ_mul_qJ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma qJ_mul_qJ
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qJ a b * qJ a b = (b : ℍ[k, a, b]) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[qI_mul_qJ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma qI_mul_qJ
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qI a b * qJ a b = qK a b := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[qJ_mul_qI](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma qJ_mul_qI
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qJ a b * qI a b = -(qK a b) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[qI_mul_qJ_eq_neg_qJ_mul_qI](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma qI_mul_qJ_eq_neg_qJ_mul_qI
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qI a b * qJ a b = -(qJ a b * qI a b) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[finrank_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma finrank_eq_four
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  finrank k ℍ[k, a, b] = 4 :=
-- proof
  QuaternionAlgebra.finrank_eq_four a 0 b

/--
[reducedTrace_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma reducedTrace_mk
  [Field k]
  {a b : k}
  [Field k]
  {a b : k}
  {r x y z : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  reducedTrace a b ⟨r, x, y, z⟩ = 2 * r :=
-- proof
  rfl

/--
[reducedTrace_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma reducedTrace_coe
  [Field k]
  {a b : k}
  {c : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  reducedTrace a b (c : ℍ[k, a, b]) = 2 * c :=
-- proof
  rfl

/--
[basis_i_mul_i](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma basis_i_mul_i
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (quatBasis a b).i * (quatBasis a b).i = a • (1 : ℍ[k, a, b]) + (0 : k) • (quatBasis a b).i :=
-- proof
  (quatBasis a b).i_mul_i

/--
[basis_j_mul_j](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma basis_j_mul_j
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (quatBasis a b).j * (quatBasis a b).j = b • (1 : ℍ[k, a, b]) :=
-- proof
  (quatBasis a b).j_mul_j

/--
[basis_i_mul_j](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma basis_i_mul_j
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (quatBasis a b).i * (quatBasis a b).j = (quatBasis a b).k :=
-- proof
  (quatBasis a b).i_mul_j

/--
[basis_j_mul_i](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma basis_j_mul_i
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (quatBasis a b).j * (quatBasis a b).i = (0 : k) • (quatBasis a b).j - (quatBasis a b).k :=
-- proof
  (quatBasis a b).j_mul_i

/--
[hamilton_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_eq
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  Quaternion ℝ = ℍ[ℝ, -1, -1] :=
-- proof
  rfl

/--
[hamilton_i_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_i_sq
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qI (-1 : ℝ) (-1) * qI (-1 : ℝ) (-1) = (-1 : ℍ[ℝ, -1, -1]) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[hamilton_j_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_j_sq
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qJ (-1 : ℝ) (-1) * qJ (-1 : ℝ) (-1) = (-1 : ℍ[ℝ, -1, -1]) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[hamilton_ij_eq_neg_ji](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_ij_eq_neg_ji
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  qI (-1 : ℝ) (-1) * qJ (-1 : ℝ) (-1) = -(qJ (-1 : ℝ) (-1) * qI (-1 : ℝ) (-1)) := by
-- proof
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/--
[hamilton_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_finrank
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  finrank ℝ (Quaternion ℝ) = 4 :=
-- proof
  Quaternion.finrank_eq_four

/--
[hamilton_not_commutative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma hamilton_not_commutative
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  ¬ ∀ (a b : Quaternion ℝ), a * b = b * a := by
-- proof
  intro h
  have h1 := h ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩
  exact absurd (congr_arg QuaternionAlgebra.imK h1) (by norm_num)

/--
[reducedNorm_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma reducedNorm_mk
  [Field k]
  {a b : k}
  [Field k]
  {a b : k}
  {r x y z : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  reducedNorm a b ⟨r, x, y, z⟩ = r * r - a * (x * x) - b * (y * y) + a * b * (z * z) := by
-- proof
  simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk]; ring

/--
[mul_star_eq_algebraMap_reducedNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma mul_star_eq_algebraMap_reducedNorm
  [Field k]
  {a b : k}
  [Field k]
  {a b : k}
  {γ : ℍ[k, a, b]}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  γ * star γ = algebraMap k _ (reducedNorm a b γ) := by
-- proof
  cases γ with | mk r i j kk =>
  ext <;> simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk] <;> ring

/--
[star_mul_eq_algebraMap_reducedNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma star_mul_eq_algebraMap_reducedNorm
  [Field k]
  {a b : k}
  [Field k]
  {a b : k}
  {γ : ℍ[k, a, b]}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  star γ * γ = algebraMap k _ (reducedNorm a b γ) := by
-- proof
  cases γ with | mk r i j kk =>
  ext <;> simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk] <;> ring

/--
[isDivisionRing_iff_norm_anisotropic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma isDivisionRing_iff_norm_anisotropic
  [Field k]
  {a b : k}
  [Field k]
  {a b : k}
-- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (∀ γ : ℍ[k, a, b], reducedNorm a b γ = 0 → γ = 0) ↔ (∀ γ : ℍ[k, a, b], γ ≠ 0 → IsUnit γ) := by
-- proof
  constructor
  ·
    intro h γ hγ
    have hN : reducedNorm a b γ ≠ 0 := fun hN => hγ (h γ hN)
    exact ⟨⟨γ, (reducedNorm a b γ)⁻¹ • star γ,
      by rw [Algebra.mul_smul_comm, mul_star_eq_algebraMap_reducedNorm]
        simp [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN],
      by rw [Algebra.smul_mul_assoc, star_mul_eq_algebraMap_reducedNorm]
        simp [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN]⟩, rfl⟩
  ·
    intro h γ hN
    by_contra hγ
    obtain ⟨u, hu⟩ := h γ hγ
    have h1 : γ * star γ = 0 := by
      rw [mul_star_eq_algebraMap_reducedNorm, hN, map_zero]
    have h2 : star γ = 0 := by
      have key : ↑u * star γ = 0 := by rwa [hu]
      calc star γ = ↑u⁻¹ * (↑u * star γ) := by rw [Units.inv_mul_cancel_left]
        _ = ↑u⁻¹ * 0 := by rw [key]
        _ = 0 := mul_zero _
    have h3 : γ = 0 := by
      have := congr_arg star h2
      rwa [star_star, star_zero] at this
    exact hγ h3
/-- Promote a quaternion algebra `ℍ[k, a, b]` with anisotropic reduced norm to a
`DivisionRing`, by inverting nonzero elements via the conjugate. -/
@[reducible] noncomputable def toDivisionRing {k : Type*} [Field k] (a b : k)
  (h : ∀ γ : ℍ[k, a, b], reducedNorm a b γ = 0 → γ = 0) :
  DivisionRing ℍ[k, a, b] :=
  DivisionRing.ofIsUnitOrEqZero (fun γ => by
    by_cases hγ : γ = 0
    · right; exact hγ
    · left; exact (isDivisionRing_iff_norm_anisotropic a b).mp h γ hγ)
section Lemma125
open TensorProduct

/--
[algebraMap_mul_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma algebraMap_mul_eq_smul
  [CommRing R]
  [Field K]
  [Algebra R K]
  {r : R}
  {k : K} :
-- imply
  (algebraMap R K) r * k = r • k := by
-- proof
  rw [Algebra.smul_def]

/--
[TensorProduct.exists_tmul_inv_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma TensorProduct.exists_tmul_inv_algebraMap
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup A]
  [Module R A]
  {x : A ⊗[R] K} :
-- imply
  ∃ (a : A) (s : nonZeroDivisors R), x = a ⊗ₜ[R] ((algebraMap R K) s)⁻¹ := by
-- proof
  induction x with
  | zero =>
    exact ⟨0, ⟨1, Submonoid.one_mem _⟩, by simp [TensorProduct.zero_tmul]⟩
  | tmul m n =>
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) n
    dsimp at hs
    have hsne : (algebraMap R K) ↑s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [show n = (algebraMap R K) r * ((algebraMap R K) ↑s)⁻¹ from by
      rw [← mul_inv_cancel_right₀ hsne n, hs],
      algebraMap_mul_eq_smul, ← smul_tmul]
    exact ⟨r • m, s, rfl⟩
  | add x y hx hy =>
    obtain ⟨a₁, s₁, rfl⟩ := hx
    obtain ⟨a₂, s₂, rfl⟩ := hy
    have hs₁ := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2 (K := K)
    have hs₂ := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2 (K := K)
    rw [show ((algebraMap R K) ↑s₁)⁻¹ =
      (algebraMap R K) ↑s₂ * ((algebraMap R K) (↑s₁ * ↑s₂))⁻¹ from by
        rw [map_mul, mul_inv, mul_comm ((algebraMap R K) ↑s₁)⁻¹,
          ← mul_assoc, mul_inv_cancel₀ hs₂, one_mul],
      show ((algebraMap R K) ↑s₂)⁻¹ =
        (algebraMap R K) ↑s₁ * ((algebraMap R K) (↑s₁ * ↑s₂))⁻¹ from by
          rw [map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs₁, one_mul],
      algebraMap_mul_eq_smul, algebraMap_mul_eq_smul,
      ← smul_tmul, ← smul_tmul, ← add_tmul]
    exact ⟨(↑s₂ : R) • a₁ + (↑s₁ : R) • a₂,
      ⟨↑s₁ * ↑s₂, (nonZeroDivisors R).mul_mem s₁.2 s₂.2⟩, rfl⟩

/--
[TensorProduct.exists_pure_tensor_fractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma TensorProduct.exists_pure_tensor_fractionRing
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup A]
  [Module R A]
  {x : A ⊗[R] K} :
-- imply
  ∃ a : A, ∃ b : K, x = a ⊗ₜ[R] b :=
-- proof
  let ⟨a, s, h⟩ := TensorProduct.exists_tmul_inv_algebraMap x
  ⟨a, ((algebraMap R K) s)⁻¹, h⟩

/--
[TensorProduct.exists_pure_tensor_int_rat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[path]
lemma TensorProduct.exists_pure_tensor_int_rat
  [AddCommGroup M]
  [Module ℤ M]
  {x : M ⊗[ℤ] ℚ} :
-- imply
  ∃ m : M, ∃ n : ℤ, n ≠ 0 ∧ x = m ⊗ₜ[ℤ] (n⁻¹ : ℚ) := by
-- proof
  obtain ⟨a, s, hs⟩ := TensorProduct.exists_tmul_inv_algebraMap x
  exact ⟨a, ↑s, nonZeroDivisors.ne_zero s.2, by rw [hs]; congr 1⟩
end Lemma125
section Corollary1220
open WeierstrassCurve.Affine
universe v
variable {F : Type v} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)
/-- The subring of "isogeny endomorphisms" of `E` inside the full endomorphism ring;
this is the subring relevant for Corollary 12.20. -/
end Corollary1220
section Definition1221
open WeierstrassCurve.Affine
universe w
variable {F : Type w} [Field F] [DecidableEq F]
/-- Definition 12.21: an elliptic curve `E` has complex multiplication if
`End(E) ≇ ℤ`. -/
end Definition1221


-- created on 2026-10-23
