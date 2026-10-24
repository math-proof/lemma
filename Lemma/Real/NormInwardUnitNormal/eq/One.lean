import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.InnerProductWalls
import Lemma.Finset.Inner.ne.Zero.of.Nonempty.All_Ne_0
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[norm_inwardUnitNormal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma norm_inwardUnitNormal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {η : AffineHyperplane E}
  [Decidable (ChamberInPositiveHalfSpace C η)] :
-- imply
  ‖inwardUnitNormal C η‖ = 1 := by
-- proof
  unfold inwardUnitNormal
  split
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero
  · rw [norm_smul, norm_inv, norm_norm, norm_neg, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[root_diff_mem_of_inner_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma root_diff_mem_of_inner_pos
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {Φ : FiniteReflectionGroups.RootSystem E}
  {α β : E}
-- given
  (hcryst : Φ.IsCrystallographic)
  (hα : α ∈ Φ.roots)
  (hβ : β ∈ Φ.roots)
  (hne : α ≠ β)
  (hneg : α ≠ -β)
  (hpos : @inner ℝ _ _ α β > 0) :
-- imply
  α - β ∈ Φ.roots := by
-- proof
  open FiniteReflectionGroups in
  obtain ⟨n, hn⟩ := hcryst β hβ α hα
  obtain ⟨m, hm⟩ := hcryst α hα β hβ
  have hα_ne : α ≠ 0 := Φ.roots_ne_zero α hα
  have hβ_ne : β ≠ 0 := Φ.roots_ne_zero β hβ
  have hαα_pos : ⟪α, α⟫_ℝ > 0 := by rw [real_inner_self_eq_norm_sq]; positivity
  have hββ_pos : ⟪β, β⟫_ℝ > 0 := by rw [real_inner_self_eq_norm_sq]; positivity
  have hcoroot_α : ⟪β, coroot α⟫_ℝ = (2 / ⟪α, α⟫_ℝ) * ⟪β, α⟫_ℝ := by
    simp only [coroot, real_inner_smul_right]
  have hcoroot_β : ⟪α, coroot β⟫_ℝ = (2 / ⟪β, β⟫_ℝ) * ⟪α, β⟫_ℝ := by
    simp only [coroot, real_inner_smul_right]
  have hn_val : (n : ℝ) = 2 * ⟪α, β⟫_ℝ / ⟪α, α⟫_ℝ := by
    rw [← hn, hcoroot_α, real_inner_comm β α]; ring
  have hm_val : (m : ℝ) = 2 * ⟪α, β⟫_ℝ / ⟪β, β⟫_ℝ := by
    rw [← hm, hcoroot_β]; ring
  have hn_pos : (n : ℝ) > 0 := by rw [hn_val]; positivity
  have hn_ge_one : n ≥ 1 := Int.lt_iff_add_one_le.mp (by exact_mod_cast hn_pos)
  have hm_pos : (m : ℝ) > 0 := by rw [hm_val]; positivity
  have hm_ge_one : m ≥ 1 := Int.lt_iff_add_one_le.mp (by exact_mod_cast hm_pos)
  have cs : ⟪α, β⟫_ℝ * ⟪α, β⟫_ℝ ≤ ⟪α, α⟫_ℝ * ⟪β, β⟫_ℝ := by
    have h1 := real_inner_le_norm α β
    have h2 := real_inner_le_norm α (-β)
    simp only [inner_neg_right, norm_neg] at h2
    have : ⟪α, β⟫_ℝ ^ 2 ≤ (‖α‖ * ‖β‖) ^ 2 := sq_le_sq' (by linarith) h1
    rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at this
    nlinarith [sq_abs (⟪α, β⟫_ℝ)]
  have hnm_eq : (n : ℝ) * m = 4 * (⟪α, β⟫_ℝ * ⟪α, β⟫_ℝ) / (⟪α, α⟫_ℝ * ⟪β, β⟫_ℝ) := by
    rw [hn_val, hm_val]; field_simp; ring
  have hnm_le : (n : ℝ) * m ≤ 4 := by
    rw [hnm_eq]; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hnm_le_int : n * m ≤ 4 := by exact_mod_cast hnm_le
  have h_n1_or_m1 : n = 1 ∨ m = 1 := by
    by_contra h_neither
    push_neg at h_neither
    have hn2 : n ≥ 2 := by omega
    have hm2 : m ≥ 2 := by omega
    have h4 : n * m ≥ 4 := by nlinarith
    have hn_eq : n = 2 := by nlinarith
    have hm_eq : m = 2 := by nlinarith
    have h_inner_eq_αα : ⟪α, β⟫_ℝ = ⟪α, α⟫_ℝ := by
      have : (n : ℝ) = 2 := by exact_mod_cast hn_eq
      rw [hn_val] at this; field_simp at this; linarith
    have h_inner_eq_ββ : ⟪α, β⟫_ℝ = ⟪β, β⟫_ℝ := by
      have : (m : ℝ) = 2 := by exact_mod_cast hm_eq
      rw [hm_val] at this; field_simp at this; linarith
    have h_zero : ⟪α - β, α - β⟫_ℝ = 0 := by
      simp only [inner_sub_left, inner_sub_right]
      nlinarith [real_inner_comm β α]
    exact hne (sub_eq_zero.mp (inner_self_eq_zero.mp h_zero))
  obtain hn1 | hm1 := h_n1_or_m1
  ·
    have h_coeff : 2 * ⟪α, β⟫_ℝ / ⟪α, α⟫_ℝ = 1 := by
      linarith [show (n : ℝ) = 1 from by exact_mod_cast hn1, hn_val]
    have h_refl : linearReflection α β = β - α := by
      simp only [linearReflection, h_coeff, one_smul]
    have h_mem := Φ.reflection_closed α hα β hβ
    rw [show α - β = -(β - α) from by abel, ← h_refl]
    exact Φ.neg_mem_roots h_mem
  ·
    have h_coeff : 2 * ⟪β, α⟫_ℝ / ⟪β, β⟫_ℝ = 1 := by
      rw [real_inner_comm]
      linarith [show (m : ℝ) = 1 from by exact_mod_cast hm1, hm_val]
    have h_refl : linearReflection β α = α - β := by
      simp only [linearReflection, h_coeff, one_smul]
    rw [← h_refl]
    exact Φ.reflection_closed β hβ α hα

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[simple_roots_inner_nonpos_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma simple_roots_inner_nonpos_axiom
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {Φ : FiniteReflectionGroups.RootSystem E}
  {f : E → ℝ}
  {α β : E}
-- given
  (hcryst : Φ.IsCrystallographic)
  (hf_linear : IsLinearMap ℝ f)
  (hf_nonzero : ∀ α ∈ Φ.roots, f α ≠ 0)
  (hα : Φ.IsSimpleRoot f α)
  (hβ : Φ.IsSimpleRoot f β)
  (hne : α ≠ β) :
-- imply
  @inner ℝ _ _ α β ≤ 0 := by
-- proof
  by_contra h_pos
  push_neg at h_pos
  have hα_pos : α ∈ Φ.positiveRootSet f := hα.1
  have hβ_pos : β ∈ Φ.positiveRootSet f := hβ.1
  have hα_root : α ∈ Φ.roots := hα_pos.1
  have hβ_root : β ∈ Φ.roots := hβ_pos.1
  have hfα : f α > 0 := hα_pos.2
  have hfβ : f β > 0 := hβ_pos.2
  have hα_simple := hα.2
  have hβ_simple := hβ.2
  have hα_ne_neg_β : α ≠ -β := by
    intro h
    have h1 : f α = f (-β) := by rw [h]
    have hf_map_smul' : ∀ (r : ℝ) (x : E), f (r • x) = r * f x := hf_linear.2
    have h2 : f (-β) = (-1 : ℝ) * f β := by rw [← hf_map_smul']; simp
    linarith
  have h_diff_root : α - β ∈ Φ.roots :=
    root_diff_mem_of_inner_pos Φ hcryst hα_root hβ_root hne hα_ne_neg_β h_pos
  have hf_diff_ne : f (α - β) ≠ 0 := hf_nonzero (α - β) h_diff_root
  have hf_map_add : ∀ (x y : E), f (x + y) = f x + f y := hf_linear.1
  have hf_map_smul : ∀ (r : ℝ) (x : E), f (r • x) = r * f x := hf_linear.2
  have hf_map_sub : ∀ (x y : E), f (x - y) = f x - f y := by
    intro x y; rw [sub_eq_add_neg, hf_map_add, show f (-y) = (-1) * f y from
      by rw [← hf_map_smul, neg_one_smul]]; ring
  have hf_diff_val : f (α - β) = f α - f β := hf_map_sub α β
  obtain hf_neg | hf_pos_diff := lt_or_gt_of_ne hf_diff_ne
  ·
    have h_neg_diff_root : β - α ∈ Φ.roots := by
      have : β - α = -(α - β) := by abel
      rw [this]; exact Φ.neg_mem_roots h_diff_root
    have hf_neg_diff : f (β - α) > 0 := by
      have : f (β - α) = f β - f α := hf_map_sub β α
      rw [this]; linarith [hf_diff_val]
    have h_neg_diff_pos : β - α ∈ Φ.positiveRootSet f := ⟨h_neg_diff_root, hf_neg_diff⟩
    apply hβ_simple
    exact ⟨β - α, α, h_neg_diff_pos, hα_pos, by abel⟩
  ·
    have h_diff_pos : α - β ∈ Φ.positiveRootSet f := ⟨h_diff_root, by linarith [hf_diff_val]⟩
    apply hα_simple
    exact ⟨α - β, β, h_diff_pos, hβ_pos, by abel⟩

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[linearReflection_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma linearReflection_unit
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {e v : E}
-- given
  (he : ‖e‖ = 1) :
-- imply
  FiniteReflectionGroups.linearReflection e v = v - (2 * ⟪e, v⟫_ℝ) • e := by
-- proof
  unfold FiniteReflectionGroups.linearReflection
  congr 1
  congr 1
  rw [real_inner_self_eq_norm_sq, he]
  norm_num

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[coroot_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma coroot_unit
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {e : E}
-- given
  (he : ‖e‖ = 1) :
-- imply
  FiniteReflectionGroups.coroot e = (2 : ℝ) • e := by
-- proof
  unfold FiniteReflectionGroups.coroot
  congr 1
  rw [real_inner_self_eq_norm_sq, he]
  norm_num

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[exists_in_ker_inner_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma exists_in_ker_inner_ne_zero
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {d : E}
  {S : Finset E}
-- given
  (hd : d ≠ 0)
  (_hS : ∀ γ ∈ S, γ ≠ 0)
  (hS_ne : S.Nonempty)
  (h_not_prop : ∀ γ ∈ S, ∀ c : ℝ, γ ≠ c • d) :
-- imply
  ∃ v : E, ⟪v, d⟫_ℝ = 0 ∧ ∀ γ ∈ S, ⟪v, γ⟫_ℝ ≠ 0 := by
-- proof
  classical
  let πd : E → E := fun x => x - (⟪x, d⟫_ℝ / ⟪d, d⟫_ℝ) • d
  let S' : Finset E := S.image πd
  have hS'_nz : ∀ w ∈ S', w ≠ 0 := by
    intro w hw
    simp only [S', Finset.mem_image] at hw
    obtain ⟨γ, hγ_mem, hγ_eq⟩ := hw
    rw [← hγ_eq]
    intro hc
    exact h_not_prop γ hγ_mem _ (by rwa [sub_eq_zero] at hc)
  have hS'_ne : S'.Nonempty := Finset.Nonempty.image hS_ne πd
  obtain ⟨u, hu⟩ := exists_inner_ne_zero_of_finite_nonzero S' hS'_nz hS'_ne
  refine ⟨πd u, ?_, ?_⟩
  ·
    show ⟪u - (⟪u, d⟫_ℝ / ⟪d, d⟫_ℝ) • d, d⟫_ℝ = 0
    rw [inner_sub_left, real_inner_smul_left, div_mul_cancel₀]
    · ring
    · exact inner_self_ne_zero.mpr hd
  ·
    intro γ hγ_mem
    have self_adj : ⟪πd u, γ⟫_ℝ = ⟪u, πd γ⟫_ℝ := by
      show ⟪u - (⟪u, d⟫_ℝ / ⟪d, d⟫_ℝ) • d, γ⟫_ℝ =
        ⟪u, γ - (⟪γ, d⟫_ℝ / ⟪d, d⟫_ℝ) • d⟫_ℝ
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm d γ]
      ring
    rw [self_adj]
    exact hu (πd γ) (Finset.mem_image.mpr ⟨γ, hγ_mem, rfl⟩)

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[coxeter_arrangement_dihedral_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma coxeter_arrangement_dihedral_finite
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber}
  {η ζ : AffineHyperplane E}
  [inst_η : Decidable (ChamberInPositiveHalfSpace C η)]
  [inst_ζ : Decidable (ChamberInPositiveHalfSpace C ζ)]
-- given
  (hη : η ∈ arr.hyperplanes)
  (hζ : ζ ∈ arr.hyperplanes)
  (hη_wall : η.IsWall C.set)
  (hζ_wall : ζ.IsWall C.set) :
-- imply
  ∃ n : ℤ, (2 : ℝ) * ⟪inwardUnitNormal C η, inwardUnitNormal C ζ⟫_ℝ = ↑n := by
-- proof
  obtain ⟨n, hn⟩ := CoxeterArrangement.locally_finite C η ζ hη hζ hη_wall hζ_wall
  unfold inwardUnitNormal
  split_ifs with hη_pos hζ_pos hζ_pos
  · exact ⟨n, hn⟩
  · refine ⟨-n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • (-ζ.normal)⟫_ℝ =
      -⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_right, inner_neg_right]
    rw [this, mul_neg, hn]; push_cast; ring
  · refine ⟨-n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • (-η.normal), (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ =
      -⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_left, inner_neg_left]
    rw [this, mul_neg, hn]; push_cast; ring
  · refine ⟨n, ?_⟩
    have : ⟪(‖η.normal‖⁻¹) • (-η.normal), (‖ζ.normal‖⁻¹) • (-ζ.normal)⟫_ℝ =
      ⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ := by
      simp [inner_smul_left, inner_smul_right, inner_neg_left, inner_neg_right]
    rw [this, hn]

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[linearIndependent_of_unit_not_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma linearIndependent_of_unit_not_parallel
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {e f : E}
-- given
  (he : ‖e‖ = 1)
  (hf : ‖f‖ = 1)
  (h_not_parallel : ¬∃ c : ℝ, f = c • e) :
-- imply
  LinearIndependent ℝ ![e, f] := by
-- proof
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  exact ⟨by intro h; rw [h, norm_zero] at hf; linarith,
    fun a ha => h_not_parallel ⟨a⁻¹, by
      have he_ne : e ≠ 0 := by intro h; rw [h, norm_zero] at he; linarith
      have ha_ne : a ≠ 0 := by intro h; rw [h, zero_smul] at ha; exact he_ne ha.symm
      rw [← ha, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]⟩⟩

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[closure_subset_closedHalfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma closure_subset_closedHalfSpace
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {n : E}
  {a : ℝ}
  {S : Set E}
-- given
  (hS : S ⊆ {x : E | @inner ℝ _ _ n x > a}) :
-- imply
  closure S ⊆ {x : E | @inner ℝ _ _ n x ≥ a} := by
-- proof
  apply closure_minimal
  · intro y hy
    have := hS hy
    simp only [mem_setOf_eq] at this ⊢
    linarith
  · exact isClosed_le continuous_const (continuous_const.inner continuous_id')

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[wall_carrier_meets_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma wall_carrier_meets_closure
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {η : AffineHyperplane E}
  {C : Set E}
-- given
  (hw : η.IsWall C) :
-- imply
  (η.carrier ∩ closure C).Nonempty := by
-- proof
  obtain ⟨U, _, hU_nonempty, hU_sub⟩ := hw
  obtain ⟨p, hp⟩ := hU_nonempty
  exact ⟨p, hp.2, hU_sub hp⟩

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[inwardNormal_carrier_and_halfspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma inwardNormal_carrier_and_halfspace
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {η : AffineHyperplane E}
  {x : E}
  [inst_η : Decidable (ChamberInPositiveHalfSpace C η)]
-- given
  (hη : η ∈ arr.hyperplanes)
  (hx : x ∈ C.set) :
-- imply
  ∃ a : ℝ, (∀ y, y ∈ η.carrier ↔ @inner ℝ _ _ (inwardUnitNormal C η) y = a) ∧ (∀ y, y ∈ C.set → @inner ℝ _ _ (inwardUnitNormal C η) y > a) := by
-- proof
  set e := inwardUnitNormal C η
  obtain hpos | hneg := chamber_subset_halfSpace C hη
  ·
    have he_eq : e = ‖η.normal‖⁻¹ • η.normal := by
      show inwardUnitNormal C η = _
      unfold inwardUnitNormal
      simp [show ChamberInPositiveHalfSpace C η from hpos]
    have h_inv_pos : (0 : ℝ) < ‖η.normal‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr η.normal_ne_zero)
    refine ⟨η.offset * ‖η.normal‖⁻¹, ?_, ?_⟩
    · intro y
      simp only [AffineHyperplane.carrier, mem_setOf_eq, he_eq, real_inner_smul_left]
      constructor <;> intro h <;> nlinarith
    · intro y hy
      have := hpos hy
      simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at this
      simp only [he_eq, real_inner_smul_left]
      nlinarith
  ·
    have he_eq : e = ‖η.normal‖⁻¹ • (-η.normal) := by
      show inwardUnitNormal C η = _
      unfold inwardUnitNormal
      split_ifs with h
      · exfalso
        have h1 := h hx
        have h2 := hneg hx
        simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at h1
        simp only [AffineHyperplane.negativeHalfSpace, mem_setOf_eq] at h2
        linarith
      · rfl
    have h_inv_pos : (0 : ℝ) < ‖η.normal‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr η.normal_ne_zero)
    refine ⟨-(η.offset * ‖η.normal‖⁻¹), ?_, ?_⟩
    · intro y
      simp only [AffineHyperplane.carrier, mem_setOf_eq, he_eq,
        real_inner_smul_left, inner_neg_left]
      constructor <;> intro h <;> nlinarith
    · intro y hy
      have := hneg hy
      simp only [AffineHyperplane.negativeHalfSpace, mem_setOf_eq] at this
      simp only [he_eq, real_inner_smul_left, inner_neg_left]
      nlinarith
/-- *Inner product of inward unit normals of distinct walls is non-positive* (without the
non-parallel hypothesis): this is the geometric heart of the Coxeter property. We split into
the parallel and non-parallel cases. In the parallel case $f = c \cdot e$ with $|c| = 1$, so
$c = 1$ (impossible, since it would force $\eta.carrier = \zeta.carrier$ — contradicted using
`closure_subset_closedHalfSpace` and `wall_carrier_meets_closure`) or $c = -1$ (giving
$\langle e, f\rangle = -1 \le 0$). In the non-parallel case, this reduces to
`nonparallel_walls_inner_nonpos`. -/

end HyperplaneArrangement


-- created on 2026-10-23
-- updated on 2026-10-24
