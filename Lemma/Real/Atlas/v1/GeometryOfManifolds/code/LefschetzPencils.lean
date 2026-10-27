import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part7
open DifferentialFormSpace


/--
[SymplecticFibration.fiber_pullback_base_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma SymplecticFibration.fiber_pullback_base_zero
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {ωB_data : SymplecticManifold Ω_B VF_B}
-- given
  (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)) :
-- imply
  fib.fiberInclusion.pullback (fib.f.pullback ωB_data.ω) = 0 :=
-- proof
  fib.fiber_pullback_base_zero_general ωB_data.ω

/--
[SymplecticFibration.fiberInclusion_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma SymplecticFibration.fiberInclusion_surjective
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {p : ℕ}
  {β : Ω_F p}
-- given
  (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)) :
-- imply
  ∃ (γ : Ω_M p), fib.fiberInclusion.pullback γ = β := by
-- proof
  obtain ⟨i, hi⟩ := fib.fiberInclusion_eq_localTriv
  obtain ⟨γ, hγ⟩ := fib.localTriv_surjective i β
  exact ⟨γ, by rw [hi, hγ]⟩

/--
[thurston_global_correction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma thurston_global_correction
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  [IsCompactManifold Ω_M VF_M]
  {baseSymplectic : SymplecticManifold Ω_B VF_B}
  {η : Ω_M 2}
-- given
  (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
  (η_closed : inst_M.d η = 0)
  (η_cohomological : ∃ (β : Ω_F 1), fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω + inst_F.d β) :
-- imply
  ∃ (correction : Ω_M 1), fib.fiberInclusion.pullback (η + inst_M.d correction) = fib.fiberSymplectic.ω := by
-- proof
  obtain ⟨β, hβ⟩ := η_cohomological
  obtain ⟨γ, hγ⟩ := fib.fiberInclusion_surjective (-β : Ω_F 1)
  exact ⟨γ, by
    rw [fib.fiberInclusion.pullback_add, fib.fiberInclusion.pullback_comm_d, hγ, hβ]
    have hd_neg : inst_F.d (-β) = -(inst_F.d β) := by
      have h := inst_F.d_smul (-1 : ℝ) β
      simp only [neg_one_smul] at h
      exact h
    rw [hd_neg]
    abel⟩

/--
[pullback_vanishes_on_verticals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma pullback_vanishes_on_verticals
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  {f_map : DFSMorphism Ω_M VF_M Ω_B VF_B}
  {ωB : Ω_B 2}
  {projV : VF_M → VF_M}
-- given
  (hV_ker : ∀ (X : VF_M) {p : ℕ} (β : Ω_B (p + 1)), inst_M.ι (projV X) (f_map.pullback β) = 0) :
-- imply
  ∀ (X : VF_M), inst_M.ι (projV X) (f_map.pullback ωB) = 0 :=
-- proof
  fun X => hV_ker X ωB

/--
[eta_nondegen_on_verticals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma eta_nondegen_on_verticals
  {Ω_M : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M}
  {fiberSymplectic : SymplecticManifold Ω_F VF_F}
  {η : Ω_M 2}
  {projV : VF_M → VF_M}
  {restrictV : VF_M → VF_F}
-- given
  (h_fiber : fiberInclusion.pullback η = fiberSymplectic.ω)
  (h_compat : ∀ X : VF_M, fiberInclusion.pullback (inst_M.ι (projV X) η) = inst_F.ι (restrictV (projV X)) (fiberInclusion.pullback η))
  (h_restrictV_inj : ∀ X Y : VF_M, restrictV (projV X) = restrictV (projV Y) → projV X = projV Y) :
-- imply
  ∀ (X Y : VF_M), inst_M.ι (projV X) η = inst_M.ι (projV Y) η → projV X = projV Y := by
-- proof
  intro X Y h_eq
  have h_pb_eq : fiberInclusion.pullback (inst_M.ι (projV X) η) =
    fiberInclusion.pullback (inst_M.ι (projV Y) η) :=
    congrArg fiberInclusion.pullback h_eq
  rw [h_compat X, h_compat Y] at h_pb_eq
  rw [h_fiber] at h_pb_eq
  have h_restrict_eq : restrictV (projV X) = restrictV (projV Y) :=
    fiberSymplectic.nondegenerate h_pb_eq
  exact h_restrictV_inj X Y h_restrict_eq

/--
[horizontal_nondegen_for_large_k](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma horizontal_nondegen_for_large_k
  {Ω_M : ℕ → Type*}
  {Ω_B : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  [IsCompactManifold Ω_M VF_M]
  {f_map : DFSMorphism Ω_M VF_M Ω_B VF_B}
  {baseSymplectic : SymplecticManifold Ω_B VF_B}
  {η : Ω_M 2}
  {projV : VF_M → VF_M}
-- given
  (hdf_nondegen_H : ∀ (X Y : VF_M), projV X = projV Y → inst_M.ι X (f_map.pullback baseSymplectic.ω) = inst_M.ι Y (f_map.pullback baseSymplectic.ω) → X = Y)
  (h_perturb_stable : ∀ (ω₀ : Ω_M 2), (∀ (X Y : VF_M), projV X = projV Y → inst_M.ι X ω₀ = inst_M.ι Y ω₀ → X = Y) → ∃ (k₀ : ℕ), 1 ≤ k₀ ∧ ∀ (k : ℕ), k₀ ≤ k → ∀ (X Y : VF_M), projV X = projV Y → inst_M.ι X (ω₀ + ((k : ℝ)⁻¹) • η) = inst_M.ι Y (ω₀ + ((k : ℝ)⁻¹) • η) → X = Y) :
-- imply
  ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k → ∀ (X Y : VF_M), projV X = projV Y → inst_M.ι X (η + (k : ℝ) • f_map.pullback baseSymplectic.ω) = inst_M.ι Y (η + (k : ℝ) • f_map.pullback baseSymplectic.ω) → X = Y := by
-- proof
  obtain ⟨k₀, hk₀_pos, hk₀⟩ := h_perturb_stable (f_map.pullback baseSymplectic.ω) hdf_nondegen_H
  refine ⟨k₀, fun k hk X Y hprojV hι => ?_⟩
  have hk_ge_one : 1 ≤ k := le_trans hk₀_pos hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hk_ge_one |>.bot_lt)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hform_eq : η + (k : ℝ) • f_map.pullback baseSymplectic.ω =
    (k : ℝ) • (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hk_ne, one_smul, add_comm]
  rw [hform_eq] at hι
  rw [inst_M.ι_smul X (k : ℝ), inst_M.ι_smul Y (k : ℝ)] at hι
  have hι_inner : inst_M.ι X (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) =
    inst_M.ι Y (f_map.pullback baseSymplectic.ω + ((k : ℝ)⁻¹) • η) := by
    exact (IsUnit.mk0 (k : ℝ) hk_ne).smul_left_cancel.mp hι
  exact hk₀ k hk X Y hprojV hι_inner

/--
[eta_nondegenerate_on_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma eta_nondegenerate_on_vertical
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_B : ℕ → Type*}
  [inst_B : DifferentialFormSpace Ω_B VF_B]
  {Ω_F : ℕ → Type*}
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {baseSymplectic : SymplecticManifold Ω_B VF_B}
  {η : Ω 2}
  {tsd : ThurstonSplittingData fib baseSymplectic η h_η_restricts}
  {X Y : VF}
-- given
  (fib : SymplecticFibration (inst_M := inst) (inst_B := inst_B) (inst_F := inst_F))
  (h_η_restricts : fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω)
  (hι : inst.ι (tsd.projV X) η = inst.ι (tsd.projV Y) η) :
-- imply
  tsd.projV X = tsd.projV Y :=
-- proof
  tsd.eta_nondegen_vertical X Y hι

/--
[ι_one_form_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
This is the non-degeneracy of the contraction pairing on 1-forms. -/
lemma ι_one_form_eq
  {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
  (α β : Ω 1) (h : ∀ X : VF, inst.ι X α = inst.ι X β) : α = β := by
  have hsub : α - β = 0 := by
    apply inst.ι_one_form_nondegenerate
    intro X
    have hX := h X
    have : inst.ι X (α - β) = inst.ι X α - inst.ι X β := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rw [show -β = (-1 : ℝ) • β from (neg_one_smul ℝ β).symm]
      rw [inst.ι_add, inst.ι_smul]
      rw [neg_one_smul]
    rw [this, hX, sub_self]
  exact sub_eq_zero.mp hsub

/--
[vertical_contraction_ignores_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma vertical_contraction_ignores_base
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {η β : Ω 2}
  {X_V : VF}
  {k : ℝ}
-- given
  (hV_beta : inst.ι X_V β = 0) :
-- imply
  inst.ι X_V (η + k • β) = inst.ι X_V η := by
-- proof
  rw [inst.ι_add, inst.ι_smul, hV_beta, smul_zero, add_zero]

/--
[extract_vertical_eta_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma extract_vertical_eta_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {η β : Ω 2}
  {k : ℝ}
  {X Y : VF}
-- given
  (split : TangentSplitting (inst := inst) η)
  (hV_beta : ∀ X : VF, inst.ι (split.projV X) β = 0)
  (hXY : inst.ι X (η + k • β) = inst.ι Y (η + k • β)) :
-- imply
  inst.ι (split.projV X) η = inst.ι (split.projV Y) η := by
-- proof
  apply ι_one_form_eq (inst := inst)
  intro Z
  have hVX : inst.ι (split.projV X) (η + k • β) = inst.ι (split.projV X) η :=
    vertical_contraction_ignores_base η β (split.projV X) k (hV_beta X)
  have hVY : inst.ι (split.projV Y) (η + k • β) = inst.ι (split.projV Y) η :=
    vertical_contraction_ignores_base η β (split.projV Y) k (hV_beta Y)
  have hdecomp_X := split.decompose X (η + k • β)
  have hdecomp_Y := split.decompose Y (η + k • β)
  rw [hVX] at hdecomp_X; rw [hVY] at hdecomp_Y
  have h1_eq : inst.ι (split.projV X) η + inst.ι (split.projH X) (η + k • β) =
    inst.ι (split.projV Y) η + inst.ι (split.projH Y) (η + k • β) := by
    rw [← hdecomp_X, ← hdecomp_Y]; exact hXY
  have hHZ_VX : inst.ι (split.projH Z) (inst.ι (split.projV X) η) = 0 := by
    rw [inst.ι_ι_anticomm]; simp [split.orthogonal Z X]
  have hHZ_VY : inst.ι (split.projH Z) (inst.ι (split.projV Y) η) = 0 := by
    rw [inst.ι_ι_anticomm]; simp [split.orthogonal Z Y]
  have hVZ_HX : inst.ι (split.projV Z) (inst.ι (split.projH X) (η + k • β)) = 0 := by
    rw [inst.ι_add (split.projH X), inst.ι_smul (split.projH X)]
    rw [inst.ι_add (split.projV Z)]
    rw [split.orthogonal X Z]
    rw [inst.ι_smul (split.projV Z)]
    rw [inst.ι_ι_anticomm, hV_beta Z]
    simp [neg_zero, smul_zero, DifferentialFormSpace.ι_zero_val]
  have hVZ_HY : inst.ι (split.projV Z) (inst.ι (split.projH Y) (η + k • β)) = 0 := by
    rw [inst.ι_add (split.projH Y), inst.ι_smul (split.projH Y)]
    rw [inst.ι_add (split.projV Z)]
    rw [split.orthogonal Y Z]
    rw [inst.ι_smul (split.projV Z)]
    rw [inst.ι_ι_anticomm, hV_beta Z]
    simp [neg_zero, smul_zero, DifferentialFormSpace.ι_zero_val]
  have hVZ_eq : inst.ι (split.projV Z) (inst.ι (split.projV X) η) =
    inst.ι (split.projV Z) (inst.ι (split.projV Y) η) := by
    have := congr_arg (inst.ι (split.projV Z)) h1_eq
    rwa [inst.ι_add (split.projV Z), inst.ι_add (split.projV Z),
      hVZ_HX, hVZ_HY, add_zero, add_zero] at this
  rw [split.decompose Z (inst.ι (split.projV X) η),
    split.decompose Z (inst.ι (split.projV Y) η)]
  rwa [hHZ_VX, hHZ_VY, add_zero, add_zero]

/--
[DFSMorphism.pullback_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma DFSMorphism.pullback_zero
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ} :
-- imply
  φ.pullback (0 : Ω₂ p) = 0 := by
-- proof
  have := φ.pullback_smul (0 : ℝ) (0 : Ω₂ p)
  simp only [zero_smul] at this; exact this

/--
[DFSMorphism.pullback_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma DFSMorphism.pullback_closed_form
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ}
  {α : Ω₂ p}
-- given
  (hclosed : inst₂.d α = 0) :
-- imply
  inst₁.d (φ.pullback α) = 0 := by
-- proof
  rw [← φ.pullback_comm_d, hclosed, φ.pullback_zero]

/--
[thurston_fiber_restriction_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma thurston_fiber_restriction_step
  {Ω_M : ℕ → Type*}
  {Ω_F : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_F : DifferentialFormSpace Ω_F VF_F]
  {i : DFSMorphism Ω_F VF_F Ω_M VF_M}
  {α₁ α₂ : Ω_M 2}
  {r₁ r₂ : ℝ}
  {ωF : Ω_F 2}
-- given
  (h₁ : i.pullback α₁ = ωF)
  (h₂ : i.pullback α₂ = ωF)
  (hsum : r₁ + r₂ = 1) :
-- imply
  i.pullback (r₁ • α₁ + r₂ • α₂) = ωF := by
-- proof
  rw [i.pullback_add, i.pullback_smul, i.pullback_smul, h₁, h₂]
  rw [← add_smul, hsum, one_smul]

/--
[branched_cover_form_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma branched_cover_form_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {η : Ω 2}
  {α : Ω 2}
  {ε : ℝ}
-- given
  (hη_closed : inst.d η = 0)
  (hα_exact : inst.d α = 0) :
-- imply
  inst.d (η + ε • α) = 0 := by
-- proof
  rw [inst.d_add, inst.d_smul, hη_closed, hα_exact, smul_zero, add_zero]

/--
[rescale_contraction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma rescale_contraction_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {η α : Ω 2}
  {ε : ℝ}
  {X Y : VF}
-- given
  (hε : ε ≠ 0)
  (h : inst.ι X (η + ε • α) = inst.ι Y (η + ε • α)) :
-- imply
  inst.ι X (α + ε⁻¹ • η) = inst.ι Y (α + ε⁻¹ • η) := by
-- proof
  have key : η + ε • α = ε • (α + ε⁻¹ • η) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hε, one_smul, add_comm]
  rw [key] at h
  rw [inst.ι_smul, inst.ι_smul] at h
  have h1 : ε⁻¹ • (ε • inst.ι X (α + ε⁻¹ • η)) = ε⁻¹ • (ε • inst.ι Y (α + ε⁻¹ • η)) :=
    congrArg (ε⁻¹ • ·) h
  simp [smul_smul, inv_mul_cancel₀ hε] at h1
  exact h1

/--
[branched_cover_perturbation_nondegeneracy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma branched_cover_perturbation_nondegeneracy
  {Ω_X : ℕ → Type*}
  {Ω_Y : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
  {α : Ω_X 2}
  {ε : ℝ}
-- given
  (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y))
  (bcpd : BranchedCoverPerturbationData (inst := inst_X) (bc.f.pullback bc.target.ω) α ε) :
-- imply
  ∃ (α' : Ω_X 2) (ε' : ℝ), inst_X.d α' = 0 ∧ Function.Injective (fun (X : VF_X) => inst_X.ι X (bc.f.pullback bc.target.ω + ε' • α')) := by
-- proof
  let η := bc.f.pullback bc.target.ω
  let split := bcpd.toTangentSplitting
  refine ⟨α, ε, bcpd.alpha_closed, fun X Y hXY => ?_⟩
  have h_rescaled : inst_X.ι X (α + ε⁻¹ • η) = inst_X.ι Y (α + ε⁻¹ • η) :=
    rescale_contraction_eq η α ε bcpd.ε_ne_zero X Y hXY
  have h_alpha_K_eq : inst_X.ι (split.projV X) α = inst_X.ι (split.projV Y) α :=
    extract_vertical_eta_eq α η ε⁻¹ split
      (fun Z => bcpd.pullback_vanishes_on_K Z)
      X Y h_rescaled
  have hK_eq : split.projV X = split.projV Y :=
    bcpd.alpha_nondeg_on_K X Y h_alpha_K_eq
  exact bcpd.complement_nondeg X Y hK_eq hXY

/--
[branched_cover_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma branched_cover_symplectic
  {Ω_X : ℕ → Type*}
  {Ω_Y : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
  {α : Ω_X 2}
  {ε : ℝ}
-- given
  (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y))
  (bcpd : BranchedCoverPerturbationData (inst := inst_X) (bc.f.pullback bc.target.ω) α ε) :
-- imply
  ∃ (ωX : Ω_X 2), inst_X.d ωX = 0 ∧ Function.Injective (fun (X : VF_X) => inst_X.ι X ωX) := by
-- proof
  obtain ⟨α', ε', hα_closed, h_nondeg⟩ :=
    branched_cover_perturbation_nondegeneracy bc α ε bcpd
  refine ⟨bc.f.pullback bc.target.ω + ε' • α', ?_, h_nondeg⟩
  have h_pullback_closed : inst_X.d (bc.f.pullback bc.target.ω) = 0 :=
    bc.f.pullback_closed_form bc.target.ω bc.target.closed
  exact branched_cover_form_closed (bc.f.pullback bc.target.ω) α' ε' h_pullback_closed hα_closed

/--
[HasAdjunctionData.gauss_bonnet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma HasAdjunctionData.gauss_bonnet
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S) :
-- imply
  hA.chern_tangent = 2 - 2 * (hA.genus : ℤ) :=
-- proof
  hA.gauss_bonnet_eq

/--
[HasAdjunctionData.normal_bundle_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma HasAdjunctionData.normal_bundle_degree
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S) :
-- imply
  hA.chern_normal = hA.selfIntersection :=
-- proof
  hA.normal_bundle_degree_eq

/--
[HasAdjunctionData.chern_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma HasAdjunctionData.chern_split
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S) :
-- imply
  hA.c₁_eval = hA.chern_tangent + hA.chern_normal :=
-- proof
  hA.chern_split_eq

/--
[HasAdjunctionData.genus_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma HasAdjunctionData.genus_formula
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S) :
-- imply
  hA.c₁_eval = 2 - 2 * (hA.genus : ℤ) + hA.selfIntersection := by
-- proof
  rw [hA.chern_split, hA.gauss_bonnet, hA.normal_bundle_degree]

/--
[adjunction_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma adjunction_formula
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S) :
-- imply
  hA.c₁_eval = 2 - 2 * (hA.genus : ℤ) + hA.selfIntersection :=
-- proof
  hA.genus_formula

/--
[adjunction_inequality_fiber_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean)
-/
@[path]
lemma adjunction_inequality_fiber_genus
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
-- given
  (hA : HasAdjunctionData S)
  (h_self_zero : hA.selfIntersection = 0)
  (h_adjunction_ineq : hA.selfIntersection ≥ 0 → 2 * (hA.genus : ℤ) - 2 ≥ hA.selfIntersection) :
-- imply
  hA.genus ≥ 1 := by
-- proof
  have hge : hA.selfIntersection ≥ 0 := by omega
  have h := h_adjunction_ineq hge
  omega


-- created on 2026-10-23
