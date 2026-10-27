import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
open DifferentialFormSpace


/--
[Codifferential.formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma Codifferential.formula
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {ω : Ω (p + 1)}
-- given
  (cod : Codifferential (inst := inst))
  (h : p + 1 ≤ cod.manifold_dim) :
-- imply
  cod.dstar ω = cod.sign_factor (p + 1) • cast (by congr 1; omega) (cod.star_deg (by omega : cod.manifold_dim - (p + 1) + 1 ≤ cod.manifold_dim) (inst.d (cod.star_deg h ω))) :=
-- proof
  cod.dstar_formula h ω

/--
[L2InnerProduct.inner_product_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma L2InnerProduct.inner_product_axioms
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ} :
-- imply
  (∀ (α β : Ω p), ip.inner α β = ip.inner β α) ∧ (∀ (α β γ : Ω p), ip.inner (α + β) γ = ip.inner α γ + ip.inner β γ) ∧ (∀ (r : ℝ) (α β : Ω p), ip.inner (r • α) β = r * ip.inner α β) ∧ (∀ (α : Ω p), (0 : ℝ) ≤ ip.inner α α) ∧ (∀ (α : Ω p), ip.inner α α = 0 → α = 0) :=
-- proof
  ⟨ip.inner_symm, ip.inner_add_left, ip.inner_smul_left,
    ip.inner_self_nonneg, ip.inner_self_eq_zero⟩

/--
[Codifferential.dstar_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma Codifferential.dstar_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
-- given
  (cod : Codifferential (inst := inst)) :
-- imply
  cod.dstar (0 : Ω (p + 1)) = (0 : Ω p) := by
-- proof
  have h := cod.dstar_smul (0 : ℝ) (0 : Ω (p + 1))
  simp [zero_smul] at h; exact h

/--
[L2InnerProduct.inner_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma L2InnerProduct.inner_zero_left
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω p} :
-- imply
  ip.inner 0 α = 0 := by
-- proof
  have h := ip.inner_smul_left (0 : ℝ) (0 : Ω p) α
  simp [zero_mul] at h; exact h

/--
[harmonic_iff_closed_coclosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma harmonic_iff_closed_coclosed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (cod : Codifferential (inst := inst)) :
-- imply
  IsHarmonic cod α ↔ (inst.d α = 0 ∧ cod.dstar α = 0) := by
-- proof
  constructor
  ·
    intro h
    unfold IsHarmonic laplacian at h
    have eq1 : ip.inner (inst.d (cod.dstar α)) α =
      ip.inner (cod.dstar α) (cod.dstar α) :=
      ip.adjoint_d (cod.dstar α) α
    have eq2 : ip.inner (cod.dstar (inst.d α)) α =
      ip.inner (inst.d α) (inst.d α) := by
      rw [ip.inner_symm (cod.dstar (inst.d α)) α,
        ip.adjoint_d α (inst.d α), ip.inner_symm]
    have sum_eq : ip.inner (cod.dstar α) (cod.dstar α) +
      ip.inner (inst.d α) (inst.d α) = 0 := by
      have step : ip.inner (inst.d (cod.dstar α) + cod.dstar (inst.d α)) α =
        ip.inner (cod.dstar α) (cod.dstar α) +
        ip.inner (inst.d α) (inst.d α) := by
        rw [ip.inner_add_left, eq1, eq2]
      rw [h, ip.inner_zero_left] at step
      linarith
    have h_dstar : ip.inner (cod.dstar α) (cod.dstar α) = 0 := by
      linarith [ip.inner_self_nonneg (cod.dstar α),
        ip.inner_self_nonneg (inst.d α)]
    have h_d : ip.inner (inst.d α) (inst.d α) = 0 := by linarith
    exact ⟨ip.inner_self_eq_zero _ h_d, ip.inner_self_eq_zero _ h_dstar⟩
  ·
    intro ⟨hclosed, hcoclosed⟩
    unfold IsHarmonic laplacian
    rw [hclosed, hcoclosed, d_zero_val, Codifferential.dstar_zero]
    simp

/--
[kahler_box_eq_box_bar_blocker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_box_eq_box_bar_blocker
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J _hK dol_lap}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p)
  (delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p)
  (box : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  (box_bar : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  (hbox_def : ∀ {p : ℕ} (α : Ω (p + 1)), box α = dol.del (del_star α) + del_star (dol.del α))
  (hbox_bar_def : ∀ {p : ℕ} (α : Ω (p + 1)), box_bar α = dol.delbar (delbar_star α) + delbar_star (dol.delbar α))
  (h_del_star : ∀ {p : ℕ} (α : Ω (p + 1)), del_star α = dol_lap.del_star α)
  (h_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)), delbar_star α = dol_lap.delbar_star α) :
-- imply
  box α = box_bar α := by
-- proof
  rw [hbox_def α, hbox_bar_def α]
  simp only [h_del_star, h_delbar_star]
  have h_anti1 := wells.del_delbar_star_anticommute α
  have h_anti2 := wells.delbar_del_star_anticommute α
  have h_wells := wells.wells_expansion α
  have hef : (dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α)) = 0 := h_anti1
  have hgh : (dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α)) = 0 := h_anti2
  have key : (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) -
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)) = 0 := by
    have := h_wells
    rw [hef, hgh] at this
    simp only [add_zero, sub_zero] at this
    exact this
  exact sub_eq_zero.mp key

/--
[kahler_del_delbar_star_anticommute_blocker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_del_delbar_star_anticommute_blocker
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J _hK dol_lap}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J) :
-- imply
  dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
-- proof
  wells.del_delbar_star_anticommute α

/--
[kahler_delbar_del_star_anticommute_blocker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_delbar_del_star_anticommute_blocker
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J _hK dol_lap}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J) :
-- imply
  dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
-- proof
  wells.delbar_del_star_anticommute α

/--
[kahler_two_box_bar_blocker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_two_box_bar_blocker
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J _hK dol_lap}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J) :
-- imply
  dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α := by
-- proof
  have h_box_eq : dol_lap.box α = dol_lap.box_bar α :=
    kahler_box_eq_box_bar_blocker S J _hK dol_lap
      dol_lap.del_star dol_lap.delbar_star
      dol_lap.box dol_lap.box_bar
      (fun α => rfl) (fun α => rfl) wells
      (fun α => rfl) (fun α => rfl) α
  have h_anti1 : dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
    kahler_del_delbar_star_anticommute_blocker S J _hK dol_lap wells α
  have h_anti2 : dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
    kahler_delbar_del_star_anticommute_blocker S J _hK dol_lap wells α
  show dol_lap.box_bar α + dol_lap.box_bar α =
    inst.d (cod.dstar α) + cod.dstar (inst.d α)
  have h_expand : inst.d (cod.dstar α) + cod.dstar (inst.d α) =
    dol_lap.box α + dol_lap.box_bar α := by
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
      (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))
    rw [dol_lap.dstar_decomp α]
    rw [inst.d_add]
    rw [dol.decomp (dol_lap.del_star α)]
    rw [dol.decomp (dol_lap.delbar_star α)]
    rw [dol.decomp α]
    rw [cod.dstar_add]
    rw [dol_lap.dstar_decomp (dol.del α)]
    rw [dol_lap.dstar_decomp (dol.delbar α)]
    have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
      eq_neg_of_add_eq_zero_left h_anti1
    have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
      eq_neg_of_add_eq_zero_left h_anti2
    rw [hc1', hc2']
    abel
  rw [h_expand, h_box_eq]

/--
[kahler_laplacian_eq_box_plus_box_bar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_laplacian_eq_box_plus_box_bar
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {_S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (_J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler _S _J)
  (h_del_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)), dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0)
  (h_delbar_del_star : ∀ {p : ℕ} (α : Ω (p + 1)), dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0) :
-- imply
  laplacian cod α = dol_lap.box α + dol_lap.box_bar α := by
-- proof
  have h_anti1 := h_del_delbar_star α
  have h_anti2 := h_delbar_del_star α
  show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
    (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))
  rw [dol_lap.dstar_decomp α]
  rw [inst.d_add]
  rw [dol.decomp (dol_lap.del_star α)]
  rw [dol.decomp (dol_lap.delbar_star α)]
  rw [dol.decomp α]
  rw [cod.dstar_add]
  rw [dol_lap.dstar_decomp (dol.del α)]
  rw [dol_lap.dstar_decomp (dol.delbar α)]
  have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
    eq_neg_of_add_eq_zero_left h_anti1
  have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
    eq_neg_of_add_eq_zero_left h_anti2
  rw [hc1', hc2']
  abel

/--
[box_eq_box_bar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma box_eq_box_bar
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (h_del_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)), dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0)
  (h_delbar_del_star : ∀ {p : ℕ} (α : Ω (p + 1)), dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0)
  (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)), dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α) :
-- imply
  dol_lap.box α = dol_lap.box_bar α := by
-- proof
  have h1 : dol_lap.box α + dol_lap.box_bar α = laplacian cod α :=
    (kahler_laplacian_eq_box_plus_box_bar S J hK dol_lap h_del_delbar_star h_delbar_del_star α).symm
  have h2 : dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    h_two_box_bar α
  exact add_right_cancel (h1.trans h2.symm)

/--
[kahler_laplacian_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_laplacian_identity
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J _hK dol_lap}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (cod : Codifferential (inst := inst))
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  laplacian cod α = dol_lap.box α + dol_lap.box α ∧ laplacian cod α = dol_lap.box_bar α + dol_lap.box_bar α ∧ dol_lap.box α = dol_lap.box_bar α := by
-- proof
  have h_anticomm1 : dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
    kahler_del_delbar_star_anticommute_blocker S J _hK dol_lap wells α
  have h_anticomm2 : dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
    kahler_delbar_del_star_anticommute_blocker S J _hK dol_lap wells α
  have h_two_box_bar : dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    kahler_two_box_bar_blocker S J _hK dol_lap wells α
  have part1 : laplacian cod α = dol_lap.box α + dol_lap.box_bar α := by
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      dol_lap.box α + dol_lap.box_bar α
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
      (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))
    rw [dol_lap.dstar_decomp α]
    rw [inst.d_add]
    rw [dol.decomp (dol_lap.del_star α)]
    rw [dol.decomp (dol_lap.delbar_star α)]
    rw [dol.decomp α]
    rw [cod.dstar_add]
    rw [dol_lap.dstar_decomp (dol.del α)]
    rw [dol_lap.dstar_decomp (dol.delbar α)]
    have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
      eq_neg_of_add_eq_zero_left h_anticomm1
    have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
      eq_neg_of_add_eq_zero_left h_anticomm2
    rw [hc1', hc2']
    abel
  have part3 : dol_lap.box α = dol_lap.box_bar α :=
    add_right_cancel (part1.symm.trans h_two_box_bar.symm)
  have part2 : laplacian cod α = dol_lap.box_bar α + dol_lap.box_bar α :=
    h_two_box_bar.symm
  have part4 : laplacian cod α = dol_lap.box α + dol_lap.box α := by
    rw [part1, ← part3]
  exact ⟨part4, part2, part3⟩

/--
[dolbeault_identification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma dolbeault_identification
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol_lap : DolbeaultLaplacian dol cod}
  {k : ℕ}
  {α : Ω (k + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (cod : Codifferential (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)), dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α) :
-- imply
  laplacian cod α = 0 ↔ dol_lap.box_bar α = 0 := by
-- proof
  constructor
  ·
    intro hΔ
    have h := box_bar_eq_half_laplacian S J hK dol_lap (h_two_box_bar := h_two_box_bar) α
    rw [hΔ] at h
    have h2 : (2 : ℝ) • dol_lap.box_bar α = (0 : Ω (k + 1)) := by
      rw [two_smul]; exact h
    rw [smul_eq_zero] at h2
    exact h2.resolve_left (by norm_num)
  ·
    intro hbox
    have h := box_bar_eq_half_laplacian S J hK dol_lap (h_two_box_bar := h_two_box_bar) α
    rwa [hbox, add_zero] at h

/--
[JActsOnForms.J_form_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.J_form_neg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {Jf : JActsOnForms J}
  {p : ℕ}
  {α : Ω p} :
-- imply
  Jf.J_form (-α) = -(Jf.J_form α) := by
-- proof
  have h := Jf.J_form_smul (-1 : ℝ) α
  simp at h
  exact h

/--
[JActsOnForms.J_form_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.J_form_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {Jf : JActsOnForms J}
  {p : ℕ} :
-- imply
  Jf.J_form (0 : Ω p) = 0 := by
-- proof
  have h := Jf.J_form_smul (0 : ℝ) (0 : Ω p)
  simp [zero_smul] at h
  exact h

/--
[JActsOnForms.laplacian_commutes_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.laplacian_commutes_J
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {Jf : JActsOnForms J}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (cod : Codifferential (inst := inst))
  (d_commutes_J : ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α))
  (dstar_commutes_J : ∀ {p : ℕ} (α : Ω (p + 1)), cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α)) :
-- imply
  laplacian cod (Jf.J_form α) = Jf.J_form (laplacian cod α) := by
-- proof
  unfold laplacian
  rw [dstar_commutes_J α, d_commutes_J (cod.dstar α),
    d_commutes_J α, dstar_commutes_J (inst.d α),
    ← Jf.J_form_add]

/--
[kahler_identity_Lstar_dstar_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_identity_Lstar_dstar_commute
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {lef : LefschetzOp S}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω (p + 3)}
-- given
  (cod : Codifferential (inst := inst))
  (dl : DualLefschetz (inst := inst))
  (adjoint_L : ∀ {q : ℕ} (γ : Ω q) (δ : Ω (q + 2)), ip.inner (lef.L_op γ) δ = ip.inner γ (dl.Λ_op δ)) :
-- imply
  dl.Λ_op (cod.dstar α) = cod.dstar (dl.Λ_op α) := by
-- proof
  suffices h : ∀ β : Ω p,
    ip.inner (dl.Λ_op (cod.dstar α)) β = ip.inner (cod.dstar (dl.Λ_op α)) β by
    have hdiff : ∀ β : Ω p,
      ip.inner (dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α)) β = 0 := by
      intro β
      have hsub : dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α) =
        dl.Λ_op (cod.dstar α) + (-1 : ℝ) • cod.dstar (dl.Λ_op α) := by
        simp [sub_eq_add_neg]
      rw [hsub, ip.inner_add_left, ip.inner_smul_left, h β]
      ring
    have hself := hdiff (dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α))
    exact sub_eq_zero.mp (ip.inner_self_eq_zero _ hself)
  intro β
  have adjoint_Lstar : ∀ {q : ℕ} (x : Ω (q + 2)) (y : Ω q),
    ip.inner (dl.Λ_op x) y = ip.inner x (lef.L_op y) := by
    intro q x y
    rw [ip.inner_symm (dl.Λ_op x) y]
    rw [← adjoint_L y x]
    rw [ip.inner_symm]
  calc ip.inner (dl.Λ_op (cod.dstar α)) β
    _ = ip.inner (cod.dstar α) (lef.L_op β) := adjoint_Lstar _ _
    _ = ip.inner (lef.L_op β) (cod.dstar α) := ip.inner_symm _ _
    _ = ip.inner (inst.d (lef.L_op β)) α := by
      exact (ip.adjoint_d (lef.L_op β) α).symm
    _ = ip.inner (lef.L_op (inst.d β)) α := by
      rw [lef.d_commutes β]
    _ = ip.inner (inst.d β) (dl.Λ_op α) := adjoint_L _ _
    _ = ip.inner β (cod.dstar (dl.Λ_op α)) := ip.adjoint_d _ _
    _ = ip.inner (cod.dstar (dl.Λ_op α)) β := ip.inner_symm _ _

/--
[kahler_identities_all_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_identities_all_four
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {Jf : JActsOnForms J}
  {lef : LefschetzOp S}
  {ip : L2InnerProduct cod}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (cod : Codifferential (inst := inst))
  (dl : DualLefschetz (inst := inst))
  (adjoint_L : ∀ {q : ℕ} (γ : Ω q) (δ : Ω (q + 2)), ip.inner (lef.L_op γ) δ = ip.inner γ (dl.Λ_op δ))
  (identity3_L_dstar : ∀ {p : ℕ} (α : Ω (p + 1)), lef.L_op (cod.dstar α) + -(cod.dstar (lef.L_op α)) = d_C_form Jf α)
  (identity4_Λ_d : ∀ {p : ℕ} (α : Ω (p + 2)), dl.Λ_op (inst.d α) + -(inst.d (dl.Λ_op α)) = -(d_C_star_form Jf cod α)) :
-- imply
  (∀ {p : ℕ} (α : Ω p), lef.L_op (inst.d α) = inst.d (lef.L_op α)) ∧ (∀ {p : ℕ} (α : Ω (p + 3)), dl.Λ_op (cod.dstar α) = cod.dstar (dl.Λ_op α)) ∧ (∀ {p : ℕ} (α : Ω (p + 1)), lef.L_op (cod.dstar α) + -(cod.dstar (lef.L_op α)) = d_C_form Jf α) ∧ (∀ {p : ℕ} (α : Ω (p + 2)), dl.Λ_op (inst.d α) + -(inst.d (dl.Λ_op α)) = -(d_C_star_form Jf cod α)) :=
-- proof
  ⟨fun α => lef.d_commutes α,
    fun α => kahler_identity_Lstar_dstar_commute lef cod ip dl adjoint_L α,
    fun α => identity3_L_dstar α,
    fun α => identity4_Λ_d α⟩

/--
[laplacian_J_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma laplacian_J_invariant
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {Jf : JActsOnForms J}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (cod : Codifferential (inst := inst))
  (d_commutes_J : ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α))
  (dstar_commutes_J : ∀ {p : ℕ} (α : Ω (p + 1)), cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α)) :
-- imply
  laplacian cod (Jf.J_form α) = Jf.J_form (laplacian cod α) :=
-- proof
  Jf.laplacian_commutes_J cod d_commutes_J dstar_commutes_J α

/--
[IsCompactOrientedRiemannian.codifferential_from_star](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma IsCompactOrientedRiemannian.codifferential_from_star
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hR : IsCompactOrientedRiemannian Ω VF]
  {p : ℕ}
  {ω : Ω (p + 1)}
-- given
  (h : p + 1 ≤ hR.cod.manifold_dim) :
-- imply
  hR.cod.dstar ω = hR.cod.sign_factor (p + 1) • cast (by congr 1; omega) (hR.cod.star_deg (by omega : hR.cod.manifold_dim - (p + 1) + 1 ≤ hR.cod.manifold_dim) (inst.d (hR.cod.star_deg h ω))) :=
-- proof
  hR.cod.dstar_formula h ω

/--
[IsCompactOrientedRiemannian.l2_inner_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma IsCompactOrientedRiemannian.l2_inner_eq_integral
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hR : IsCompactOrientedRiemannian Ω VF]
  {p : ℕ}
  {α β : Ω p} :
-- imply
  hR.ip.inner α β = hR.integrate (hR.wedge_star p α β) :=
-- proof
  hR.inner_eq_integrate_wedge_star α β

/--
[IsSmoothing.iterate_improvement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma IsSmoothing.iterate_improvement
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [sob : HasSobolevSpaces Ω VF]
  {S : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)}
  [hS : IsSmoothing (inst := inst) S] :
-- imply
  ∀ (n s : ℕ) {p : ℕ} (α : Ω (p + 1)), sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + n) (S^[n] α) := by
-- proof
  intro n
  induction n with
  | zero => intro s p α h; simpa using h
  | succ n ih =>
    intro s p α hs
    rw [Function.iterate_succ', Function.comp]
    have h1 := ih s α hs
    have h2 := hS.sobolev_improvement (s + n) (S^[n] α) h1
    rwa [show s + (n + 1) = s + n + 1 from by omega]

/--
[elliptic_regularity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma elliptic_regularity
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasSobolevSpaces Ω VF]
  {p : ℕ}
  {ξ : Ω (p + 1)}
  {s : ℕ}
-- given
  (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  (param : HasParametrixDFS (inst := inst) L)
  (IsSmoothSection : ∀ {p : ℕ}, Ω (p + 1) → Prop)
  (IsSobolevRegular : ℕ → ∀ {p : ℕ}, Ω (p + 1) → Prop)
  (P_preserves_smooth : ∀ {p : ℕ} (β : Ω (p + 1)), IsSmoothSection β → IsSmoothSection (param.P β))
  (S_left_maps_sobolev_to_smooth : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)), IsSobolevRegular s α → IsSmoothSection (param.S_left α))
  (smooth_sub : ∀ {p : ℕ} (a b : Ω (p + 1)), IsSmoothSection a → IsSmoothSection b → IsSmoothSection (a - b))
  (hξ_sob : IsSobolevRegular s ξ)
  (hLξ_smooth : IsSmoothSection (L ξ)) :
-- imply
  IsSmoothSection ξ := by
-- proof
  have hid := param.PL_eq ξ
  have hP_smooth : IsSmoothSection (param.P (L ξ)) :=
    P_preserves_smooth (L ξ) hLξ_smooth
  have hS_smooth : IsSmoothSection (param.S_left ξ) :=
    S_left_maps_sobolev_to_smooth s ξ hξ_sob
  have h_eq : ξ = param.P (L ξ) - param.S_left ξ := by
    rw [hid]; simp [sub_eq_add_neg, add_assoc, add_neg_cancel]
  rw [h_eq]
  exact smooth_sub _ _ hP_smooth hS_smooth

/--
[L2InnerProduct.inner_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma L2InnerProduct.inner_add_right
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α β γ : Ω p} :
-- imply
  ip.inner α (β + γ) = ip.inner α β + ip.inner α γ := by
-- proof
  rw [ip.inner_symm α (β + γ), ip.inner_add_left, ip.inner_symm β α, ip.inner_symm γ α]

/--
[laplacian_self_adjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma laplacian_self_adjoint
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α β : Ω (p + 1)}
-- given
  (cod : Codifferential (inst := inst)) :
-- imply
  ip.inner (laplacian cod α) β = ip.inner α (laplacian cod β) := by
-- proof
  unfold laplacian
  rw [ip.inner_add_left]
  rw [ip.inner_add_right]
  have h1 : ip.inner (inst.d (cod.dstar α)) β = ip.inner (cod.dstar α) (cod.dstar β) :=
    ip.adjoint_d (cod.dstar α) β
  have h2 : ip.inner α (inst.d (cod.dstar β)) = ip.inner (cod.dstar α) (cod.dstar β) := by
    rw [ip.inner_symm, ip.adjoint_d (cod.dstar β) α, ip.inner_symm]
  have h3 : ip.inner (cod.dstar (inst.d α)) β = ip.inner (inst.d α) (inst.d β) := by
    rw [ip.inner_symm (cod.dstar (inst.d α)) β]
    rw [← ip.adjoint_d β (inst.d α), ip.inner_symm (inst.d β) (inst.d α)]
  have h4 : ip.inner α (cod.dstar (inst.d β)) = ip.inner (inst.d α) (inst.d β) :=
    (ip.adjoint_d α (inst.d β)).symm
  linarith

/--
[green_operator_image_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma green_operator_image_orthogonal
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactOrientedRiemannian Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (gd : @HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α)) :
-- imply
  (∃ β, gd.G (laplacian cod β) = α) ↔ (∀ h : Ω (p + 1), IsHarmonic cod h → ip.inner h α = 0) := by
-- proof
  constructor
  ·
    rintro ⟨β, hβ⟩ h hh
    have hGL : gd.G (laplacian cod β) = β + -(gd.H β) := gd.GL_eq β
    have hLG : laplacian cod (gd.G β) = β + -(gd.H β) := gd.LG_eq β
    have hα_eq : α = laplacian cod (gd.G β) := by
      have : α = β + -(gd.H β) := by rw [← hGL, hβ]
      rw [this, ← hLG]
    rw [hα_eq, ip.inner_symm, laplacian_self_adjoint cod ip (gd.G β) h]
    rw [show laplacian cod h = 0 from hh]
    rw [ip.inner_symm]; exact ip.inner_zero_left (gd.G β)
  ·
    intro horth
    use α
    have hGL : gd.G (laplacian cod α) = α + -(gd.H α) := gd.GL_eq α
    suffices hH0 : gd.H α = 0 by rw [hGL, hH0, neg_zero, add_zero]
    have hH_harm : IsHarmonic cod (gd.H α) := gd.H_maps_to_ker α
    have horth_Hα : ip.inner (gd.H α) α = 0 := horth (gd.H α) hH_harm
    have hLG : laplacian cod (gd.G α) = α + -(gd.H α) := gd.LG_eq α
    have hα_decomp : α = gd.H α + laplacian cod (gd.G α) := by
      have : gd.H α + laplacian cod (gd.G α) = gd.H α + (α + -(gd.H α)) := by
        rw [hLG]
      rw [this]; abel
    have horth_decomp : ip.inner (gd.H α) (laplacian cod (gd.G α)) = 0 :=
      gd.orth_decomp cod ip α
    have hHα_self : ip.inner (gd.H α) (gd.H α) = 0 := by
      have expand : ip.inner (gd.H α) α =
        ip.inner (gd.H α) (gd.H α) + ip.inner (gd.H α) (laplacian cod (gd.G α)) := by
        have h_eq : ip.inner (gd.H α) α =
          ip.inner (gd.H α) (gd.H α + laplacian cod (gd.G α)) := by
          congr 1
        rw [h_eq, ip.inner_add_right]
      linarith
    exact ip.inner_self_eq_zero (gd.H α) hHα_self

/--
[hodge_decomposition_three_way](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_decomposition_three_way
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactOrientedRiemannian Ω VF]
  {cod : @Codifferential Ω VF inst}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (h_green : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α))) :
-- imply
  ∃ (h : Ω (p + 1)) (β : Ω p) (γ : Ω (p + 2)), IsHarmonic cod h ∧ α = h + inst.d β + cod.dstar γ := by
-- proof
  obtain ⟨gd⟩ := h_green
  refine ⟨gd.H α, cod.dstar (gd.G α), inst.d (gd.G α), ?_, ?_⟩
  ·
    exact gd.H_maps_to_ker α
  ·
    have hLG := gd.LG_eq α
    show α = gd.H α + inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α))
    have hLG' : inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α)) = α + -gd.H α := hLG
    have step : gd.H α + (inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α))) = α := by
      rw [hLG']; abel
    rwa [← add_assoc] at step

/--
[orthog_harmonic_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma orthog_harmonic_exact
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {β : Ω p}
-- given
  (h : Ω (p + 1))
  (hh : IsHarmonic cod h) :
-- imply
  ip.inner h (inst.d β) = 0 := by
-- proof
  rw [ip.inner_symm]
  rw [ip.adjoint_d]
  rw [(harmonic_iff_closed_coclosed cod ip h).mp hh |>.2]
  rw [ip.inner_symm]
  exact ip.inner_zero_left β

/--
[orthog_harmonic_coexact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma orthog_harmonic_coexact
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {γ : Ω (p + 2)}
-- given
  (h : Ω (p + 1))
  (hh : IsHarmonic cod h) :
-- imply
  ip.inner h (cod.dstar γ) = 0 := by
-- proof
  rw [← ip.adjoint_d]
  rw [(harmonic_iff_closed_coclosed cod ip h).mp hh |>.1]
  exact ip.inner_zero_left γ

/--
[orthog_exact_coexact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma orthog_exact_coexact
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {β : Ω p}
  {γ : Ω (p + 2)} :
-- imply
  ip.inner (inst.d β) (cod.dstar γ) = 0 := by
-- proof
  rw [← ip.adjoint_d]
  rw [inst.d_squared]
  exact ip.inner_zero_left γ

/--
[hodge_decomposition_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_decomposition_orthogonal
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactOrientedRiemannian Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  [h_green : HasLaplacianGreenDecomp cod]
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  (∃ (h : Ω (p + 1)) (β : Ω p) (γ : Ω (p + 2)), IsHarmonic cod h ∧ α = h + inst.d β + cod.dstar γ ∧ ip.inner h (inst.d β) = 0 ∧ ip.inner h (cod.dstar γ) = 0 ∧ ip.inner (inst.d β) (cod.dstar γ) = 0) ∧ (∀ (h₁ h₂ : Ω (p + 1)) (β₁ β₂ : Ω p) (γ₁ γ₂ : Ω (p + 2)), IsHarmonic cod h₁ → IsHarmonic cod h₂ → α = h₁ + inst.d β₁ + cod.dstar γ₁ → α = h₂ + inst.d β₂ + cod.dstar γ₂ → h₁ = h₂) := by
-- proof
  constructor
  ·
    obtain ⟨h, β, γ, hh, hdecomp⟩ := hodge_decomposition_three_way cod h_green.green_decomp α
    exact ⟨h, β, γ, hh, hdecomp,
      orthog_harmonic_exact cod ip h hh β,
      orthog_harmonic_coexact cod ip h hh γ,
      orthog_exact_coexact cod ip β γ⟩
  ·
    intro h₁ h₂ β₁ β₂ γ₁ γ₂ hHarm₁ hHarm₂ hdecomp₁ hdecomp₂
    have dstar_neg_local : ∀ {q : ℕ} (ω : Ω (q + 1)),
      cod.dstar (-ω) = -cod.dstar ω := by
      intro q ω; have := cod.dstar_smul (-1 : ℝ) ω; simp at this; exact this
    have hdiff : h₁ - h₂ = inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁) := by
      have heq : h₁ + inst.d β₁ + cod.dstar γ₁ = h₂ + inst.d β₂ + cod.dstar γ₂ :=
        hdecomp₁.symm.trans hdecomp₂
      have hd_sub : inst.d (β₂ - β₁) = inst.d β₂ - inst.d β₁ := by
        rw [show β₂ - β₁ = β₂ + (-β₁) from sub_eq_add_neg β₂ β₁, inst.d_add, d_neg]; abel
      have hds_sub : cod.dstar (γ₂ - γ₁) = cod.dstar γ₂ - cod.dstar γ₁ := by
        rw [show γ₂ - γ₁ = γ₂ + (-γ₁) from sub_eq_add_neg γ₂ γ₁,
          cod.dstar_add, dstar_neg_local]; abel
      rw [hd_sub, hds_sub]
      have h1 : h₁ = α - inst.d β₁ - cod.dstar γ₁ := by rw [hdecomp₁]; abel
      have h2 : h₂ = α - inst.d β₂ - cod.dstar γ₂ := by rw [hdecomp₂]; abel
      rw [h1, h2]; abel
    have hHarm_diff : IsHarmonic cod (h₁ - h₂) := by
      unfold IsHarmonic laplacian
      rw [show h₁ - h₂ = h₁ + (-h₂) from sub_eq_add_neg h₁ h₂]
      rw [cod.dstar_add, inst.d_add, inst.d_add, cod.dstar_add]
      rw [d_neg, dstar_neg_local, d_neg, dstar_neg_local]
      have hΔ₁ : inst.d (cod.dstar h₁) + cod.dstar (inst.d h₁) = 0 := hHarm₁
      have hΔ₂ : inst.d (cod.dstar h₂) + cod.dstar (inst.d h₂) = 0 := hHarm₂
      have h1a : inst.d (cod.dstar h₁) = -(cod.dstar (inst.d h₁)) :=
        eq_neg_of_add_eq_zero_left hΔ₁
      have h2a : inst.d (cod.dstar h₂) = -(cod.dstar (inst.d h₂)) :=
        eq_neg_of_add_eq_zero_left hΔ₂
      rw [h1a, h2a]; abel
    have inner_zero : ip.inner (h₁ - h₂) (h₁ - h₂) = 0 := by
      have hrw : ip.inner (h₁ - h₂) (h₁ - h₂) =
        ip.inner (h₁ - h₂) (inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁)) := by
        rw [show (h₁ - h₂ : Ω (p + 1)) = inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁) from hdiff]
      rw [hrw]
      rw [ip.inner_symm (h₁ - h₂) (inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁)),
        ip.inner_add_left,
        ip.inner_symm (inst.d (β₂ - β₁)), ip.inner_symm (cod.dstar (γ₂ - γ₁))]
      have h_exact : ip.inner (h₁ - h₂) (inst.d (β₂ - β₁)) = 0 :=
        orthog_harmonic_exact cod ip (h₁ - h₂) hHarm_diff (β₂ - β₁)
      have h_coexact : ip.inner (h₁ - h₂) (cod.dstar (γ₂ - γ₁)) = 0 :=
        orthog_harmonic_coexact cod ip (h₁ - h₂) hHarm_diff (γ₂ - γ₁)
      linarith
    exact sub_eq_zero.mp (ip.inner_self_eq_zero _ inner_zero)

/--
[hodge_representative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_representative
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactOrientedRiemannian Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (h_green : Nonempty (HasGreenOperatorDecomp (inst := inst) (fun α => laplacian cod α)))
  (hclosed : inst.d α = 0) :
-- imply
  ∃ (h : Ω (p + 1)) (β : Ω p), IsHarmonic cod h ∧ α = h + inst.d β := by
-- proof
  obtain ⟨h, β, γ, hHarm, hDecomp⟩ := hodge_decomposition_three_way cod h_green α
  have hclosed_h : inst.d h = 0 :=
    ((harmonic_iff_closed_coclosed cod ip h).mp hHarm).1
  have hd_dstar_gamma : inst.d (cod.dstar γ) = 0 := by
    have := congr_arg inst.d hDecomp
    rw [inst.d_add, inst.d_add, hclosed, hclosed_h, inst.d_squared] at this
    simp only [zero_add, add_zero] at this
    exact this.symm
  have adj : ip.inner (inst.d (cod.dstar γ)) γ =
    ip.inner (cod.dstar γ) (cod.dstar γ) :=
    ip.adjoint_d (cod.dstar γ) γ
  have inner_zero : ip.inner (cod.dstar γ) (cod.dstar γ) = 0 := by
    rw [← adj, hd_dstar_gamma]; exact ip.inner_zero_left γ
  have hvanish : cod.dstar γ = 0 := ip.inner_self_eq_zero _ inner_zero
  exact ⟨h, β, hHarm, by rw [hDecomp, hvanish, add_zero]⟩

/--
[harmonic_exact_is_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma harmonic_exact_is_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {γ : Ω p}
-- given
  (h : Ω (p + 1))
  (hHarm : IsHarmonic cod h)
  (hExact : h = inst.d γ) :
-- imply
  h = 0 := by
-- proof
  have hcoclosed : cod.dstar h = 0 :=
    ((harmonic_iff_closed_coclosed cod ip h).mp hHarm).2
  have inner_hh : ip.inner h h = 0 := by
    have : ip.inner h h = ip.inner (inst.d γ) h := by rw [hExact]
    rw [this, ip.adjoint_d γ h, hcoclosed]
    rw [ip.inner_symm γ (0 : Ω p)]
    exact ip.inner_zero_left γ
  exact ip.inner_self_eq_zero h inner_hh

/--
[Codifferential.dstar_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma Codifferential.dstar_neg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  cod.dstar (-α) = -cod.dstar α := by
-- proof
  have := cod.dstar_smul (-1 : ℝ) α; simp at this; exact this

/--
[laplacian_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma laplacian_sub
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {p : ℕ}
  {α β : Ω (p + 1)} :
-- imply
  laplacian cod (α - β) = laplacian cod α - laplacian cod β := by
-- proof
  unfold laplacian
  rw [show α - β = α + (-β) from sub_eq_add_neg α β]
  rw [cod.dstar_add, inst.d_add, inst.d_add, cod.dstar_add]
  rw [d_neg, cod.dstar_neg, d_neg, cod.dstar_neg]
  abel

/--
[hodge_representative_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_representative_unique
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {γ : Ω p}
-- given
  (h₁ h₂ : Ω (p + 1))
  (hHarm₁ : IsHarmonic cod h₁)
  (hHarm₂ : IsHarmonic cod h₂)
  (hDiff : h₁ - h₂ = inst.d γ) :
-- imply
  h₁ = h₂ := by
-- proof
  have hHarm_diff : IsHarmonic cod (h₁ - h₂) := by
    unfold IsHarmonic
    rw [laplacian_sub]
    rw [show laplacian cod h₁ = 0 from hHarm₁, show laplacian cod h₂ = 0 from hHarm₂]
    simp
  have hzero : h₁ - h₂ = 0 := harmonic_exact_is_zero cod ip (h₁ - h₂) hHarm_diff γ hDiff
  exact sub_eq_zero.mp hzero

/--
[d_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma d_sub
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α β : Ω p} :
-- imply
  inst.d (α - β) = inst.d α - inst.d β := by
-- proof
  rw [show α - β = α + (-β) from sub_eq_add_neg α β, inst.d_add, d_neg]
  abel

/--
[hodge_representative_exists_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_representative_exists_unique
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hR : IsCompactOrientedRiemannian Ω VF]
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (h_green : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian hR.cod α)))
  (hclosed : inst.d α = 0) :
-- imply
  ∃! (h : Ω (p + 1)), IsHarmonic hR.cod h ∧ ∃ (β : Ω p), α = h + inst.d β := by
-- proof
  let cod := hR.cod
  let ip := hR.ip
  obtain ⟨h, β, hHarm, hDecomp⟩ := hodge_representative cod ip h_green α hclosed
  refine ⟨h, ⟨hHarm, β, hDecomp⟩, ?_⟩
  intro h' ⟨hHarm', β', hDecomp'⟩
  have hdiff : h - h' = inst.d (β' - β) := by
    have heq : h + inst.d β = h' + inst.d β' := hDecomp.symm.trans hDecomp'
    rw [d_sub]
    have step : h = h' + inst.d β' + -(inst.d β) := by
      calc h = (h + inst.d β) + -(inst.d β) := by abel
        _ = (h' + inst.d β') + -(inst.d β) := by rw [heq]
    calc h - h' = (h' + inst.d β' + -(inst.d β)) - h' := by rw [step]
      _ = inst.d β' - inst.d β := by abel
  exact (hodge_representative_unique cod ip h h' hHarm hHarm' (β' - β) hdiff).symm

/--
[kahler_hodge_decomposition_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_hodge_decomposition_cohomology
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {ip : L2InnerProduct cod}
  {n : ℕ}
  {bg : HasBigrading J n}
  {dol_lap : DolbeaultLaplacian dol cod}
  {k : ℕ}
  {α₁ α₂ : Ω (k + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (cod : Codifferential (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (h_harmonic_bigrading : ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0), ∃ (component : Fin (k + 2) → Ω (k + 1)), (∀ (j : Fin (k + 2)), ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)), cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt))) (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧ (∀ j, dol.del (component j) = 0) ∧ (∀ j, dol.delbar (component j) = 0) ∧ (∀ j, laplacian cod (component j) = 0) ∧ h_form = Finset.univ.sum component)
  (h_hodge_rep : ∀ {p : ℕ} (α' : Ω (p + 1)), inst.d α' = 0 → ∃ (h : Ω (p + 1)) (β : Ω p), laplacian cod h = 0 ∧ α' = h + inst.d β)
  (h_dolbeault_id : ∀ {k' : ℕ} (α' : Ω (k' + 1)), laplacian cod α' = 0 ↔ dol_lap.box_bar α' = 0)
  (hclosed₁ : inst.d α₁ = 0)
  (hclosed₂ : inst.d α₂ = 0)
  (hcohom : IsDRCohomologous (inst := inst) (k := k) α₁ α₂) :
-- imply
  (∀ (h₁ h₂ : Ω (k + 1)) (β₁ β₂ : Ω k), IsHarmonic cod h₁ → α₁ = h₁ + inst.d β₁ → IsHarmonic cod h₂ → α₂ = h₂ + inst.d β₂ → h₁ = h₂) ∧ (∃ (component : Fin (k + 2) → Ω (k + 1)) (β : Ω k), (∀ (j : Fin (k + 2)), ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)), cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt))) (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧ (∀ j, dol.del (component j) = 0) ∧ (∀ j, dol.delbar (component j) = 0) ∧ (∀ j, laplacian cod (component j) = 0) ∧ (∀ j, dol_lap.box_bar (component j) = 0) ∧ (α₁ = (Finset.univ.sum component) + inst.d β) ∧ (∃ (β' : Ω k), α₂ = (Finset.univ.sum component) + inst.d β')) := by
-- proof
  obtain ⟨γ, hγ⟩ := hcohom
  constructor
  · intro h₁ h₂ β₁ β₂ hHarm₁ hDecomp₁ hHarm₂ hDecomp₂
    have hdiff : h₁ - h₂ = inst.d (γ - β₁ + β₂) := by
      have h₁_eq : h₁ = α₁ - inst.d β₁ := by rw [hDecomp₁]; abel
      have h₂_eq : h₂ = α₂ - inst.d β₂ := by rw [hDecomp₂]; abel
      rw [h₁_eq, h₂_eq]
      rw [show α₁ - inst.d β₁ - (α₂ - inst.d β₂) = (α₁ - α₂) - (inst.d β₁ - inst.d β₂)
        from by abel]
      rw [hγ, ← d_sub, show inst.d γ - inst.d (β₁ - β₂) = inst.d (γ - (β₁ - β₂))
        from (d_sub γ (β₁ - β₂)).symm]
      congr 1; abel
    exact hodge_representative_unique cod ip h₁ h₂ hHarm₁ hHarm₂ (γ - β₁ + β₂) hdiff
  ·
    obtain ⟨h₁, β₁, hHarm₁, hDecomp₁⟩ := h_hodge_rep α₁ hclosed₁
    obtain ⟨h₂, β₂, hHarm₂, hDecomp₂⟩ := h_hodge_rep α₂ hclosed₂
    have heq_harm : h₁ = h₂ := by
      have hdiff : h₁ - h₂ = inst.d (γ - β₁ + β₂) := by
        have h₁_eq : h₁ = α₁ - inst.d β₁ := by rw [hDecomp₁]; abel
        have h₂_eq : h₂ = α₂ - inst.d β₂ := by rw [hDecomp₂]; abel
        rw [h₁_eq, h₂_eq]
        rw [show α₁ - inst.d β₁ - (α₂ - inst.d β₂) = (α₁ - α₂) - (inst.d β₁ - inst.d β₂)
          from by abel]
        rw [hγ, ← d_sub, show inst.d γ - inst.d (β₁ - β₂) = inst.d (γ - (β₁ - β₂))
          from (d_sub γ (β₁ - β₂)).symm]
        congr 1; abel
      exact hodge_representative_unique cod ip h₁ h₂ hHarm₁ hHarm₂ (γ - β₁ + β₂) hdiff
    obtain ⟨component, h_bideg, h_del, h_delbar, h_laplacian, h_sum⟩ :=
      h_harmonic_bigrading h₁ hHarm₁
    have h_box_bar : ∀ j, dol_lap.box_bar (component j) = 0 := by
      intro j
      exact (h_dolbeault_id (component j)).mp (h_laplacian j)
    have hDecomp₂' : α₂ = Finset.univ.sum component + inst.d β₂ := by
      rw [← heq_harm] at hDecomp₂
      rw [hDecomp₂, h_sum]
    exact ⟨component, β₁,
      h_bideg, h_del, h_delbar, h_laplacian, h_box_bar,
      by rw [hDecomp₁, h_sum],
      β₂, hDecomp₂'⟩
set_option maxHeartbeats 400000 in

/--
[corollary4_kahler_hodge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma corollary4_kahler_hodge
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {cod : @Codifferential Ω VF inst}
  {ip : L2InnerProduct cod}
  {n : ℕ}
  {bg : HasBigrading J n}
  {dol_lap : DolbeaultLaplacian dol cod}
  {wells : KahlerWellsIdentities S J hK dol_lap}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (dol : DolbeaultOps (inst := inst))
  (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'), ∃ ω' : bg.Ω_pq p' q', cast (congrArg Ω h) (bg.incl p' q' ω') = dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))
  (h_harmonic_bigrading : ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0), ∃ (component : Fin (k + 2) → Ω (k + 1)), (∀ (j : Fin (k + 2)), ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)), cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt))) (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧ (∀ j, dol.del (component j) = 0) ∧ (∀ j, dol.delbar (component j) = 0) ∧ (∀ j, laplacian cod (component j) = 0) ∧ h_form = Finset.univ.sum component)
  (_hC : @HasComplexStructure Ω VF inst)
  (h_hodge_rep : ∀ {p : ℕ} (α' : Ω (p + 1)), inst.d α' = 0 → ∃ (h : Ω (p + 1)) (β : Ω p), laplacian cod h = 0 ∧ α' = h + inst.d β) :
-- imply
  (∀ (k : ℕ) (p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'), ∃ ω' : bg.Ω_pq p' q', cast (congrArg Ω h) (bg.incl p' q' ω') = laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω))) ∧ (∀ {k : ℕ} (α₁ α₂ : Ω (k + 1)) (hclosed₁ : inst.d α₁ = 0) (hclosed₂ : inst.d α₂ = 0) (hcohom : IsDRCohomologous (inst := inst) (k := k) α₁ α₂), (∀ (h₁ h₂ : Ω (k + 1)) (β₁ β₂ : Ω k), IsHarmonic cod h₁ → α₁ = h₁ + inst.d β₁ → IsHarmonic cod h₂ → α₂ = h₂ + inst.d β₂ → h₁ = h₂) ∧ (∃ (component : Fin (k + 2) → Ω (k + 1)) (β : Ω k), (∀ (j : Fin (k + 2)), ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)), cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt))) (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧ (∀ j, dol.del (component j) = 0) ∧ (∀ j, dol.delbar (component j) = 0) ∧ (∀ j, laplacian cod (component j) = 0) ∧ (∀ j, dol_lap.box_bar (component j) = 0) ∧ (α₁ = (Finset.univ.sum component) + inst.d β) ∧ (∃ (β' : Ω k), α₂ = (Finset.univ.sum component) + inst.d β'))) := by
-- proof
  have h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    fun α => kahler_two_box_bar_blocker S J hK dol_lap wells α
  have h_dolbeault_id : ∀ {k' : ℕ} (α' : Ω (k' + 1)),
    laplacian cod α' = 0 ↔ dol_lap.box_bar α' = 0 :=
    fun α' => dolbeault_identification S J hK cod dol dol_lap h_two_box_bar α'
  constructor
  · exact fun k p' q' h ω =>
    laplacian_preserves_bidegree S J hK cod dol dol_lap bg h_box_bar_pres
      (h_two_box_bar := h_two_box_bar) k p' q' h ω
  · intro k α₁ α₂ hclosed₁ hclosed₂ hcohom
    exact kahler_hodge_decomposition_cohomology S J hK cod ip dol bg dol_lap
      h_harmonic_bigrading h_hodge_rep h_dolbeault_id α₁ α₂ hclosed₁ hclosed₂ hcohom

/--
[HasBigrading.star_bigraded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma HasBigrading.star_bigraded
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {n : ℕ}
  {bg : HasBigrading J n}
  {p q : ℕ}
  {β : bg.Ω_pq p q}
-- given
  (hp : p ≤ n)
  (hq : q ≤ n) :
-- imply
  ∃ γ : bg.Ω_pq (n - q) (n - p), bg.incl (n - q) (n - p) γ = cast (congrArg Ω (by omega)) (bg.star_total (by omega : p + q ≤ 2 * n) (bg.incl p q β)) := by
-- proof
  obtain ⟨a, b, c, ha, hb, habc, γ, hγ⟩ := bg.star_abc_decomp hp hq β
  have h_nq : a + (n - a - b - c) = n - q := by omega
  have h_np : b + (n - a - b - c) = n - p := by omega
  exact ⟨cast (by rw [h_nq, h_np]) γ, by
    rw [bg.incl_cast h_nq h_np γ, hγ, cast_cast]⟩

/--
[HasBigrading.star_pq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma HasBigrading.star_pq_spec
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {n : ℕ}
  {bg : HasBigrading J n}
  {p q : ℕ}
  {β : bg.Ω_pq p q}
-- given
  (hp : p ≤ n)
  (hq : q ≤ n) :
-- imply
  bg.incl (n - q) (n - p) (bg.star_pq hp hq β) = cast (congrArg Ω (by omega)) (bg.star_total (by omega : p + q ≤ 2 * n) (bg.incl p q β)) :=
-- proof
  (bg.star_bigraded hp hq β).choose_spec

/--
[hodge_star_pq_type](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma hodge_star_pq_type
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {n : ℕ}
  {bg : HasBigrading J n}
  {p q : ℕ}
  {α : Ω (p + q)}
-- given
  (hp : p ≤ n)
  (hq : q ≤ n)
  (hα : bg.is_pq_form p q α) :
-- imply
  bg.is_pq_form (n - q) (n - p) (cast (congrArg Ω (by omega)) (bg.star_total (by omega : p + q ≤ 2 * n) α)) := by
-- proof
  obtain ⟨β, hβ⟩ := hα
  obtain ⟨γ, hγ⟩ := bg.star_bigraded hp hq β
  exact ⟨γ, by subst hβ; exact hγ⟩

/--
[delbar_adjoint_from_stokes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma delbar_adjoint_from_stokes
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dbs : DelbarStar dol}
  {cip : ComplexL2InnerProduct cod dol dbs}
  {p : ℕ}
  {α : Ω p}
  {β : Ω (p + 1)}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  cip.inner (dol.delbar α) β = cip.inner α (dbs.delbar_star β) := by
-- proof
  rw [cip.stokes_delbar_leibniz α β]
  exact cip.h_delbar_star_sign α β

/--
[delbar_star_L2_adjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma delbar_star_L2_adjoint
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dbs : DelbarStar dol}
  {cip : ComplexL2InnerProduct cod dol dbs}
  {p : ℕ}
  {α : Ω p}
  {β : Ω (p + 1)}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  cip.inner (dol.delbar α) β = cip.inner α (dbs.delbar_star β) :=
-- proof
  delbar_adjoint_from_stokes cod dol dbs cip α β

/--
[del_adjoint_from_stokes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma del_adjoint_from_stokes
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ds : DelStar dol}
  {cip : ComplexL2InnerProductDel cod dol ds}
  {p : ℕ}
  {α : Ω p}
  {β : Ω (p + 1)}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  cip.inner (dol.del α) β = cip.inner α (ds.del_star β) := by
-- proof
  rw [cip.stokes_del_leibniz α β]
  exact cip.h_del_star_sign α β

/--
[del_star_L2_adjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma del_star_L2_adjoint
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {cod : @Codifferential Ω VF inst}
  {ds : DelStar dol}
  {cip : ComplexL2InnerProductDel cod dol ds}
  {p : ℕ}
  {α : Ω p}
  {β : Ω (p + 1)}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  cip.inner (dol.del α) β = cip.inner α (ds.del_star β) :=
-- proof
  del_adjoint_from_stokes cod dol ds cip α β

/--
[lemma2_L2_adjointness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma lemma2_L2_adjointness
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dbs : DelbarStar dol}
  {ds : DelStar dol}
  {cip_delbar : ComplexL2InnerProduct cod dol dbs}
  {cip_del : ComplexL2InnerProductDel cod dol ds}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  (∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), cip_delbar.inner (dol.delbar α) β = cip_delbar.inner α (dbs.delbar_star β)) ∧ (∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), cip_del.inner (dol.del α) β = cip_del.inner α (ds.del_star β)) :=
-- proof
  ⟨fun α β => delbar_star_L2_adjoint cod dol dbs cip_delbar α β,
    fun α β => del_star_L2_adjoint cod dol ds cip_del α β⟩

/--
[box_bar_harmonic_implies_delbar_closed_coclosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma box_bar_harmonic_implies_delbar_closed_coclosed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (dol : DolbeaultOps (inst := inst))
  (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
  (hBox : dol_lap.box_bar α = 0) :
-- imply
  dol.delbar α = 0 ∧ dol_lap.delbar_star α = 0 := by
-- proof
  have eq1 : ip.inner (dol.delbar (dol_lap.delbar_star α)) α =
    ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) :=
    h_adj_delbar (dol_lap.delbar_star α) α
  have eq2 : ip.inner (dol_lap.delbar_star (dol.delbar α)) α =
    ip.inner (dol.delbar α) (dol.delbar α) := by
    rw [ip.inner_symm (dol_lap.delbar_star (dol.delbar α)) α,
      h_adj_delbar α (dol.delbar α), ip.inner_symm]
  have sum_eq : ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) +
    ip.inner (dol.delbar α) (dol.delbar α) = 0 := by
    have step : ip.inner (dol.delbar (dol_lap.delbar_star α) +
      dol_lap.delbar_star (dol.delbar α)) α =
      ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) +
      ip.inner (dol.delbar α) (dol.delbar α) := by
      rw [ip.inner_add_left, eq1, eq2]
    have hbox_def : dol.delbar (dol_lap.delbar_star α) +
      dol_lap.delbar_star (dol.delbar α) = dol_lap.box_bar α := rfl
    rw [hbox_def, hBox, ip.inner_zero_left] at step
    linarith
  have h_delbar_star : ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) = 0 := by
    linarith [ip.inner_self_nonneg (dol_lap.delbar_star α),
      ip.inner_self_nonneg (dol.delbar α)]
  have h_delbar : ip.inner (dol.delbar α) (dol.delbar α) = 0 := by linarith
  exact ⟨ip.inner_self_eq_zero _ h_delbar, ip.inner_self_eq_zero _ h_delbar_star⟩

/--
[box_bar_harmonic_delbar_exact_is_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma box_bar_harmonic_delbar_exact_is_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {ip : L2InnerProduct cod}
  {p : ℕ}
  {γ : Ω p}
-- given
  (dol : DolbeaultOps (inst := inst))
  (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
  (h : Ω (p + 1))
  (hBox : dol_lap.box_bar h = 0)
  (hExact : h = dol.delbar γ) :
-- imply
  h = 0 := by
-- proof
  have hcoclosed : dol_lap.delbar_star h = 0 :=
    (box_bar_harmonic_implies_delbar_closed_coclosed cod dol dol_lap ip h_adj_delbar h hBox).2
  have inner_hh : ip.inner h h = 0 := by
    have : ip.inner h h = ip.inner (dol.delbar γ) h := by rw [hExact]
    rw [this, h_adj_delbar γ h, hcoclosed]
    rw [ip.inner_symm γ (0 : Ω p)]
    exact ip.inner_zero_left γ
  exact ip.inner_self_eq_zero h inner_hh

/--
[delbar_star_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma delbar_star_neg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dol : DolbeaultOps (inst := inst)}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  dol_lap.delbar_star (-α) = -dol_lap.delbar_star α := by
-- proof
  have := dol_lap.delbar_star_smul (-1 : ℝ) α; simp at this; exact this

/--
[delbar_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma delbar_neg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω p}
-- given
  (dol : DolbeaultOps (inst := inst)) :
-- imply
  dol.delbar (-α) = -dol.delbar α := by
-- proof
  have := dol.delbar_smul (-1 : ℝ) α; simp at this; exact this

/--
[box_bar_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma box_bar_sub
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dol : DolbeaultOps (inst := inst)}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α β : Ω (p + 1)} :
-- imply
  dol_lap.box_bar (α - β) = dol_lap.box_bar α - dol_lap.box_bar β := by
-- proof
  unfold DolbeaultLaplacian.box_bar
  rw [show α - β = α + (-β) from sub_eq_add_neg α β]
  rw [dol_lap.delbar_star_add, dol.delbar_add, dol.delbar_add, dol_lap.delbar_star_add]
  rw [delbar_neg, delbar_star_neg dol_lap,
    delbar_neg, delbar_star_neg dol_lap]
  abel

/--
[box_bar_harmonic_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma box_bar_harmonic_unique
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {ip : L2InnerProduct cod}
  {p' : ℕ}
  {a b : Ω p'}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (dol : DolbeaultOps (inst := inst))
  (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
  (h₁ h₂ : Ω (p' + 1))
  (hHarm₁ : dol_lap.box_bar h₁ = 0)
  (hHarm₂ : dol_lap.box_bar h₂ = 0)
  (hcohom : h₁ + dol.delbar a = h₂ + dol.delbar b) :
-- imply
  h₁ = h₂ := by
-- proof
  have hExact : h₁ - h₂ = dol.delbar (b - a) := by
    have hsub : h₁ - h₂ = dol.delbar b - dol.delbar a := by
      have : h₁ = h₂ + dol.delbar b - dol.delbar a := by rw [← hcohom]; abel
      rw [this]; abel
    rw [hsub]
    rw [show b - a = b + (-a) from sub_eq_add_neg b a, dol.delbar_add, delbar_neg]
    abel
  have hHarm_diff : dol_lap.box_bar (h₁ - h₂) = 0 := by
    rw [box_bar_sub dol_lap]
    rw [hHarm₁, hHarm₂]
    simp
  have hzero : h₁ - h₂ = 0 :=
    box_bar_harmonic_delbar_exact_is_zero cod dol dol_lap ip h_adj_delbar
      (h₁ - h₂) hHarm_diff (b - a) hExact
  exact sub_eq_zero.mp hzero

/--
[harmonic_is_delbar_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma harmonic_is_delbar_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {ip : L2InnerProduct cod}
  {p' : ℕ}
-- given
  (dol : DolbeaultOps (inst := inst))
  (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)), ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
  (h : Ω (p' + 1))
  (hBox : dol_lap.box_bar h = 0) :
-- imply
  dol.delbar h = 0 :=
-- proof
  (box_bar_harmonic_implies_delbar_closed_coclosed cod dol dol_lap ip h_adj_delbar h hBox).1

/--
[JActsOnForms.d_C_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.d_C_sq_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {Jf : JActsOnForms J}
  {p : ℕ}
  {α : Ω p} :
-- imply
  Jf.d_C (Jf.d_C α) = 0 := by
-- proof
  unfold JActsOnForms.d_C
  rw [Jf.J_form_neg]
  rw [Jf.J_form_sq]
  rw [neg_neg]
  rw [inst.d_squared]
  rwa [Jf.J_form_zero]

/--
[kahler_d_commutes_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_d_commutes_J
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {Jf : JActsOnForms J}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap) :
-- imply
  ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α) := by
-- proof
  intro p α
  rw [dol.decomp (Jf.J_form α), hJD.J_commutes_del, hJD.J_commutes_delbar,
    ← Jf.J_form_add, ← dol.decomp]

/--
[kahler_dstar_commutes_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma kahler_dstar_commutes_J
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {Jf : JActsOnForms J}
  {cod : @Codifferential Ω VF inst}
  {dol : DolbeaultOps (inst := inst)}
  {dol_lap : DolbeaultLaplacian dol cod}
-- given
  (J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler S J)
  (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap) :
-- imply
  ∀ {p : ℕ} (α : Ω (p + 1)), cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α) := by
-- proof
  intro p α
  rw [dol_lap.dstar_decomp (Jf.J_form α), hJD.J_commutes_del_star,
    hJD.J_commutes_delbar_star, ← Jf.J_form_add, ← dol_lap.dstar_decomp]

/--
[JActsOnForms.laplacian_C_eq_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.laplacian_C_eq_laplacian
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [IsCompactSymplectic Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {Jf : JActsOnForms J}
  {cod : @Codifferential Ω VF inst}
  {dol : DolbeaultOps (inst := inst)}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (J : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J)
  (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap) :
-- imply
  Jf.laplacian_C cod α = laplacian cod α := by
-- proof
  unfold JActsOnForms.laplacian_C
  rw [laplacian_J_invariant S J hK Jf cod
    (kahler_d_commutes_J S J hK Jf hJD)
    (kahler_dstar_commutes_J S J hK Jf cod hJD) α]
  rw [Jf.J_form_sq]
  exact neg_neg _

/--
[JActsOnForms.laplacian_C_eq_dC_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
lemma JActsOnForms.laplacian_C_eq_dC_decomp
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {J : AlmostComplexStr (inst := inst)}
  {Jf : JActsOnForms J}
  {cod : @Codifferential Ω VF inst}
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  Jf.laplacian_C cod α = Jf.d_C (Jf.d_C_star cod α) + Jf.d_C_star cod (Jf.d_C α) := by
-- proof
  unfold JActsOnForms.laplacian_C laplacian JActsOnForms.d_C_star JActsOnForms.d_C
  conv_rhs => rw [show Jf.J_form (-(Jf.J_form (cod.dstar (Jf.J_form α))))
    = cod.dstar (Jf.J_form α) from by rw [Jf.J_form_neg, Jf.J_form_sq, neg_neg]]
  conv_rhs => rw [show Jf.J_form (-(Jf.J_form (inst.d (Jf.J_form α))))
    = inst.d (Jf.J_form α) from by rw [Jf.J_form_neg, Jf.J_form_sq, neg_neg]]
  rw [← neg_add]
  rw [← Jf.J_form_add]

/--
[box_bar_eq_half_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
private lemma box_bar_eq_half_laplacian_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {_S : SymplecticManifold Ω VF}
  {dol : DolbeaultOps (inst := inst)}
  {cod : @Codifferential Ω VF inst}
  {dol_lap : DolbeaultLaplacian dol cod}
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (_J : AlmostComplexStr (inst := inst))
  (_hK : IsKahler _S _J)
  (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)), dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α) :
-- imply
  dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α := by
-- proof
  apply box_bar_eq_half_laplacian _S _J _hK dol_lap h_two_box_bar α

/--
[laplacian_preserves_bidegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean)
-/
@[path]
private lemma laplacian_preserves_bidegree_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {dol_lap : DolbeaultLaplacian dol cod}
  {J : AlmostComplexStr (inst := inst)}
  {n : ℕ}
  {bg : HasBigrading J n}
  {k : ℕ}
  {p' q' : ℕ}
  {ω : bg.Ω_pq p' q'}
-- given
  (J' : AlmostComplexStr (inst := inst))
  (hK : IsKahler S J')
  (cod : Codifferential (inst := inst))
  (dol : DolbeaultOps (inst := inst))
  (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'), ∃ ω' : bg.Ω_pq p' q', cast (congrArg Ω h) (bg.incl p' q' ω') = dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))
  (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)), dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α)
  (h : p' + q' = k + 1) :
-- imply
  ∃ ω' : bg.Ω_pq p' q', cast (congrArg Ω h) (bg.incl p' q' ω') = laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) := by
-- proof
  apply laplacian_preserves_bidegree S J' hK cod dol dol_lap bg h_box_bar_pres h_two_box_bar k p' q' h ω


-- created on 2026-10-23
