import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MeasureTheory.Geometry.BanachTarski.Part16
open MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
open FinitelyEquidecomposableByIsometries


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btCongr_union](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btCongr_union {X : Type*} [MetricSpace X] {A₁ A₂ B₁ B₂ : Set X}
  (h1 : btCongr A₁ B₁) (h2 : btCongr A₂ B₂)
  (hdA : Disjoint A₁ A₂) (hdB : Disjoint B₁ B₂) :
  btCongr (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  obtain ⟨f1, S1, hfin1, hbij1, hloc1⟩ := h1
  obtain ⟨f2, S2, hfin2, hbij2, hloc2⟩ := h2
  classical
  have hA2 : ∀ x ∈ A₂, x ∉ A₁ := fun x hx2 hx1 =>
    Set.disjoint_left.mp hdA hx1 hx2
  have e1 : ∀ x ∈ A₁, (fun x => if x ∈ A₁ then f1 x else f2 x) x = f1 x :=
    fun x hx => ite_eq_left hx
  have e2 : ∀ x ∈ A₂, (fun x => if x ∈ A₁ then f1 x else f2 x) x = f2 x :=
    fun x hx => ite_eq_right (hA2 x hx)
  have hB1 : Set.BijOn (fun x => if x ∈ A₁ then f1 x else f2 x) A₁ B₁ :=
    hbij1.congr (fun x hx => (e1 x hx).symm)
  have hB2 : Set.BijOn (fun x => if x ∈ A₁ then f1 x else f2 x) A₂ B₂ :=
    hbij2.congr (fun x hx => (e2 x hx).symm)
  have hinj : Set.InjOn (fun x => if x ∈ A₁ then f1 x else f2 x) (A₁ ∪ A₂) := by
    intro x hx y hy hxy
    rw [Set.mem_union] at hx hy
    by_cases hx1 : x ∈ A₁ <;> by_cases hy1 : y ∈ A₁
    · rw [e1 x hx1, e1 y hy1] at hxy
      exact hbij1.2.1 hx1 hy1 hxy
    · have hy2 : y ∈ A₂ := hy.resolve_left hy1
      rw [e1 x hx1, e2 y hy2] at hxy
      have h1 : f1 x ∈ B₁ := hbij1.mapsTo hx1
      have h2 : f1 x ∈ B₂ := hxy ▸ hbij2.mapsTo hy2
      exact False.elim (Set.disjoint_left.mp hdB h1 h2)
    · have hx2 : x ∈ A₂ := hx.resolve_left hx1
      rw [e2 x hx2, e1 y hy1] at hxy
      have h1 : f1 y ∈ B₁ := hbij1.mapsTo hy1
      have h2 : f1 y ∈ B₂ := hxy.symm ▸ hbij2.mapsTo hx2
      exact False.elim (Set.disjoint_left.mp hdB h1 h2)
    · have hx2 : x ∈ A₂ := hx.resolve_left hx1
      have hy2 : y ∈ A₂ := hy.resolve_left hy1
      rw [e2 x hx2, e2 y hy2] at hxy
      exact hbij2.2.1 hx2 hy2 hxy
  refine ⟨fun x => if x ∈ A₁ then f1 x else f2 x, S1 ∪ S2, hfin1.union hfin2,
    hB1.union hB2 hinj, ?_⟩
  intro x hx
  rw [Set.mem_union] at hx
  obtain hx1 | hx2 := hx
  · obtain ⟨g, hgS, hgx⟩ := hloc1 x hx1
    exact ⟨g, Set.mem_union_left _ hgS, by rw [e1 x hx1]; exact hgx⟩
  · obtain ⟨g, hgS, hgx⟩ := hloc2 x hx2
    exact ⟨g, Set.mem_union_right _ hgS, by rw [e2 x hx2]; exact hgx⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btCongr_self_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btCongr_self_image {X : Type*} [MetricSpace X]
  (g : X ≃ᵢ X) (A : Set X) : btCongr A (g '' A) := by
  refine ⟨g, {g}, Set.finite_singleton _, g.injective.bijOn_image, ?_⟩
  intro x _
  exact ⟨g, rfl, rfl⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btCongr_absorb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
never returns to `C`, then `Y` is congruent to `Y \ C`. -/
private lemma btCongr_absorb {X : Type*} [MetricSpace X]
  (σ : X ≃ᵢ X) {C Y : Set X}
  (hY : ∀ n : ℕ, (⇑σ)^[n] '' C ⊆ Y)
  (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((⇑σ)^[n] '' C) C) :
  btCongr Y (Y \ C) := by
  classical
  set Ct : Set X := ⋃ n, (⇑σ)^[n] '' C with hCt
  have hCsub : C ⊆ Ct := by
    intro c hc
    rw [hCt]
    exact Set.mem_iUnion.mpr ⟨0, c, hc, rfl⟩
  have htsub : Ct ⊆ Y := Set.iUnion_subset hY
  have hiter : ∀ (n : ℕ) (c : X), (⇑σ)^[n.succ] c = σ ((⇑σ)^[n] c) :=
    fun n c => Function.iterate_succ_apply' _ n c
  have hmem : ∀ (n : ℕ) (c : X), c ∈ C → (⇑σ)^[n] c ∈ Ct := by
    intro n c hc
    rw [hCt]
    exact Set.mem_iUnion.mpr ⟨n, c, hc, rfl⟩
  have hsigCt : ∀ x ∈ Ct, σ x ∈ Ct := by
    intro x hx
    rw [hCt, Set.mem_iUnion] at hx
    obtain ⟨n, c, hcC, rfl⟩ := hx
    rw [← hiter n c]
    exact hmem n.succ c hcC
  have e1 : ∀ x ∈ Ct, (fun x => if x ∈ Ct then σ x else x) x = σ x :=
    fun x hx => ite_eq_left hx
  have e2 : ∀ x ∉ Ct, (fun x => if x ∈ Ct then σ x else x) x = x :=
    fun x hx => ite_eq_right hx
  refine ⟨fun x => if x ∈ Ct then σ x else x, {σ, IsometryEquiv.refl X},
    (Set.finite_singleton _).union (Set.finite_singleton _), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hxY
    by_cases hxCt : x ∈ Ct
    · rw [e1 x hxCt]
      refine ⟨htsub (hsigCt x hxCt), ?_⟩
      rw [hCt, Set.mem_iUnion] at hxCt
      obtain ⟨n, c, hcC, rfl⟩ := hxCt
      intro hcon
      have hmemC : (⇑σ)^[n.succ] c ∈ (⇑σ)^[n.succ] '' C := ⟨c, hcC, rfl⟩
      have hcon' : (⇑σ)^[n.succ] c ∈ C := by
        rwa [hiter n c]
      exact Set.disjoint_left.mp
        (hdisj n.succ (Nat.succ_le_succ (Nat.zero_le n))) hmemC hcon'
    · rw [e2 x hxCt]
      refine ⟨hxY, ?_⟩
      exact fun hcon => hxCt (hCsub hcon)
  · intro x hxX y hyY heq
    by_cases hxCt : x ∈ Ct <;> by_cases hyCt : y ∈ Ct
    · rw [e1 x hxCt, e1 y hyCt] at heq
      exact σ.injective heq
    · rw [e1 x hxCt, e2 y hyCt] at heq
      exact False.elim (hyCt (heq ▸ hsigCt x hxCt))
    · rw [e2 x hxCt, e1 y hyCt] at heq
      exact False.elim (hxCt (heq.symm ▸ hsigCt y hyCt))
    · rw [e2 x hxCt, e2 y hyCt] at heq
      exact heq
  · intro y hyY
    obtain ⟨hyY', hyC⟩ := hyY
    by_cases hyCt : y ∈ Ct
    · rw [hCt, Set.mem_iUnion] at hyCt
      obtain ⟨n, hn⟩ := hyCt
      obtain ⟨c, hcC, hyc⟩ := hn
      cases n with
      | zero =>
        have hcc : c = y := hyc
        exact False.elim (hyC (hcc ▸ hcC))
      | succ m =>
        refine ⟨(⇑σ)^[m] c, htsub (hmem m c hcC), ?_⟩
        rwa [e1 _ (hmem m c hcC), ← hiter m c]
    · exact ⟨y, hyY', by rw [e2 y hyCt]⟩
  · intro x hxY
    by_cases hxCt : x ∈ Ct
    · rw [hCt, Set.mem_iUnion] at hxCt
      obtain ⟨n, c, hcC, rfl⟩ := hxCt
      exact ⟨σ, by simp, e1 _ (hmem n c hcC)⟩
    · exact ⟨IsometryEquiv.refl X, by simp, by rw [e2 x hxCt]; rfl⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btIsoOfUnitary_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btIsoOfUnitary_zero (U : Matrix.unitaryGroup (Fin 3) ℝ) :
  btIsoOfUnitary U 0 = 0 := by
  change (Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩).toLinearIsometry 0 = 0
  exact LinearIsometry.map_zero _

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btIsoOfUnitary_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btIsoOfUnitary_norm (U : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
  ‖btIsoOfUnitary U x‖ = ‖x‖ := by
  change ‖(Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩) x‖ = ‖x‖
  exact LinearIsometryEquiv.norm_map _ x

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotZ_mat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotZ_mat (θ : ℝ) :
  (btRotZ θ : Matrix (Fin 3) (Fin 3) ℝ) =
    !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, (1 : ℝ)] :=
  rfl

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_mat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_mat (θ : ℝ) :
  (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) =
    !![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, (Real.cos θ : ℝ)] :=
  rfl

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_add (a b : ℝ) : btRotY (a + b) = btRotY a * btRotY b := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, btRotY_mat, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_add, Real.sin_add] <;> ring

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotZ_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotZ_add (a b : ℝ) : btRotZ (a + b) = btRotZ a * btRotZ b := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, btRotZ_mat, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_add, Real.sin_add] <;> ring

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_zero : btRotY 0 = 1 := by
  apply Subtype.ext
  simp only [btRotY_mat, Submonoid.coe_one, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_zero, Real.sin_zero]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotZ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotZ_zero : btRotZ 0 = 1 := by
  apply Subtype.ext
  simp only [btRotZ_mat, Submonoid.coe_one, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_zero, Real.sin_zero]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_fix_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_fix_cos (θ : ℝ) (u : Fin 3 → ℝ)
  (h : Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) u = u)
  (hne : (u 0, u 2) ≠ (0, 0)) : Real.cos θ = 1 := by
  rw [btRotY_mat] at h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h2
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, zero_mul, add_zero,
    Matrix.cons_val, neg_mul] at h0 h2
  have hS : u 0 ^ 2 + u 2 ^ 2 ≠ 0 := by
    intro hz
    have e1 : u 0 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 2 ^ 2 := sq_nonneg _
      linarith
    have e2 : u 2 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 2 ^ 2 := sq_nonneg _
      linarith
    rw [sq_eq_zero_iff] at e1 e2
    exact hne (by rw [e1, e2])
  have hcomb : Real.cos θ * (u 0 ^ 2 + u 2 ^ 2) = u 0 ^ 2 + u 2 ^ 2 := by
    linear_combination u 0 * h0 + u 2 * h2
  have hcomb2 : Real.cos θ * (u 0 ^ 2 + u 2 ^ 2)
    = 1 * (u 0 ^ 2 + u 2 ^ 2) := by
    rw [hcomb, one_mul]
  exact mul_right_cancel₀ hS hcomb2

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotZ_fix_cos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotZ_fix_cos (θ : ℝ) (u : Fin 3 → ℝ)
  (h : Matrix.mulVec (btRotZ θ : Matrix (Fin 3) (Fin 3) ℝ) u = u)
  (hne : (u 0, u 1) ≠ (0, 0)) : Real.cos θ = 1 := by
  rw [btRotZ_mat] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, zero_mul, add_zero,
    Matrix.cons_val, neg_mul] at h0 h1
  have hS : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro hz
    have e1 : u 0 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 1 ^ 2 := sq_nonneg _
      linarith
    have e2 : u 1 ^ 2 = 0 := by
      have h1 : 0 ≤ u 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ u 1 ^ 2 := sq_nonneg _
      linarith
    rw [sq_eq_zero_iff] at e1 e2
    exact hne (by rw [e1, e2])
  have hcomb : Real.cos θ * (u 0 ^ 2 + u 1 ^ 2) = u 0 ^ 2 + u 1 ^ 2 := by
    linear_combination u 0 * h0 + u 1 * h1
  have hcomb2 : Real.cos θ * (u 0 ^ 2 + u 1 ^ 2)
    = 1 * (u 0 ^ 2 + u 1 ^ 2) := by
    rw [hcomb, one_mul]
  exact mul_right_cancel₀ hS hcomb2

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btInv_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btInv_of (x : Fin 2) :
  (FreeGroup.of x)⁻¹ = FreeGroup.mk [(x, false)] :=
  rfl

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btT_word](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btT_word (n : ℕ) :
  ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n).toWord =
    List.replicate n ((0 : Fin 2), false) := by
  rw [inv_pow, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow]
  simp [FreeGroup.invRev]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btToWord_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btToWord_of (x : Fin 2) :
  (FreeGroup.of x).toWord = [(x, true)] := by
  have h1 : FreeGroup.of x = FreeGroup.mk [(x, true)] := rfl
  rw [h1, FreeGroup.toWord_mk]
  exact FreeGroup.IsReduced.reduce_eq FreeGroup.IsReduced.singleton

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btW_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btW_of (x : Fin 2) : FreeGroup.of x ∈ btW (x, true) := by
  change (FreeGroup.of x).toWord.head? = some (x, true)
  rw [btToWord_of x, List.head?_cons]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btW_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btW_disjoint {s t : Fin 2 × Bool} (h : s ≠ t) :
  Disjoint (btW s) (btW t) := by
  rw [Set.disjoint_left]
  intro w hws hwt
  exact h (Option.some_inj.mp (hws.symm.trans hwt))

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btT_disjoint_W](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btT_disjoint_W {s : Fin 2 × Bool} (hs : s ≠ (0, false)) :
  Disjoint btT (btW s) := by
  rw [Set.disjoint_left]
  intro w hwT hw
  obtain ⟨n, rfl⟩ := hwT
  simp only [btW, Set.mem_ofPred_eq] at hw
  rw [btT_word] at hw
  cases n with
  | zero =>
    rw [List.replicate_zero] at hw
    have hsn : (some s : Option (Fin 2 × Bool)) = none := hw.symm
    exact Option.some_ne_none s hsn
  | succ n =>
    rw [List.replicate_succ] at hw
    exact hs ((Option.some_inj.mp hw).symm)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btFree_mem_inv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btFree_mem_inv_mul (x : Fin 2) (v : FreeGroup (Fin 2)) :
  (FreeGroup.of x)⁻¹ * v ∈ btW (x, false) ↔ v ∉ btW (x, true) := by
  simp only [btW, Set.mem_ofPred_eq, btInv_of, FreeGroup.toWord_mk_mul_eq,
    Bool.not_false]
  match hv : v.toWord with
  | [] =>
    simp
  | hd :: tl =>
    by_cases heq : hd = (x, true)
    · have hc : ((hd :: tl).head? = some (x, true)) := by
      rw [heq, List.head?_cons]
      rw [ite_eq_left hc, hc, eq_self_iff_true, not_true_eq_false, iff_false]
      cases tl with
      | nil =>
        intro h
        exact Option.some_ne_none _ h.symm
      | cons hd2 tl2 =>
        have hred : FreeGroup.IsReduced ((x, true) :: hd2 :: tl2) := by
          rwa [← heq, ← hv]
        have hstep := (FreeGroup.isReduced_cons_cons).mp hred
        intro hcon
        have hd2eq : hd2 = (x, false) := Option.some_inj.mp hcon
        rw [hd2eq] at hstep
        have hcontra := hstep.1 rfl
        simp at hcontra
    · have hne2 : (hd :: tl).head? ≠ some (x, true) := by
      intro h
      apply heq
      have h2 : (some hd : Option (Fin 2 × Bool)) = some (x, true) := h
      exact Option.some_inj.mp h2
      rw [ite_eq_right hne2]
      exact iff_of_true List.head?_cons hne2

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btFree_pieces](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btFree_pieces :
  Disjoint btP₁ btP₂ ∧ Disjoint btP₁ btP₃ ∧ Disjoint btP₁ btP₄ ∧
  Disjoint btP₂ btP₃ ∧ Disjoint btP₂ btP₄ ∧ Disjoint btP₃ btP₄ ∧
  btP₁ ∪ btP₂ ∪ btP₃ ∪ btP₄ = Set.univ := by
  have dWW1 : Disjoint (btW (0, true)) (btW (0, false)) :=
    btW_disjoint (by decide)
  have dWW2 : Disjoint (btW (0, true)) (btW (1, true)) :=
    btW_disjoint (by decide)
  have dWW3 : Disjoint (btW (0, true)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dWW4 : Disjoint (btW (0, false)) (btW (1, true)) :=
    btW_disjoint (by decide)
  have dWW5 : Disjoint (btW (0, false)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dWW6 : Disjoint (btW (1, true)) (btW (1, false)) :=
    btW_disjoint (by decide)
  have dT1 : Disjoint btT (btW (0, true)) := btT_disjoint_W (by decide)
  have dT3 : Disjoint btT (btW (1, true)) := btT_disjoint_W (by decide)
  have dT4 : Disjoint btT (btW (1, false)) := btT_disjoint_W (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro w hw12 hw2
    simp only [btP₁, Set.mem_union] at hw12
    simp only [btP₂] at hw2
    obtain ⟨hw, hnT⟩ := hw2
    obtain hw1 | hT := hw12
    · exact Set.disjoint_left.mp dWW1 hw1 hw
    · exact hnT hT
  · rw [Set.disjoint_left]
    intro w hw13 hw3
    simp only [btP₁, Set.mem_union] at hw13
    obtain hw1 | hT := hw13
    · exact Set.disjoint_left.mp dWW2 hw1 hw3
    · exact Set.disjoint_left.mp dT3 hT hw3
  · rw [Set.disjoint_left]
    intro w hw14 hw4
    simp only [btP₁, Set.mem_union] at hw14
    obtain hw1 | hT := hw14
    · exact Set.disjoint_left.mp dWW3 hw1 hw4
    · exact Set.disjoint_left.mp dT4 hT hw4
  · rw [Set.disjoint_left]
    intro w hw2 hw3
    simp only [btP₂] at hw2
    obtain ⟨hw, -⟩ := hw2
    exact Set.disjoint_left.mp dWW4 hw hw3
  · rw [Set.disjoint_left]
    intro w hw2 hw4
    simp only [btP₂] at hw2
    obtain ⟨hw, -⟩ := hw2
    exact Set.disjoint_left.mp dWW5 hw hw4
  · exact dWW6
  · rw [Set.eq_univ_iff_forall]
    intro w
    by_cases hw1 : w = 1
    · subst hw1
      have h1T : (1 : FreeGroup (Fin 2)) ∈ btT := ⟨0, by simp⟩
      exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ h1T)))
    · have hne : w.toWord ≠ [] :=
      fun hempty => hw1 (FreeGroup.toWord_eq_nil_iff.mp hempty)
      cases hl : w.toWord with
      | nil => exact absurd hl hne
      | cons hd tl =>
        have hwW : w ∈ btW hd := by
          change w.toWord.head? = some hd
          rw [hl, List.head?_cons]
        obtain ⟨a, b⟩ := hd
        have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
        obtain rfl | rfl <;> cases b := ha
        · by_cases hT : w ∈ btT
          · exact Set.mem_union_left _ (Set.mem_union_left _
            (Set.mem_union_left _ (Set.mem_union_right _ hT)))
          · have hwP2 : w ∈ btP₂ := by
            simp only [btP₂]
            exact ⟨hwW, hT⟩
            exact Set.mem_union_left _ (Set.mem_union_left _
              (Set.mem_union_right _ hwP2))
        · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ hwW)))
        · exact Set.mem_union_right _ hwW
        · exact Set.mem_union_left _ (Set.mem_union_right _ hwW)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btFree_image_P2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
of `btP₁`. -/
private lemma btFree_image_P2 :
  (fun w => FreeGroup.of (0 : Fin 2) * w) '' btP₂ = btP₁ᶜ := by
  ext v
  simp only [Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨u, huP2, rfl⟩
    simp only [btP₂] at huP2
    obtain ⟨huW, huT⟩ := huP2
    intro hcon
    simp only [btP₁, Set.mem_union, btT, Set.mem_range] at hcon
    obtain hW | ⟨n, hn⟩ := hcon
    · have hcancel : (FreeGroup.of (0 : Fin 2))⁻¹ *
      (FreeGroup.of (0 : Fin 2) * u) = u :=
      inv_mul_cancel_left _ _
      have hmem : (FreeGroup.of (0 : Fin 2))⁻¹ *
        (FreeGroup.of (0 : Fin 2) * u) ∈ btW (0, false) := by
        rwa [hcancel]
      exact (btFree_mem_inv_mul 0 (FreeGroup.of 0 * u)).mp hmem hW
    · have hu_eq : u = (FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1) := by
      have e : (FreeGroup.of (0 : Fin 2))⁻¹ *
        ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n) =
        (FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1) :=
        (pow_succ' _ _).symm
      rw [hn] at e
      rwa [inv_mul_cancel_left] at e
      exact huT ⟨n + 1, hu_eq.symm⟩
  · intro hv
    have hW : v ∉ btW (0, true) := fun h => hv (Set.mem_union_left _ h)
    have hT : v ∉ btT := fun h => hv (Set.mem_union_right _ h)
    have huW : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∈ btW (0, false) :=
      (btFree_mem_inv_mul 0 v).mpr hW
    have huT : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∉ btT := by
      intro hcon
      simp only [btT, Set.mem_range] at hcon
      obtain ⟨n, hn⟩ := hcon
      have hv_eq : v =
        FreeGroup.of (0 : Fin 2) * ((FreeGroup.of (0 : Fin 2))⁻¹ ^ n) := by
        rw [hn]
        exact (mul_inv_cancel_left (FreeGroup.of (0 : Fin 2)) v).symm
      cases n with
      | zero =>
        rw [pow_zero, mul_one] at hv_eq
        apply hW
        rw [hv_eq]
        exact btW_of 0
      | succ n =>
        have e : FreeGroup.of (0 : Fin 2) *
          ((FreeGroup.of (0 : Fin 2))⁻¹ ^ (n + 1)) =
          (FreeGroup.of (0 : Fin 2))⁻¹ ^ n := by
          rw [pow_succ', mul_inv_cancel_left]
        rw [e] at hv_eq
        exact hT ⟨n, hv_eq.symm⟩
    have huP2 : (FreeGroup.of (0 : Fin 2))⁻¹ * v ∈ btP₂ := by
      simp only [btP₂]
      exact ⟨huW, huT⟩
    exact ⟨(FreeGroup.of (0 : Fin 2))⁻¹ * v, huP2, mul_inv_cancel_left _ _⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btFree_image_P4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
of `btP₃`. -/
private lemma btFree_image_P4 :
  (fun w => FreeGroup.of (1 : Fin 2) * w) '' btP₄ = btP₃ᶜ := by
  ext v
  simp only [Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨u, huP4, rfl⟩
    have hcancel : (FreeGroup.of (1 : Fin 2))⁻¹ *
      (FreeGroup.of (1 : Fin 2) * u) = u :=
      inv_mul_cancel_left _ _
    have hmem : (FreeGroup.of (1 : Fin 2))⁻¹ *
      (FreeGroup.of (1 : Fin 2) * u) ∈ btW (1, false) := by
      rwa [hcancel]
    exact (btFree_mem_inv_mul 1 (FreeGroup.of 1 * u)).mp hmem
  · intro hv
    have hW : v ∉ btW (1, true) := hv
    have huW : (FreeGroup.of (1 : Fin 2))⁻¹ * v ∈ btW (1, false) :=
      (btFree_mem_inv_mul 1 v).mpr hW
    exact ⟨(FreeGroup.of (1 : Fin 2))⁻¹ * v, huW, mul_inv_cancel_left _ _⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRep_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRep_orbit (x y : {x : btE // x ∈ btOmega})
  (h : ∃ w : FreeGroup (Fin 2), btAct w x.val = y.val) : btRep x = btRep y := by
  unfold btRep
  rw [Quotient.sound (s := btOrbitRel) h]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btOfLp_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btOfLp_add (a b : btE) :
  WithLp.ofLp (a + b) = WithLp.ofLp a + WithLp.ofLp b :=
  map_add (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) a b

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btOfLp_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btOfLp_zero : WithLp.ofLp (0 : btE) = 0 :=
  map_zero (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btOfLp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btOfLp_neg (a : btE) :
  WithLp.ofLp (-a) = -(WithLp.ofLp a) :=
  map_neg (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)) a

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btC_coords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btC_coords : WithLp.ofLp btC = ![1 / 2, 0, (0 : ℝ)] := by
  simp [btC]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btC_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btC_coord0 : WithLp.ofLp btC 0 = 1 / 2 := by
  simp [btC_coords, Matrix.cons_val_zero]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btC_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btC_norm : ‖btC‖ = 1 / 2 := by
  have e0 : btC 0 = (1 / 2 : ℝ) := rfl
  have e1 : btC 1 = (0 : ℝ) := rfl
  have e2 : btC 2 = (0 : ℝ) := rfl
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, e0, e1, e2]
  have h1 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [h1, norm_zero]
  have h2 : (1 / 2 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = (1 / 2) ^ 2 := by ring
  rw [h2]
  exact Real.sqrt_sq (by norm_num)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btSigma_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btSigma_apply (x : btE) :
  btSigma x = btC + btIsoOfUnitary (btRotZ 1) (x + (-btC)) := by
  simp only [btSigma, IsometryEquiv.trans_apply, IsometryEquiv.addRight_apply]
  exact add_comm _ _

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_mulVec (a b : ℝ) (Z : Fin 3 → ℝ) :
  Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ)
    (Matrix.mulVec (btRotY b : Matrix (Fin 3) (Fin 3) ℝ) Z) =
    Matrix.mulVec (btRotY (a + b) : Matrix (Fin 3) (Fin 3) ℝ) Z := by
  rw [btRotY_add, Submonoid.coe_mul, Matrix.mulVec_mulVec]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_inj (a : ℝ) (X Y : Fin 3 → ℝ)
  (hXY : Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ) X =
    Matrix.mulVec (btRotY a : Matrix (Fin 3) (Fin 3) ℝ) Y) : X = Y := by
  have e1 := congrArg (Matrix.mulVec (btRotY (-a) : Matrix (Fin 3) (Fin 3) ℝ)) hXY
  rw [btRotY_mulVec, btRotY_mulVec, neg_add_cancel] at e1
  have h0 : ∀ Z : Fin 3 → ℝ,
    Matrix.mulVec (btRotY (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) Z = Z := by
    intro Z
    simp [btRotY_zero]
  simp only [h0] at e1
  exact e1

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btRotY_dot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btRotY_dot (θ : ℝ) (u v : Fin 3 → ℝ) :
  dotProduct
    (Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) u)
    (Matrix.mulVec (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) v) =
    dotProduct u v := by
  have hort : Matrix.transpose (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ)
    * (btRotY θ : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp (btRotY θ).2
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hort, Matrix.vecMul_one]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btC₂_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btC₂_norm : ‖btC₂‖ = 3 := by
  have e0 : btC₂ 0 = (3 : ℝ) := rfl
  have e1 : btC₂ 1 = (0 : ℝ) := rfl
  have e2 : btC₂ 2 = (0 : ℝ) := rfl
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, e0, e1, e2]
  have h1 : ‖(3 : ℝ)‖ = 3 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [h1, norm_zero]
  have h2 : (3 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 3 ^ 2 := by ring
  rw [h2]
  exact Real.sqrt_sq (by norm_num)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[btC₂_dist](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma btC₂_dist : dist (0 : btE) btC₂ = 3 := by
  rw [dist_comm, dist_zero_right, btC₂_norm]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/--
[finitelyEquidecomposableByIsometries_iff_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma finitelyEquidecomposableByIsometries_iff_bijOn_eq
  [MetricSpace X]
  {A B : Set X} :
-- imply
  FinitelyEquidecomposableByIsometries A B ↔
    ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
    S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.finitelyEquidecomposableByIsometries_iff_bijOn A B

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma refl_eq
  [MetricSpace X]
  {A : Set X} :
-- imply
  FinitelyEquidecomposableByIsometries A A := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.refl A

/--
[symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma symm_eq
  [MetricSpace X]
  {A B : Set X}
-- given
  (h : FinitelyEquidecomposableByIsometries A B) :
-- imply
  FinitelyEquidecomposableByIsometries B A := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.symm h

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma trans_eq
  [MetricSpace X]
  {A B C : Set X}
-- given
  (h0 : FinitelyEquidecomposableByIsometries A B)
  (h1 : FinitelyEquidecomposableByIsometries B C) :
-- imply
  FinitelyEquidecomposableByIsometries A C := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.trans h0 h1

/--
[union](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma union_eq
  [MetricSpace X]
  {A₁ A₂ B₁ B₂ : Set X}
-- given
  (h0 : FinitelyEquidecomposableByIsometries A₁ B₁)
  (h1 : FinitelyEquidecomposableByIsometries A₂ B₂)
  (hdA : Disjoint A₁ A₂)
  (hdB : Disjoint B₁ B₂) :
-- imply
  FinitelyEquidecomposableByIsometries (A₁ ∪ A₂) (B₁ ∪ B₂) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.union h0 h1 hdA hdB

/--
[image_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma image_isometryEquiv_eq
  [MetricSpace X]
  {A : Set X}
-- given
  (g : X ≃ᵢ X) :
-- imply
  FinitelyEquidecomposableByIsometries A (g '' A) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries.image_isometryEquiv g A

/--
[banach_tarski_closedBall_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean)
-/
@[path]
private lemma banach_tarski_closedBall_unit_eq
  :
-- imply
  ∃ (c₁ c₂ : EuclideanSpace ℝ (Fin 3)),
    Disjoint (Metric.closedBall c₁ 1) (Metric.closedBall c₂ 1) ∧
    FinitelyEquidecomposableByIsometries
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1) := by
-- proof
  apply MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.banach_tarski_closedBall_unit


-- created on 2026-10-20
-- updated on 2026-10-26
