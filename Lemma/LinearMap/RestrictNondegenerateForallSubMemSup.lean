import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup.lean)
-/
@[path]
private lemma main
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ]
  (ρ : Representation K Γ V) (χ : Γ →* Units K)
  (I : Subgroup Γ)
  (e : LinearMap.BilinForm K V)
  (hrefl : ∀ a b : V, e a b = 0 → e b a = 0)
  (hnondeg : ∀ a : V, (∀ b : V, e a b = 0) → a = 0)
  (hequiv : ∀ (γ : Γ) (a b : V), e (ρ γ a) (ρ γ b) = ((χ γ : Units K) : K) * e a b)
  (Vt Vo : Submodule K V)
  (hVt : ∀ γ ∈ I, ∀ x ∈ Vt, ρ γ x ∈ Vt)
  (hVo : ∀ γ ∈ I, ∀ y ∈ Vo, ρ γ y ∈ Vo)
  (hISO : ∀ x ∈ Vt, ∀ y ∈ Vo, e x y = 0)
  (hCUT : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ Vt ⊔ Vo)
  (hOLD : ∀ y ∈ Vo, (∀ y' ∈ Vo, e y y' = 0) → y = 0)
  (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
  -- imply
  e.orthogonal Vt ≤ Vt ⊔ Vo := by
  -- proof
  classical
  have hNd : e.Nondegenerate := ⟨hnondeg, fun b hb => hnondeg b fun a => hrefl _ _ (hb a)⟩
  have hRf : e.IsRefl := hrefl
  have hρinv : ∀ (γ : Γ) (v : V), ρ γ (ρ γ⁻¹ v) = v := fun γ v => by
    apply LinearMap.congr_fun _ v
    rw [← map_mul, mul_inv_cancel, map_one]
  have hWI : ∀ τ ∈ I, ∀ w ∈ Vt ⊔ Vo, ρ τ w ∈ Vt ⊔ Vo := by
    intro τ hτ w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    apply Submodule.add_mem_sup (hVt τ hτ x hx) (hVo τ hτ y hy)
  have hSI : ∀ τ ∈ I, ∀ a ∈ e.orthogonal (Vt ⊔ Vo), ρ τ a ∈ e.orthogonal (Vt ⊔ Vo) := by
    intro τ hτ a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at ha ⊢
    intro n hn
    have hn' : ρ τ⁻¹ n ∈ Vt ⊔ Vo := hWI τ⁻¹ (I.inv_mem hτ) n hn
    have h0 := ha _ hn'
    rw [← hρinv τ n, hequiv, h0, mul_zero]
  obtain ⟨τ₀, hτ₀I, hτ₀⟩ := hCYC
  have hSS : ∀ a ∈ e.orthogonal (Vt ⊔ Vo), ∀ b ∈ e.orthogonal (Vt ⊔ Vo), e a b = 0 := by
    intro a ha b hb
    have ha' : ρ τ₀ a ∈ e.orthogonal (Vt ⊔ Vo) := hSI τ₀ hτ₀I a ha
    have hwa : ρ τ₀ a - a ∈ Vt ⊔ Vo := hCUT τ₀ hτ₀I a
    have hwb : ρ τ₀ b - b ∈ Vt ⊔ Vo := hCUT τ₀ hτ₀I b
    have hz1 : e (ρ τ₀ a) (ρ τ₀ b - b) = 0 := hrefl _ _ ((LinearMap.BilinForm.mem_orthogonal_iff.1 ha') _ hwb)
    have hz2 : e (ρ τ₀ a - a) b = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) _ hwa
    have h1 : e (ρ τ₀ a) (ρ τ₀ b) = e a b := by
      have eq1 : ρ τ₀ a = a + (ρ τ₀ a - a) := by abel
      have eq2 : ρ τ₀ b = b + (ρ τ₀ b - b) := by abel
      calc
        _ = e (ρ τ₀ a) (b + (ρ τ₀ b - b)) := by rw [← eq2]
        _ = e (ρ τ₀ a) b + e (ρ τ₀ a) (ρ τ₀ b - b) := by rw [map_add]
        _ = e (ρ τ₀ a) b := by rw [hz1, add_zero]
        _ = e (a + (ρ τ₀ a - a)) b := by rw [← eq1]
        _ = e a b + e (ρ τ₀ a - a) b := by rw [map_add, LinearMap.add_apply]
        _ = e a b := by rw [hz2, add_zero]
    rw [hequiv] at h1
    apply (mul_eq_zero.1 _).resolve_left
    rw [sub_mul, one_mul, h1, sub_self]
    rw [sub_ne_zero]
    intro h
    apply hτ₀
    apply Units.ext (h.trans Units.val_one.symm)
  have hSW : e.orthogonal (Vt ⊔ Vo) ≤ Vt ⊔ Vo := by
    intro a ha
    have h : a ∈ e.orthogonal (e.orthogonal (Vt ⊔ Vo)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      apply hSS n hn a ha
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hNd hRf] at h
  have hOLD' : (e.restrict Vo).Nondegenerate := by
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    ·
      apply Submodule.coe_eq_zero.mp (hOLD y y.2 fun y' hy' => by
        have h := hy ⟨y', hy'⟩
        simp at h
        apply h)
    ·
      apply Submodule.coe_eq_zero.mp (hOLD y y.2 fun y' hy' => by
        have h := hy ⟨y', hy'⟩
        simp at h
        apply hrefl _ _ h)
  have hcompl : IsCompl Vo (e.orthogonal Vo) := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hRf hOLD'
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  have hv' : v ∈ Vo ⊔ e.orthogonal Vo := by
    rw [hcompl.sup_eq_top]
    apply Submodule.mem_top
  obtain ⟨y₀, hy₀, s, hs, rfl⟩ := Submodule.mem_sup.1 hv'
  have hsS : s ∈ e.orthogonal (Vt ⊔ Vo) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add, LinearMap.add_apply]
    have h1 : e x s = 0 := by
      have h := hv x hx
      rwa [map_add, hISO x hx y₀ hy₀, zero_add] at h
    have h2 : e y s = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hs) y hy
    rw [h1, h2, add_zero]
  refine Submodule.add_mem _ (Submodule.mem_sup_right hy₀) (hSW hsS)


-- created on 2026-10-20
