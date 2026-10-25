import Mathlib
import sympy.Basic
import Def.CerednikDrinfeld_Ribbon
import Lemma.Int.P2MUtil

open CerednikDrinfeld

/--
[CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv.lean)
-/

private lemma pushforward_apply
  {E V : Type}
  [Fintype E]
  [DecidableEq V]
  (f : E → V) (x : E → ℤ) (v : V) :
  pushforward f x v = ∑ e, if f e = v then x e else 0 := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]

private lemma mem_ribbonKernel_iff'
  {E V : Type}
  [Fintype E]
  [DecidableEq V]
  (D : DegeneracyData E V) (x : E → ℤ) :
  x ∈ ribbonKernel D ↔ pushforward D.a x = 0 ∧ pushforward D.b x = 0 := by
  rw [mem_ribbonKernel, Fin.forall_fin_two]
  simp [jointDelta]


@[path]
private lemma main
  {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [DecidableEq V₁] [Fintype E₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁}
  {D₂ : DegeneracyData E₂ V₂}
-- given
  (eE : E₁ ≃ E₂)
  (eV : V₁ ≃ V₂)
  (ha : ∀ e, D₂.a (eE e) = eV (D₁.a e))
  (hb : ∀ e, D₂.b (eE e) = eV (D₁.b e))
  (hw : ∀ e, D₂.w (eE e) = D₁.w e) :
-- imply
  ∃ φ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂),
      (∀ (x : ↥(ribbonKernel D₁)) (e : E₁), (φ x : E₂ → ℤ) (eE e) = (x : E₁ → ℤ) e) ∧
      (∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (φ x) (φ y) = ribbonGram D₁ x y) := by
  classical
  let φ₀ : (E₁ → ℤ) ≃ₗ[ℤ] (E₂ → ℤ) := LinearEquiv.funCongrLeft ℤ ℤ eE.symm
  have hφ₀ : ∀ (x : E₁ → ℤ) (e₂ : E₂), φ₀ x e₂ = x (eE.symm e₂) := fun x e₂ => rfl
  have key : ∀ (f₁ : E₁ → V₁) (f₂ : E₂ → V₂), (∀ e, f₂ (eE e) = eV (f₁ e)) →
      ∀ (x : E₁ → ℤ) (v₂ : V₂), pushforward f₂ (φ₀ x) v₂ = pushforward f₁ x (eV.symm v₂) := by
-- proof
    intro f₁ f₂ hf x v₂
    rw [pushforward_apply, pushforward_apply, ← Equiv.sum_comp eE]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hφ₀, Equiv.symm_apply_apply, hf]
    have hiff : eV (f₁ e) = v₂ ↔ f₁ e = eV.symm v₂ := Equiv.apply_eq_iff_eq_symm_apply eV
    by_cases hc : f₁ e = eV.symm v₂
    · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
    · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]
  have hmem : ∀ x : E₁ → ℤ, x ∈ ribbonKernel D₁ ↔ φ₀ x ∈ ribbonKernel D₂ := by
    intro x
    rw [mem_ribbonKernel_iff', mem_ribbonKernel_iff']
    constructor
    ·
      rintro ⟨h1, h2⟩
      refine ⟨funext fun v₂ => ?_, funext fun v₂ => ?_⟩
      ·
        rw [key D₁.a D₂.a ha, h1]
        rfl
      ·
        rw [key D₁.b D₂.b hb, h2]
        rfl
    ·
      rintro ⟨h1, h2⟩
      refine ⟨funext fun v₁ => ?_, funext fun v₁ => ?_⟩
      ·
        have := congrFun h1 (eV v₁)
        rwa [key D₁.a D₂.a ha, Equiv.symm_apply_apply] at this
      ·
        have := congrFun h2 (eV v₁)
        rwa [key D₁.b D₂.b hb, Equiv.symm_apply_apply] at this
  have hmap : (ribbonKernel D₁).map (φ₀ : (E₁ → ℤ) →ₗ[ℤ] (E₂ → ℤ)) = ribbonKernel D₂ := by
    apply le_antisymm
    ·
      rintro _ ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    ·
      intro y hy
      refine ⟨φ₀.symm y, ?_, by simp⟩
      show φ₀.symm y ∈ ribbonKernel D₁
      rwa [hmem, LinearEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofSubmodules φ₀ _ _ hmap, fun x e => ?_, fun x y => ?_⟩
  ·
    show φ₀ (x : E₁ → ℤ) (eE e) = (x : E₁ → ℤ) e
    rw [hφ₀, Equiv.symm_apply_apply]
  ·
    rw [ribbonGram_apply, ribbonGram_apply, ← Equiv.sum_comp eE]
    refine Finset.sum_congr rfl fun e _ => ?_
    show (D₂.w (eE e) : ℤ) * (φ₀ (x : E₁ → ℤ) (eE e) * φ₀ (y : E₁ → ℤ) (eE e)) = _
    rw [hw, hφ₀, hφ₀, Equiv.symm_apply_apply]


-- created on 2026-10-23
