import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R]
  {Y : Type} [AddCommGroup Y] [Module R Y]
  {G : Type} [Group G]
  {U : Type} [CommGroup U]
    (ρ : G →* Module.End R Y) (t : G → R) (c : G →* Units R) (χ : G →* U) (D : U →* Module.End R Y)
    (ht : ∀ g h : G, t (g * h * g⁻¹) = t h)
    (hD : ∀ (u : U) (g : G), D u * ρ g = ρ g * D u)
    (N : Submodule R Y) (hNρ : ∀ (g : G), ∀ y ∈ N, ρ g y ∈ N) (_ : ∀ (u : U), ∀ y ∈ N, D u y ∈ N)
    (H : Subgroup G)
    (hρH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, ρ (g * h) y - ρ g y ∈ N)
    (htH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (t (g * h) - t g) • y ∈ N)
    (hcH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (((c (g * h) : Units R) : R) - ((c g : Units R) : R)) • y ∈ N)
    (hχH : ∀ (g : G), ∀ h ∈ H, χ (g * h) = χ g)
    (τ : G) (hτ : ρ τ * ρ τ - t τ • ρ τ + ((c τ : Units R) : R) • D (χ τ) = 0)
    (g h : G) (hh : h ∈ H) (y : Y) :
    -- imply
    (ρ (g * τ * g⁻¹ * h) * ρ (g * τ * g⁻¹ * h) - t (g * τ * g⁻¹ * h) • ρ (g * τ * g⁻¹ * h)
      + ((c (g * τ * g⁻¹ * h) : Units R) : R) • D (χ (g * τ * g⁻¹ * h))) y ∈ N := by
    -- proof
  set s : G := g * τ * g⁻¹ with hs_def
  have hρinv : ∀ z : Y, ρ g⁻¹ (ρ g z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hρinv' : ∀ z : Y, ρ g (ρ g⁻¹ z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hcs : c s = c τ := by
    rw [hs_def, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hχs : χ s = χ τ := by
    rw [hs_def, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hts : t s = t τ := ht g τ
  have hDρ : ∀ (u : U) (k : G) (z : Y), D u (ρ k z) = ρ k (D u z) := fun u k z => by
    rw [← Module.End.mul_apply, hD, Module.End.mul_apply]
  have hρs : ∀ z : Y, ρ s z = ρ g (ρ τ (ρ g⁻¹ z)) := fun z => by
    simp only [hs_def, map_mul, Module.End.mul_apply]
  have hEs : ∀ z : Y, ρ s (ρ s z) - t s • ρ s z + ((c s : Units R) : R) • D (χ s) z = 0 := by
    intro z
    have h0 := congrArg (fun f : Module.End R Y => ρ g (f (ρ g⁻¹ z))) hτ
    simp only [LinearMap.zero_apply, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply, map_add, map_sub, map_smul, ← hDρ, hρinv'] at h0
    simp only [hts, hcs, hχs, hρs, hρinv]
    apply h0
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
  rw [hχH s h hh]
  have e : ρ (s * h) (ρ (s * h) y) - t (s * h) • ρ (s * h) y + ((c (s * h) : Units R) : R) • D (χ s) y = (ρ (s * h) (ρ (s * h) y - ρ s y) + (ρ (s * h) (ρ s y) - ρ s (ρ s y))) - ((t (s * h) - t s) • ρ (s * h) y + t s • (ρ (s * h) y - ρ s y)) + (((c (s * h) : Units R) : R) - ((c s : Units R) : R)) • D (χ s) y + (ρ s (ρ s y) - t s • ρ s y + ((c s : Units R) : R) • D (χ s) y) := by
    simp only [map_sub, sub_smul, smul_sub]
    abel
  rw [e, hEs y, add_zero]
  refine N.add_mem (N.sub_mem (N.add_mem ?_ ?_) (N.add_mem ?_ ?_)) ?_
  ·
    apply hNρ _ _ (hρH s h hh y)
  ·
    apply hρH s h hh (ρ s y)
  ·
    apply htH s h hh (ρ (s * h) y)
  ·
    apply N.smul_mem _ (hρH s h hh y)
  ·
    apply hcH s h hh (D (χ s) y)


-- created on 2026-10-20
