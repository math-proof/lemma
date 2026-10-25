import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u

/--
[Rep_exists_coind_res_linearEquiv_quotient_fun](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exists_coind_res_linearEquiv_quotient_fun.lean)
-/
@[path]
private lemma main
  {k S : Type u} [CommRing k] [Group S]
  (S'' : Subgroup S) [S''.Normal]
  (N : Rep k S) :
  -- imply
  ∃ e : Rep.coind S''.subtype (Rep.res S''.subtype N) ≃ₗ[k] (S ⧸ S'' → N), ∀ (s : S) (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) (q : S ⧸ S''), e ((Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ s f) q = N.ρ s (e f (q * (s : S ⧸ S''))) := by
  -- proof
  classical
  have hwd : ∀ (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) (x y : S), (x : S ⧸ S'') = y → N.ρ x⁻¹ ((f : S → N) x) = N.ρ y⁻¹ ((f : S → N) y) := by
    intro f x y hxy
    have ht : x⁻¹ * y ∈ S'' := QuotientGroup.eq.1 hxy
    have hconj : x * (x⁻¹ * y) * x⁻¹ ∈ S'' := Subgroup.Normal.conj_mem inferInstance _ ht x
    have e1 : y = (x * (x⁻¹ * y) * x⁻¹) * x := by group
    have := f.2 ⟨x * (x⁻¹ * y) * x⁻¹, hconj⟩ x
    rw [Subgroup.coe_subtype] at this
    have e2 : (f : S → N) y = N.ρ (x * (x⁻¹ * y) * x⁻¹) ((f : S → N) x) := by
      conv_lhs => rw [e1]
      apply this
    rw [e2, ← Module.End.mul_apply, ← map_mul]
    congr 1
    group
  let toΦ (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) (q : S ⧸ S'') : N := Quotient.liftOn' q (fun x => N.ρ x⁻¹ ((f : S → N) x)) (fun x y hxy => hwd f x y (Quotient.sound' hxy))
  have Φ_add (f g : Rep.coind S''.subtype (Rep.res S''.subtype N)) : toΦ (f + g) = toΦ f + toΦ g := by
    funext q
    induction q using QuotientGroup.induction_on
    ·
      rename_i x
      show N.ρ x⁻¹ ((f : S → N) x + (g : S → N) x) = N.ρ x⁻¹ ((f : S → N) x) + N.ρ x⁻¹ ((g : S → N) x)
      rw [map_add]
  have Φ_smul (c : k) (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) : toΦ (c • f) = c • toΦ f := by
    funext q
    induction q using QuotientGroup.induction_on
    ·
      rename_i x
      show N.ρ x⁻¹ (c • (f : S → N) x) = c • N.ρ x⁻¹ ((f : S → N) x)
      rw [map_smul]
  let Φ : Rep.coind S''.subtype (Rep.res S''.subtype N) →ₗ[k] (S ⧸ S'' → N) := ⟨⟨toΦ, Φ_add⟩, Φ_smul⟩
  have Φ_apply : ∀ (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) (x : S), Φ f (x : S ⧸ S'') = N.ρ x⁻¹ ((f : S → N) x) := fun _ _ => rfl
  have Ψ_coind (F : S ⧸ S'' → N) (s : S'') (x : S) : N.ρ ((s : S) * x) (F (((s : S) * x : S) : S ⧸ S'')) = N.ρ (s : S) (N.ρ x (F (x : S ⧸ S''))) := by
    rw [map_mul, Module.End.mul_apply]
    congr 2
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (s : S)).2 s.2, one_mul]
  let toΨ (F : S ⧸ S'' → N) : Rep.coind S''.subtype (Rep.res S''.subtype N) := ⟨fun x => N.ρ x (F (x : S ⧸ S'')), Ψ_coind F⟩
  have Ψ_add (F F' : S ⧸ S'' → N) : toΨ (F + F') = toΨ F + toΨ F' := by
    apply Subtype.ext
    funext x
    show N.ρ x (F x + F' x) = N.ρ x (F x) + N.ρ x (F' x)
    rw [map_add]
  have Ψ_smul (c : k) (F : S ⧸ S'' → N) : toΨ (c • F) = c • toΨ F := by
    apply Subtype.ext
    funext x
    show N.ρ x (c • F x) = c • N.ρ x (F x)
    rw [map_smul]
  let Ψ : (S ⧸ S'' → N) →ₗ[k] Rep.coind S''.subtype (Rep.res S''.subtype N) := ⟨⟨toΨ, Ψ_add⟩, Ψ_smul⟩
  have Ψ_apply : ∀ (F : S ⧸ S'' → N) (x : S), ((Ψ F : Rep.coind S''.subtype (Rep.res S''.subtype N)) : S → N) x = N.ρ x (F (x : S ⧸ S'')) := fun _ _ => rfl
  have h1 : ∀ f, Ψ (Φ f) = f := fun f => by
    apply Subtype.ext
    funext x
    rw [Ψ_apply, Φ_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : ∀ F, Φ (Ψ F) = F := fun F => by
    funext q
    induction q using QuotientGroup.induction_on
    ·
      rename_i x
      rw [Φ_apply, Ψ_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨LinearEquiv.ofLinearMap Φ Ψ (LinearMap.ext h2) (LinearMap.ext h1), fun s f q => ?_⟩
  induction q using QuotientGroup.induction_on
  ·
    rename_i x
    show Φ ((Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ s f) (x : S ⧸ S'') = N.ρ s (Φ f ((x : S ⧸ S'') * (s : S ⧸ S'')))
    rw [← QuotientGroup.mk_mul, Φ_apply, Φ_apply]
    show N.ρ x⁻¹ ((f : S → N) (x * s)) = N.ρ s (N.ρ (x * s)⁻¹ ((f : S → N) (x * s)))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, mul_inv_cancel_left]

-- created on 2026-10-20
