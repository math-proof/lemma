import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Bialgebra_exists_id_eq_convMul_of_retract](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_id_eq_convMul_of_retract.lean)
-/
@[path]
private lemma main
    {k : Type u} [CommRing k] {D : Type v} [CommRing D] [Bialgebra k D] [Coalgebra.IsCocomm k D]
    {X : Type v} [CommRing X] [Bialgebra k X] [Coalgebra.IsCocomm k X]
    (r : D →ₐc[k] X) (j : X →ₐc[k] D) (hrj : r.comp j = BialgHom.id k X)
    (e : D →ₗ[k] D) (hrej : (r : D →ₗ[k] X) ∘ₗ e ∘ₗ (j : X →ₗ[k] D) = LinearMap.id)
    (FD : D →ₐ[k] D) (FX : X →ₐ[k] X) (hF : (r : D →ₐ[k] X).comp FD = FX.comp (r : D →ₐ[k] X))
    (VD : D →ₗc[k] D) (VX : X →ₗc[k] X) (hV : (VD : D →ₗ[k] D) ∘ₗ (j : X →ₗ[k] D) = (j : X →ₗ[k] D) ∘ₗ (VX : X →ₗ[k] X))
    (a b : D →ₐc[k] D)
    (he : e = (WithConv.toConv (FD.toLinearMap ∘ₗ (a : D →ₗ[k] D)) *
        WithConv.toConv ((b : D →ₗ[k] D) ∘ₗ (VD : D →ₗ[k] D))).ofConv) :
    ∃ a' b' : X →ₐc[k] X,
      a' = (r.comp a).comp j ∧ b' = (r.comp b).comp j ∧
      (LinearMap.id : X →ₗ[k] X) =
        (WithConv.toConv (FX.toLinearMap ∘ₗ (a' : X →ₗ[k] X)) *
          WithConv.toConv ((b' : X →ₗ[k] X) ∘ₗ (VX : X →ₗ[k] X))).ofConv := by
  refine ⟨(r.comp a).comp j, (r.comp b).comp j, rfl, rfl, ?_⟩
  subst he
  set f : WithConv (D →ₗ[k] D) := WithConv.toConv (FD.toLinearMap ∘ₗ (a : D →ₗ[k] D)) with hf
  set g : WithConv (D →ₗ[k] D) := WithConv.toConv ((b : D →ₗ[k] D) ∘ₗ (VD : D →ₗ[k] D)) with hg
  have hr : (r : D →ₐ[k] X).toLinearMap = (r : D →ₗ[k] X) := rfl
  have hj : (j : X →ₗc[k] D).toLinearMap = (j : X →ₗ[k] D) := rfl
  have hFD : FD.toLinearMap = (FD : D →ₗ[k] D) := rfl
  have h1 : (LinearMap.id : X →ₗ[k] X) = ((r : D →ₗ[k] X) ∘ₗ (f * g).ofConv) ∘ₗ (j : X →ₗ[k] D) := by
    rw [LinearMap.comp_assoc]; exact hrej.symm
  have h2 := LinearMap.algHom_comp_convMul_distrib (r : D →ₐ[k] X) f g
  rw [hr] at h2
  rw [h2] at h1
  have h3 := LinearMap.convMul_comp_coalgHom_distrib
    (WithConv.toConv ((r : D →ₗ[k] X) ∘ₗ f.ofConv)) (WithConv.toConv ((r : D →ₗ[k] X) ∘ₗ g.ofConv))
    (j : X →ₗc[k] D)
  rw [hj] at h3
  rw [h3] at h1
  have hF' : (r : D →ₗ[k] X) ∘ₗ FD.toLinearMap = FX.toLinearMap ∘ₗ (r : D →ₗ[k] X) := by
    have := congrArg AlgHom.toLinearMap hF
    rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, hr] at this
    exact this
  have e1 : (WithConv.toConv ((r : D →ₗ[k] X) ∘ₗ f.ofConv)).ofConv ∘ₗ (j : X →ₗ[k] D)
      = FX.toLinearMap ∘ₗ (((r.comp a).comp j : X →ₐc[k] X) : X →ₗ[k] X) := by
    show ((r : D →ₗ[k] X) ∘ₗ (FD.toLinearMap ∘ₗ (a : D →ₗ[k] D))) ∘ₗ (j : X →ₗ[k] D) = _
    rw [← LinearMap.comp_assoc (a : D →ₗ[k] D) FD.toLinearMap (r : D →ₗ[k] X), hF']
    rfl
  have e2 : (WithConv.toConv ((r : D →ₗ[k] X) ∘ₗ g.ofConv)).ofConv ∘ₗ (j : X →ₗ[k] D)
      = (((r.comp b).comp j : X →ₐc[k] X) : X →ₗ[k] X) ∘ₗ (VX : X →ₗ[k] X) := by
    show ((r : D →ₗ[k] X) ∘ₗ ((b : D →ₗ[k] D) ∘ₗ (VD : D →ₗ[k] D))) ∘ₗ (j : X →ₗ[k] D) = _
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hV]
    rfl
  rw [e1, e2] at h1
  exact h1

-- created on 2026-10-20
