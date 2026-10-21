import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[Bialgebra_exists_id_eq_convMul_of_retract](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_id_eq_convMul_of_retract.lean)
-/
@[path]
private lemma main
  {k : Type u} [CommRing k]
  {D : Type v} [CommRing D] [Bialgebra k D] [Coalgebra.IsCocomm k D]
  {X : Type v} [CommRing X] [Bialgebra k X] [Coalgebra.IsCocomm k X]
  {r : BialgHom k D X}
  {j : BialgHom k X D}
  {e : D →ₗ[k] D}
  {FD : D →ₐ[k] D}
  {FX : X →ₐ[k] X}
  {VD : CoalgHom k D D}
  {VX : CoalgHom k X X}
  {a b : BialgHom k D D}
  -- given
  (_ : r.comp j = BialgHom.id k X)
  (hrej : LinearMap.comp (r : D →ₗ[k] X) (LinearMap.comp e (j : X →ₗ[k] D)) = LinearMap.id)
  (hF : (r : D →ₐ[k] X).comp FD = FX.comp (r : D →ₐ[k] X))
  (hV : LinearMap.comp (VD : D →ₗ[k] D) (j : X →ₗ[k] D) = LinearMap.comp (j : X →ₗ[k] D) (VX : X →ₗ[k] X))
  (he : e = (WithConv.toConv (LinearMap.comp FD.toLinearMap (a : D →ₗ[k] D)) * WithConv.toConv (LinearMap.comp (b : D →ₗ[k] D) (VD : D →ₗ[k] D))).ofConv) :
  -- imply
  ∃ a' b' : BialgHom k X X, a' = (r.comp a).comp j ∧ b' = (r.comp b).comp j ∧ (LinearMap.id : X →ₗ[k] X) = (WithConv.toConv (LinearMap.comp FX.toLinearMap (a' : X →ₗ[k] X)) * WithConv.toConv (LinearMap.comp (b' : X →ₗ[k] X) (VX : X →ₗ[k] X))).ofConv := by
  -- proof
  refine ⟨(r.comp a).comp j, (r.comp b).comp j, rfl, rfl, ?_⟩
  subst he
  set f : WithConv (D →ₗ[k] D) := WithConv.toConv (LinearMap.comp FD.toLinearMap (a : D →ₗ[k] D))
  set g : WithConv (D →ₗ[k] D) := WithConv.toConv (LinearMap.comp (b : D →ₗ[k] D) (VD : D →ₗ[k] D))
  have hr : (r : D →ₐ[k] X).toLinearMap = (r : D →ₗ[k] X) := rfl
  have hj : (j : CoalgHom k X D).toLinearMap = (j : X →ₗ[k] D) := rfl
  have h1 : (LinearMap.id : X →ₗ[k] X) = LinearMap.comp (LinearMap.comp (r : D →ₗ[k] X) (f * g).ofConv) (j : X →ₗ[k] D) := by
    rw [LinearMap.comp_assoc]
    apply hrej.symm
  have h2 := LinearMap.algHom_comp_convMul_distrib (r : D →ₐ[k] X) f g
  rw [hr] at h2
  rw [h2] at h1
  have h3 := LinearMap.convMul_comp_coalgHom_distrib (WithConv.toConv (LinearMap.comp (r : D →ₗ[k] X) f.ofConv)) (WithConv.toConv (LinearMap.comp (r : D →ₗ[k] X) g.ofConv)) (j : CoalgHom k X D)
  rw [hj] at h3
  rw [h3] at h1
  have hF' : LinearMap.comp (r : D →ₗ[k] X) FD.toLinearMap = LinearMap.comp FX.toLinearMap (r : D →ₗ[k] X) := by
    have := congrArg AlgHom.toLinearMap hF
    rwa [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, hr] at this
  have e1 : LinearMap.comp (WithConv.toConv (LinearMap.comp (r : D →ₗ[k] X) f.ofConv)).ofConv (j : X →ₗ[k] D) = LinearMap.comp FX.toLinearMap (((r.comp a).comp j : BialgHom k X X) : X →ₗ[k] X) := by
    show LinearMap.comp (LinearMap.comp (r : D →ₗ[k] X) (LinearMap.comp FD.toLinearMap (a : D →ₗ[k] D))) (j : X →ₗ[k] D) = _
    rw [← LinearMap.comp_assoc (a : D →ₗ[k] D) FD.toLinearMap (r : D →ₗ[k] X), hF']
    rfl
  have e2 : LinearMap.comp (WithConv.toConv (LinearMap.comp (r : D →ₗ[k] X) g.ofConv)).ofConv (j : X →ₗ[k] D) = LinearMap.comp (((r.comp b).comp j : BialgHom k X X) : X →ₗ[k] X) (VX : X →ₗ[k] X) := by
    show LinearMap.comp (LinearMap.comp (r : D →ₗ[k] X) (LinearMap.comp (b : D →ₗ[k] D) (VD : D →ₗ[k] D))) (j : X →ₗ[k] D) = _
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hV]
    rfl
  rwa [e1, e2] at h1


-- created on 2026-10-20
