import Mathlib
import sympy.Basic


/--
[Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_fst_mul_withConv_algHom_dualNumber_eq_counit.lean)
-/
@[path]
private lemma main
  [CommRing k] [CommRing B] [Bialgebra k B]
  {D₁ D₂ : B →ₐ[k] DualNumber k}
  {b : B}
-- given
  (h₁ : ∀ b : B, TrivSqZeroExt.fst (D₁ b) = Bialgebra.counitAlgHom k B b)
  (h₂ : ∀ b : B, TrivSqZeroExt.fst (D₂ b) = Bialgebra.counitAlgHom k B b) :
-- imply
  TrivSqZeroExt.fst (WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b) =
      Bialgebra.counitAlgHom k B b := by
-- proof
  have hD : ∀ (D : B →ₐ[k] DualNumber k), (∀ b, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b) →
      (TrivSqZeroExt.fstHom k k k).comp D = Bialgebra.counitAlgHom k B := fun D h => AlgHom.ext h

  have h1 : (WithConv.toConv (Bialgebra.counitAlgHom k B) : WithConv (B →ₐ[k] k)) = 1 := by
    rw [AlgHom.convOne_def]
    congr 1
  have key := AlgHom.comp_convMul_distrib (TrivSqZeroExt.fstHom k k k) (WithConv.toConv D₁) (WithConv.toConv D₂)
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, hD D₁ h₁, hD D₂ h₂, h1, one_mul] at key
  have := congrArg (fun f : B →ₐ[k] k => f b) key
  simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply] at this
  rw [this]
  show (1 : WithConv (B →ₐ[k] k)) b = _
  rw [AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl


-- created on 2026-10-05
