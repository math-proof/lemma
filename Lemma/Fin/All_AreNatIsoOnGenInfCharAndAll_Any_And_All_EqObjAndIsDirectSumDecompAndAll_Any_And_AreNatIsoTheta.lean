import Mathlib
import Lemma.Int.IsDirectSummand
open ProjectiveFunctors


/--
[corollary_22_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Corollary22_6.lean)
-/
@[path]
lemma corollary_22_6
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R} :
-- imply
  (∀ (F₁ F₂ : EndoFunctorData R 𝔤) (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂) (Mverma : RepGfObj R 𝔤) (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma)) (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma)) (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _)) (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)), AreNatIsoOnGenInfChar lam F₁ F₂) ∧ (∀ (F : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F) (Mverma : RepGfObj R 𝔤) (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) (n : ℕ) (summands : Fin n → RepGfObj R 𝔤) (_hDecomp : IsDirectSumDecompObj (F.obj Mverma) summands), ∃ (F_i : Fin n → EndoFunctorData R 𝔤), (∀ i, IsProjectiveFunctor (F_i i)) ∧ (∀ i, (F_i i).obj Mverma = summands i) ∧ IsDirectSumDecomp F F_i) ∧ (∀ (H : ThetaFunctorData R 𝔤 Δ wg lam) (_hH : IsProjectiveThetaFunctor H), ∃ (F : EndoFunctorData R 𝔤) (_ : IsProjectiveFunctor F) (T : ThetaFunctorData R 𝔤 Δ wg lam), T.baseFunctor = F ∧ AreNatIsoTheta H T) := by
-- proof
  obtain ⟨h1, h2, h3⟩ := ProjectiveFunctors.corollary_22_6 Δ wg lam
  exact ⟨h1, h2, fun H hH => by
    obtain ⟨F, hF, hiso⟩ := h3 H hH
    exact ⟨F, hF, _, rfl, hiso⟩⟩


-- created on 2026-10-23
