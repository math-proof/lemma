import sympy.integrals.integrals
import sympy.vector.vector
import torch.stack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
open Tensor MeasureTheory


@[main]
private lemma main
  {s : List ℕ} {n : ℕ} {f : Fin n → ℝ → Tensor ℝ s}
-- given
  (hf : ∀ j, Integrable (f j) volume) :
-- imply
  ∫ x : ℝ, [j < n] f j x = [j < n] ∫ x : ℝ, f j x := by
-- proof
  let g : ℝ → (Fin n → Tensor ℝ s) := fun x j => f j x
  have hg : Integrable g volume := Integrable.of_eval hf
  -- `Stack n` is linear (additivity stackwise, scalar multiplication through the data)
  let L0 : (Fin n → Tensor ℝ s) →ₗ[ℝ] Tensor ℝ (n :: s) :=
    {
      toFun := Stack n
      map_add' := fun f₁ f₂ => by
        apply Tensor.Eq.of.All_EqGetS.fin
        intro i
        rw [EqGetStack.fin, Tensor.GetAdd.eq.AddGetS.fin, EqGetStack.fin, EqGetStack.fin]
        rfl
      map_smul' := fun r f₁ => by
        apply Tensor.Eq.of.EqDataS
        show (((List.Vector.range n).map fun i => r • f₁ i).map Tensor.data).flatten =
          ((((List.Vector.range n).map f₁).map Tensor.data).flatten).map (r * ·)
        have hv : ((List.Vector.range n).map fun i => r • f₁ i).map Tensor.data =
            (((List.Vector.range n).map f₁).map Tensor.data).map (·.map (r * ·)) := by
          rw [List.Vector.map_map, List.Vector.map_map, List.Vector.map_map]
          congr 1
        rw [hv]
        exact Vector.FlattenMap.eq.MapFlatten _
    }
  -- the domain is finite-dimensional, so the linear map is continuous
  let L : (Fin n → Tensor ℝ s) →L[ℝ] Tensor ℝ (n :: s) :=
    { L0 with cont := L0.continuous_of_finiteDimensional }
  -- commute the integral with the stack, then evaluate componentwise
  show ∫ x, L (g x) = L (fun i => ∫ x, f i x)
  rw [L.integral_comp_comm hg]
  congr 1
  funext i
  exact eval_integral hf i


-- created on 2026-09-14
