import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
open MeasureTheory Filter Topology SchwartzRepresentation
open scoped ZeroAtInfty SchwartzMap


namespace SchwartzRepresentation

/--
[hasTemperateGrowth_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean)
-/
@[path]
lemma hasTemperateGrowth_finset_prod
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedCommRing R]
  [NormedAlgebra ℝ R]
  {f : ι → E → R}
  {s : Finset ι}
-- given
  (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
-- imply
  (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
-- proof
  classical
  induction s using Finset.induction_on
  case empty =>
    simp only [Finset.prod_empty]
    exact Function.HasTemperateGrowth.const 1
  case insert a s' has ih =>
    simp only [Finset.prod_insert has]
    exact (hf _ (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[monomial_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean)
-/
@[path]
lemma monomial_hasTemperateGrowth
  {n : ℕ}
  {α : Fin n → ℕ} :
-- imply
  (monomial α).HasTemperateGrowth := by
-- proof
  show (fun x : EuclideanSpace ℝ (Fin n) => ∏ i : Fin n, (↑(x i) : ℂ) ^ α i).HasTemperateGrowth
  apply hasTemperateGrowth_finset_prod
  intro i _
  suffices h : (fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ)).HasTemperateGrowth by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ) ^ α i) =
      ((fun x : EuclideanSpace ℝ (Fin n) => (↑(x i) : ℂ)) ^ α i) := by
      ext x; simp [Pi.pow_apply]
    rw [heq]
    exact h.pow (α i)
  convert (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth using 1

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[sobolev_intermediate_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean)
-/
@[path]
lemma sobolev_intermediate_form
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  ∃ (M : ℕ) (v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)), ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), u φ = ∑ γ ∈ multiIndicesBall n M, c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ) :=
-- proof
  intermediate_form_eq1010 n u

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[leibniz_rewrite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean)
-/
@[path]
lemma leibniz_rewrite
  {n : ℕ}
  {n M : ℕ}
  {v : (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)), ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), (∑ γ ∈ multiIndicesBall n M, c0SchwartzPairing (v γ) (iterSchwartzDeriv γ φ)) = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m, c0SchwartzPairing (f α β) (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) :=
-- proof
  representation_rewrite n M v

end SchwartzRepresentation

namespace SchwartzRepresentation

/--
[schwartz_representation_improved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean)
-/
@[path]
lemma schwartz_representation_improved
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  ∃ (m : ℕ) (f : (Fin n → ℕ) → (Fin n → ℕ) → C₀(EuclideanSpace ℝ (Fin n), ℂ)), ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)), u φ = ∑ α ∈ multiIndicesBall n m, ∑ β ∈ multiIndicesBall n m, c0SchwartzPairing (f α β) (iterSchwartzDeriv β (SchwartzMap.smulLeftCLM ℂ (monomial α) φ)) := by
-- proof
  obtain ⟨M, v, hv⟩ := sobolev_intermediate_form n u
  obtain ⟨m, f, hf⟩ := leibniz_rewrite n M v
  exact ⟨m, f, fun φ => (hv φ).trans (hf φ)⟩
end SchwartzRepresentation



-- created on 2026-10-23
