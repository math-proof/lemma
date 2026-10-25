import Mathlib
import sympy.Basic
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
open Filter Topology TestFunctions TestFunctions.SchwartzTestFunctionSpace
open scoped ZeroAtInfty
open ContinuousLinearMap


namespace TestFunctions

/--
[restrictDual_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma restrictDual_apply
  {n : ℕ}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup U]
  [NormedSpace 𝕜 U]
  {ι : V →L[𝕜] U}
  {L : U →L[𝕜] 𝕜} :
-- imply
  restrictDual ι L = L.comp ι :=
-- proof
  rfl

end TestFunctions

namespace TestFunctions

/--
[norm_restrictDual_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma norm_restrictDual_le
  {n : ℕ}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup U]
  [NormedSpace 𝕜 U]
  {ι : V →L[𝕜] U}
  {L : U →L[𝕜] 𝕜}
  {C : ℝ}
-- given
  (hC : ‖ι‖ ≤ C) :
-- imply
  ‖restrictDual ι L‖ ≤ C * ‖L‖ := by
-- proof
  calc ‖restrictDual ι L‖ = ‖L.comp ι‖ := rfl
    _ ≤ ‖L‖ * ‖ι‖ := L.opNorm_comp_le ι
    _ ≤ ‖L‖ * C := by gcongr
    _ = C * ‖L‖ := mul_comm _ _

end TestFunctions

namespace TestFunctions

/--
[restrictDual_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma restrictDual_injective
  {n : ℕ}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup U]
  [NormedSpace 𝕜 U]
  {ι : V →L[𝕜] U}
-- given
  (hd : DenseRange ι) :
-- imply
  Function.Injective (restrictDual ι) := by
-- proof
  intro L₁ L₂ h
  simp only [restrictDual_apply] at h
  have heq : (⇑L₁) ∘ (⇑ι) = (⇑L₂) ∘ (⇑ι) := by
    ext v
    exact ContinuousLinearMap.ext_iff.mp h v
  exact ContinuousLinearMap.ext
    (fun u => congr_fun (DenseRange.equalizer hd L₁.continuous L₂.continuous heq) u)

end TestFunctions

namespace TestFunctions

/--
[restrictDual_norm_bound_and_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma restrictDual_norm_bound_and_injective
  {n : ℕ}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup U]
  [NormedSpace 𝕜 U]
  {ι : V →L[𝕜] U}
  {C : ℝ}
-- given
  (hC : ‖ι‖ ≤ C) :
-- imply
  (∀ L : U →L[𝕜] 𝕜, ‖restrictDual ι L‖ ≤ C * ‖L‖) ∧ (DenseRange ι → Function.Injective (restrictDual ι)) :=
-- proof
  ⟨fun L => norm_restrictDual_le ι L hC, fun hd => restrictDual_injective ι hd⟩

end TestFunctions

namespace TestFunctions

/--
[japaneseBracket_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma japaneseBracket_ne_zero
  {n : ℕ}
  {n}
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  japaneseBracket n x ≠ 0 :=
-- proof
  ne_of_gt (japaneseBracket_pos n x)

end TestFunctions

namespace TestFunctions.SchwartzTestFunctionSpace

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma ext
  {n : ℕ}
  {n}
  {n : ℕ}
  {n : ℕ}
  {f g : SchwartzTestFunctionSpace n}
-- given
  (h : ∀ x, f x = g x) :
-- imply
  f = g :=
-- proof
  DFunLike.ext f g h

end TestFunctions.SchwartzTestFunctionSpace

namespace TestFunctions.SchwartzTestFunctionSpace

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma coe_mk
  {n : ℕ}
  {n}
  {n : ℕ}
  {n : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → ℂ}
  (hf) :
-- imply
  ⇑(mk f hf : SchwartzTestFunctionSpace n) = f :=
-- proof
  rfl
/-- Equivalence between our concrete `SchwartzTestFunctionSpace n` and Mathlib's
`SchwartzMap (ℝⁿ, ℂ)`, expressing Melrose's characterisation of Schwartz space. -/
section UniformConvergenceCLM

end TestFunctions.SchwartzTestFunctionSpace

namespace TestFunctions

/--
[euclideanSpace_norm_coord_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma euclideanSpace_norm_coord_le
  {n : ℕ}
  {n}
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {j : Fin n} :
-- imply
  ‖x j‖ ≤ ‖x‖ := by
-- proof
  rw [EuclideanSpace.norm_eq x]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ j)

end TestFunctions

namespace TestFunctions

/--
[opNorm_le_sum_basis_norms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
lemma opNorm_le_sum_basis_norms
  {n : ℕ}
  {n}
  {n : ℕ}
  {T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ} :
-- imply
  ‖T‖ ≤ ∑ j : Fin n, ‖T (EuclideanSpace.single j 1)‖ := by
-- proof
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg (fun j _ => norm_nonneg _))
  intro x
  have hdecomp : x = ∑ j : Fin n, (x j) • EuclideanSpace.single j (1 : ℝ) := by
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
    exact h.symm
  conv_lhs => rw [hdecomp]
  rw [map_sum]
  calc ‖∑ j : Fin n, T ((x j) • EuclideanSpace.single j 1)‖
    ≤ ∑ j : Fin n, ‖T ((x j) • EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, ‖x j‖ * ‖T (EuclideanSpace.single j 1)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ContinuousLinearMap.map_smul]
      exact norm_smul (x j) _
    _ ≤ ∑ j : Fin n, ‖x‖ * ‖T (EuclideanSpace.single j 1)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (euclideanSpace_norm_coord_le x j) (norm_nonneg _)
    _ = (∑ j : Fin n, ‖T (EuclideanSpace.single j 1)‖) * ‖x‖ := by
      rw [← Finset.mul_sum]; ring
end TestFunctions


/--
[japaneseBracket_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean)
-/
@[path]
private lemma japaneseBracket_pos_eq
  {n : ℕ}
  {n}
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  0 < japaneseBracket n x := by
-- proof
  apply TestFunctions.japaneseBracket_pos n n x


-- created on 2026-10-23
