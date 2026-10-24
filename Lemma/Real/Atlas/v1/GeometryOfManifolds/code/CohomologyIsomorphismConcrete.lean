import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete
open ContinuousAlternatingMap DeRhamConcrete DeRhamConcrete.HasDeformationRetractConcrete
open DeRhamConcrete


namespace DeRhamConcrete.HasDeformationRetractConcrete

/--
[d_squared](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma d_squared
  {i : E_X → E_U}
  {π : E_U → E_X}
  {n : ℕ}
  {ω : DiffForm E_U n}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  extDeriv (extDeriv ω) = 0 :=
-- proof
  extDeriv_extDeriv (hdr.smooth_forms_U ω) le_top

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete.HasDeformationRetractConcrete

/--
[d_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma d_sub
  {i : E_X → E_U}
  {π : E_U → E_X}
  {n : ℕ}
  {ω₁ ω₂ : DiffForm E_U n}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  extDeriv (ω₁ - ω₂) = extDeriv ω₁ - extDeriv ω₂ := by
-- proof
  funext x
  have h1 := (hdr.smooth_forms_U ω₁).differentiable WithTop.top_ne_zero x
  have h2 := (hdr.smooth_forms_U ω₂).differentiable WithTop.top_ne_zero x
  simp only [extDeriv, Pi.sub_apply, fderiv_sub h1 h2]
  exact map_sub _ _ _

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete.HasDeformationRetractConcrete

/--
[d_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma d_add
  {i : E_X → E_U}
  {π : E_U → E_X}
  {n : ℕ}
  {ω₁ ω₂ : DiffForm E_U n}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  extDeriv (ω₁ + ω₂) = extDeriv ω₁ + extDeriv ω₂ := by
-- proof
  funext x
  exact extDeriv_add
    ((hdr.smooth_forms_U ω₁).differentiable WithTop.top_ne_zero x)
    ((hdr.smooth_forms_U ω₂).differentiable WithTop.top_ne_zero x)

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete.HasDeformationRetractConcrete

/--
[i_comm_d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma i_comm_d
  {i : E_X → E_U}
  {π : E_U → E_X}
  {n : ℕ}
  {ω : DiffForm E_U n}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  pullbackForm i (extDeriv ω) = extDeriv (pullbackForm i ω) := by
-- proof
  funext x
  have hω_diff : DifferentiableAt ℝ ω (i x) :=
    (hdr.smooth_forms_U ω).differentiable WithTop.top_ne_zero (i x)
  have := extDeriv_pullback (r := ⊤) hω_diff hdr.smooth_i.contDiffAt le_top
  simp only [pullbackForm] at this ⊢
  exact this.symm

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete.HasDeformationRetractConcrete

/--
[i_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma i_sub
  {i : E_X → E_U}
  {π : E_U → E_X}
  {n : ℕ}
  {ω₁ ω₂ : DiffForm E_U n}
-- given
  (_hdr : HasDeformationRetractConcrete i π) :
-- imply
  pullbackForm i (ω₁ - ω₂) = pullbackForm i ω₁ - pullbackForm i ω₂ :=
-- proof
  rfl

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete.HasDeformationRetractConcrete

variable {E_X E_U : Type*} [NormedAddCommGroup E_X] [NormedSpace ℝ E_X] [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]
variable {i : E_X → E_U} {π : E_U → E_X}
/--
[π_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma π_zero (_hdr : HasDeformationRetractConcrete i π)
  {n : ℕ} :
  pullbackForm π (0 : DiffForm E_X n) = (0 : DiffForm E_U n) :=
  rfl

end DeRhamConcrete.HasDeformationRetractConcrete

namespace DeRhamConcrete

/--
[cohomology_isomorphism_surjectivity_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma cohomology_isomorphism_surjectivity_concrete
  {i : E_X → E_U}
  {π : E_U → E_X}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  ∀ {p : ℕ} (α : DiffForm E_X p), ∃ (β : DiffForm E_U p), pullbackForm i β = α :=
-- proof
  fun α => ⟨pullbackForm π α, hdr.retraction α⟩

end DeRhamConcrete

namespace DeRhamConcrete

/--
[cohomology_isomorphism_injectivity_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma cohomology_isomorphism_injectivity_concrete
  {i : E_X → E_U}
  {π : E_U → E_X}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  ∀ (p : ℕ) (β : DiffForm E_U (p + 1)), extDeriv β = 0 → (∃ (γ : DiffForm E_X p), pullbackForm i β = extDeriv γ) → ∃ (η : DiffForm E_U p), β = extDeriv η := by
-- proof
  intro p β hclosed ⟨γ, hγ⟩
  set dπγ := extDeriv (pullbackForm π γ)
  set β' := β - dπγ with hβ'_def
  have hβ'_closed : extDeriv β' = 0 := by
    rw [hdr.d_sub β dπγ, hclosed, hdr.d_squared, sub_zero]
  have hβ'_vanish : pullbackForm i β' = 0 := by
    rw [hdr.i_sub β dπγ, hdr.i_comm_d (pullbackForm π γ), hdr.retraction γ, hγ, sub_self]
  have hformula := hdr.homotopy_formula β'
  have hK_zero : hdr.K (extDeriv β') = (0 : DiffForm E_U (p + 1)) := by
    rw [hβ'_closed]
    have := hdr.K_smul (0 : ℝ) (0 : DiffForm E_U (p + 1 + 1))
    simp [zero_smul] at this
    exact this
  have hpull_zero : pullbackForm π (pullbackForm i β') = (0 : DiffForm E_U (p + 1)) := by
    rw [hβ'_vanish, hdr.π_zero]
  have hKβ' : extDeriv (hdr.K β') = β' := by
    rwa [hK_zero, hpull_zero, add_zero, sub_zero] at hformula
  refine ⟨hdr.K β' + pullbackForm π γ, ?_⟩
  rw [hdr.d_add (hdr.K β') (pullbackForm π γ), hKβ']
  simp only [hβ'_def]
  abel

end DeRhamConcrete

namespace DeRhamConcrete

/--
[cohomology_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
lemma cohomology_isomorphism
  {i : E_X → E_U}
  {π : E_U → E_X}
-- given
  (hdr : HasDeformationRetractConcrete i π) :
-- imply
  (∀ {p : ℕ} (α : DiffForm E_X p), ∃ (β : DiffForm E_U p), pullbackForm i β = α) ∧ (∀ (p : ℕ) (β : DiffForm E_U (p + 1)), extDeriv β = 0 → (∃ (γ : DiffForm E_X p), pullbackForm i β = extDeriv γ) → ∃ (η : DiffForm E_U p), β = extDeriv η) ∧ (∀ (β : DiffForm E_U 0), extDeriv β = 0 → pullbackForm i β = 0 → β = 0) :=
-- proof
  ⟨cohomology_isomorphism_surjectivity_concrete i π hdr,
    cohomology_isomorphism_injectivity_concrete i π hdr,
    hdr.deg0_injectivity⟩
end DeRhamConcrete
section Instances
open DeRhamConcrete


/--
[pullbackForm_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
private lemma pullbackForm_id_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {ω : DiffForm E n} :
-- imply
  pullbackForm id ω = ω := by
-- proof
  apply pullbackForm_id ω

/--
[extDeriv_zero_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
private lemma extDeriv_zero_eq_zero_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ} :
-- imply
  extDeriv (0 : DiffForm E n) = (0 : DiffForm E (n + 1)) := by
-- proof
  apply extDeriv_zero_eq_zero

/--
[contDiff_of_subsingleton_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean)
-/
@[path]
private lemma contDiff_of_subsingleton_domain_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup E']
  [NormedSpace ℝ E']
  [Subsingleton E']
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {f : E' → F} :
-- imply
  ContDiff ℝ ⊤ f := by
-- proof
  apply contDiff_of_subsingleton_domain f


-- created on 2026-10-23
