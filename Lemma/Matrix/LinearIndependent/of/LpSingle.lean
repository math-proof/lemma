import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.SL2CRepresentations
open Complex
open scoped Classical


/--
[lp_single_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean)
-/
@[path]
lemma lp_single_linearIndependent
-- imply
  LinearIndependent ℂ (fun i : ℕ => lp.single 2 i (1 : ℂ)) := by
-- proof
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h : ∀ k : ℕ, (∑ j ∈ s, g j • lp.single 2 j (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) k =
    (0 : lp (fun _ : ℕ => ℂ) 2) k := by
    intro k; exact congr_fun (congr_arg (fun x : lp (fun _ : ℕ => ℂ) 2 => (x : ℕ → ℂ)) hg) k
  specialize h i
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    lp.coeFn_zero, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simp [lp.single_apply] at h; exact h
  · intro j _ hji; simp [lp.single_apply, hji]
  · intro hi'; exact absurd hi hi'

/--
[lp_not_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean)
-/
@[path]
lemma lp_not_finiteDimensional
-- imply
  ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) := by
-- proof
  intro h
  have hli := lp_single_linearIndependent.lt_aleph0_of_finiteDimensional
  simp only [Cardinal.mk_nat] at hli
  exact lt_irrefl _ hli

/--
[no_liso_lp_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean)
-/
@[path]
lemma no_liso_lp_complex
-- imply
  IsEmpty (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] ℂ) := by
-- proof
  constructor
  intro T
  have : FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) :=
    T.symm.toLinearEquiv.finiteDimensional
  exact lp_not_finiteDimensional this


-- created on 2026-10-23
