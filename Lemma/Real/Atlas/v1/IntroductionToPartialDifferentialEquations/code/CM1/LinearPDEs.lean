import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs.Part4
open LinearDifferentialOperator


namespace LinearDifferentialOperator

/--
[toLinearMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma toLinearMap_apply
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {f : (Fin n → ℝ) → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  (L.toLinearMap hlin) f = L.apply f :=
-- proof
  rfl

end LinearDifferentialOperator

namespace LinearDifferentialOperator

/--
[apply_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma apply_add
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {u v : (Fin n → ℝ) → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  L.apply (u + v) = L.apply u + L.apply v := by
-- proof
  have := (L.toLinearMap hlin).map_add u v
  simp only [toLinearMap_apply] at this
  exact this

end LinearDifferentialOperator

namespace LinearDifferentialOperator

/--
[apply_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma apply_smul
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {c : ℝ}
  {u : (Fin n → ℝ) → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  L.apply (c • u) = c • L.apply u := by
-- proof
  have := (L.toLinearMap hlin).map_smul c u
  simp only [toLinearMap_apply] at this
  exact this

end LinearDifferentialOperator

namespace LinearDifferentialOperator

/--
[apply_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma apply_sum
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {s : Finset ι}
  {f : ι → ((Fin n → ℝ) → ℝ)}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  L.apply (∑ i ∈ s, f i) = ∑ i ∈ s, L.apply (f i) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    simp only [apply, Pi.zero_apply]
    have h0 : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      multiIndexDeriv α.1 (0 : (Fin n → ℝ) → ℝ) x = 0 := by
      intro α
      have := hlin α 0 0 (0 : (Fin n → ℝ) → ℝ) 0 x
      simp only [zero_smul, add_zero, zero_mul] at this
      linarith
    simp only [h0, mul_zero, Finset.sum_const_zero]
  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, L.apply_add hlin, ih, Finset.sum_insert hna]

end LinearDifferentialOperator

namespace LinearDifferentialOperator

/--
[apply_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma apply_sub
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {u v : (Fin n → ℝ) → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  L.apply (u - v) = L.apply u - L.apply v := by
-- proof
  have : u - v = u + (-1 : ℝ) • v := by simp [sub_eq_add_neg, neg_smul, one_smul]
  rw [this, L.apply_add hlin, L.apply_smul hlin]
  simp [sub_eq_add_neg, neg_smul, one_smul]

end LinearDifferentialOperator

namespace LinearDifferentialOperator

/--
[linearity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma linearity
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {a b : ℝ}
  {u v : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
-- imply
  L.apply (a • u + b • v) x = a * L.apply u x + b * L.apply v x := by
-- proof
  simp only [apply]
  simp_rw [hlin _ a b u v x, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> (congr 1; funext α; ring)

end LinearDifferentialOperator

/--
[superposition_principle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma superposition_principle
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {M : ℕ}
  {u : Fin M → ((Fin n → ℝ) → ℝ)}
  {c : Fin M → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
  (hsol : ∀ i, L.apply (u i) = 0) :
-- imply
  L.apply (∑ i, c i • u i) = 0 := by
-- proof
  rw [L.apply_sum hlin]
  simp only [L.apply_smul hlin, hsol, smul_zero, Finset.sum_const_zero]

/--
[inhomogeneous_solution_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean)
-/
@[path]
lemma inhomogeneous_solution_set
  {n N : ℕ}
  {L : LinearDifferentialOperator n N}
  {f : (Fin n → ℝ) → ℝ}
  {u_I : (Fin n → ℝ) → ℝ}
-- given
  (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N }, ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), multiIndexDeriv α.1 (a • u + b • v) x = a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x)
  (hI : L.apply u_I = f) :
-- imply
  {w : (Fin n → ℝ) → ℝ | L.apply w = f} = {w | ∃ u_H, L.apply u_H = 0 ∧ w = u_I + u_H} := by
-- proof
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hw
    refine ⟨w - u_I, ?_, ?_⟩
    · have hsub := L.apply_sub hlin w u_I
      rwa [hw, hI, sub_self] at hsub
    · abel
  · rintro ⟨u_H, hH, rfl⟩
    have hadd := L.apply_add hlin u_I u_H
    rwa [hI, hH, add_zero] at hadd


-- created on 2026-10-23
