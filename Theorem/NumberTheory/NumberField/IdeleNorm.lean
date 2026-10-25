/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean -/

/-
Author: @toskua, Avocado
-/

import Abbrev.NumberTheory.NumberField.Idele.Part2
import Lemma.Nat.NumberField.Idele
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# Norm-one ideles

This module defines the global adelic norm (modulus) on the native
restricted-product idele group, defines its norm-one kernel, and proves
principal ideles lie in it by the number-field product formula.

ATLAS NumberTheoryI N544 / Definition 26.7. This is distinct from the
relative extension norm between idele groups.
-/


noncomputable section

namespace NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

theorem finite_mulSupport_norm (a : FiniteIdeleGroup (𝓞 K) K) :
    (Function.mulSupport (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖(a v : v.adicCompletion K)‖)).Finite := by
  have hev := a.2
  rw [Filter.eventually_cofinite] at hev
  apply Set.Finite.subset hev
  intro v hv
  rw [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  by_contra hmem
  have hvS : a v ∈ localIntegralUnitSubgroup (𝓞 K) K v := hmem
  rw [mem_localIntegralUnitSubgroup] at hvS
  obtain ⟨hint, hinv⟩ := hvS
  have h1 : ‖(a v : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hint
  have h2 :
      ‖(((a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hinv
  have hmul : ‖(a v : v.adicCompletion K)‖ *
      ‖(((a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
    rw [← norm_mul]
    change ‖(((a v) * (a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1
    simp
  have hge : 1 ≤ ‖(a v : v.adicCompletion K)‖ := by
    by_contra hlt
    push Not at hlt
    linarith [mul_le_mul_of_nonneg_left h2
      (norm_nonneg (a v : v.adicCompletion K))]
  have heq : ‖(a v : v.adicCompletion K)‖ = 1 := le_antisymm h1 hge
  exact hv heq

end NumberField.TopologicalIdeleGroup
end
