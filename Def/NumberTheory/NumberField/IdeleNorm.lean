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
import Theorem.NumberTheory.NumberField.IdeleNorm
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

/-- The adelic norm of an idele: archimedean factor times finite finprod factor. -/
noncomputable def adelicNorm : TopologicalIdeleGroup (𝓞 K) K →* ℝ :=
  show (InfiniteIdeleGroup K × FiniteIdeleGroup (𝓞 K) K) →* ℝ from
  { toFun a :=
      (∏ w : InfinitePlace K, ‖(a.1 w : w.Completion)‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖(a.2 v : v.adicCompletion K)‖
    map_one' := by
      change
        (∏ w : InfinitePlace K, ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ = 1
      have hinf : (∏ w : InfinitePlace K,
          ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) = 1 := by
        apply Finset.prod_eq_one
        intro w _
        change ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult = 1
        change ‖((1 : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult = 1
        simp
      have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) = 1 := by
        have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
            (fun _ => (1 : ℝ)) := by
          funext v
          change ‖((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1
          simp
        rw [hfun]
        exact finprod_one
      rw [hinf, hfin, mul_one]
    map_mul' := by
      intro a b
      have hinf : (∏ w : InfinitePlace K,
          ‖((((a.1 * b.1 : InfiniteIdeleGroup K) w : w.Completion)))‖ ^ w.mult) =
          (∏ w : InfinitePlace K, ‖((a.1 w : w.Completion))‖ ^ w.mult) *
            (∏ w : InfinitePlace K, ‖((b.1 w : w.Completion))‖ ^ w.mult) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro w _
        have hdef : (a.1 * b.1 : InfiniteIdeleGroup K) w = a.1 w * b.1 w := rfl
        rw [hdef, Units.val_mul, norm_mul, mul_pow]
      have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ =
            ‖((a.2 v : v.adicCompletion K))‖ * ‖((b.2 v : v.adicCompletion K))‖ := by
        intro v
        have hdef : (a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v = a.2 v * b.2 v := rfl
        rw [hdef, Units.val_mul, norm_mul]
      have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
          (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((a.2 v : v.adicCompletion K))‖) *
          (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((b.2 v : v.adicCompletion K))‖) := by
        have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
            (fun v => ‖((a.2 v : v.adicCompletion K))‖ *
              ‖((b.2 v : v.adicCompletion K))‖) := by
          funext v
          exact hfmul v
        rw [hfun]
        exact finprod_mul_distrib (finite_mulSupport_norm K a.2)
          (finite_mulSupport_norm K b.2)
      change
        (∏ w : InfinitePlace K,
          ‖(((a.1 * b.1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) *
          ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ =
          ((∏ w : InfinitePlace K, ‖((a.1 w : w.Completion))‖ ^ w.mult) *
            ∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
              ‖((a.2 v : v.adicCompletion K))‖) *
          ((∏ w : InfinitePlace K, ‖((b.1 w : w.Completion))‖ ^ w.mult) *
            ∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
              ‖((b.2 v : v.adicCompletion K))‖)
      rw [hinf, hfin]
      ring }

/-- Norm-one ideles: kernel of the adelic norm. -/
def normOneIdeles : Subgroup (TopologicalIdeleGroup (𝓞 K) K) :=
  (adelicNorm K).ker

end NumberField.TopologicalIdeleGroup
end
