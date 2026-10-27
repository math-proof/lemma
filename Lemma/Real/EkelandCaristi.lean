import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Calculus.EkelandCaristi
open Set


/--
[EkelandCaristi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Variational/EkelandCaristi.lean)
-/
@[path]
private lemma ekeland_variational_principle_general_is
  [MetricSpace X] [CompleteSpace X]
-- given
  (hf_lsc : LowerSemicontinuous f)
  (hf_bdd : BddBelow (range f))
  (hε : 0 < ε)
  (hx₀ : ∀ x, f x₀ ≤ f x + ε) :
-- imply
  ∃ xε : X, f xε ≤ f x₀ ∧ dist xε x₀ ≤ 1 ∧
    ∀ y, y ≠ xε → f xε < f y + ε * dist xε y := by
-- proof
  apply MetaMathlibExt.ekeland_variational_principle_general hf_lsc hf_bdd hε hx₀

/--
[EkelandCaristi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Variational/EkelandCaristi.lean)
-/
@[path]
private lemma ekeland_variational_principle_is
  [MetricSpace X] [CompleteSpace X] [Nonempty X]
-- given
  (hf_lsc : LowerSemicontinuous f)
  (hf_bdd : BddBelow (range f))
  (hε : 0 < ε)
  (hx₀ : ∀ x, f x₀ ≤ f x + ε) :
-- imply
  ∃ xε : X, f xε ≤ f x₀ ∧ dist xε x₀ ≤ 1 ∧
    ∀ y, y ≠ xε → f xε < f y + ε * dist xε y := by
-- proof
  apply MetaMathlibExt.ekeland_variational_principle hf_lsc hf_bdd hε hx₀

/--
[EkelandCaristi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Variational/EkelandCaristi.lean)
-/
@[path]
private lemma caristi_fixed_point_is
  [MetricSpace X] [CompleteSpace X] [Nonempty X]
  {T : X → X}
-- given
  (hφ_lsc : LowerSemicontinuous φ)
  (hφ_bdd : BddBelow (range φ))
  (hT : ∀ x, dist x (T x) ≤ φ x - φ (T x)) :
-- imply
  ∃ x, T x = x := by
-- proof
  apply MetaMathlibExt.caristi_fixedPoint hφ_lsc hφ_bdd hT


-- created on 2026-10-11
