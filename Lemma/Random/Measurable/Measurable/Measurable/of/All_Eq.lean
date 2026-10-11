import sympy.stats.policy_trajectory
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.Measurable.Measurable.Measurable.of.All_Eq |
| And.left | Random.Measurable.of.All_Eq.fst |
| And.right.left | Random.Measurable.of.All_Eq.snd.fst |
| And.right.right | Random.Measurable.of.All_Eq.snd.snd |

The reward / state / action coordinates of the trajectory are measurable.
-/
@[path, And.left, And.right.left, And.right.right]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (k : ℕ) :
-- imply
  Measurable (r k) ∧ Measurable (s k) ∧ Measurable (a k) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  exact ⟨measurable_fst.comp (measurable_pi_apply k),
    measurable_snd.fst.comp (measurable_pi_apply k),
    measurable_snd.snd.comp (measurable_pi_apply k)⟩


-- created on 2026-10-10
