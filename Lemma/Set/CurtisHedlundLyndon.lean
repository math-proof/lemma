import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.CurtisHedlundLyndon
open MetaMathlibExt


/--
[curtis_hedlund_lyndon_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/CurtisHedlundLyndon.lean)
-/
@[path]
private lemma curtis_hedlund_lyndon_general_eq
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [TopologicalSpace B] [DiscreteTopology B]
  {F : (ℤ → A) → (ℤ → B)} :
-- imply
  (∃ (r : ℕ) (φ : (Fin (2 * r + 1) → A) → B), ∀ (x : ℤ → A) (n : ℤ),
    F x n = φ (fun i => x (n + ((i.val : ℤ) - (r : ℤ))))) ↔
    (Continuous F ∧ ∀ (x : ℤ → A) (k : ℤ), F (fun n => x (n + k)) = fun n => F x (n + k)) := by
-- proof
  apply MetaMathlibExt.curtis_hedlund_lyndon_general F

/--
[curtis_hedlund_lyndon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/CurtisHedlundLyndon.lean)
-/
@[path]
private lemma curtis_hedlund_lyndon_eq
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  {F : (ℤ → A) → (ℤ → B)} :
-- imply
  (∃ (r : ℕ) (φ : (Fin (2 * r + 1) → A) → B), ∀ (x : ℤ → A) (n : ℤ), F x n = φ
    (fun i => x (n + ((i.val : ℤ) - (r : ℤ))))) ↔
    (Continuous F ∧ ∀ (x : ℤ → A) (k : ℤ), F (fun n => x (n + k)) = fun n => F x (n + k)) := by
-- proof
  apply MetaMathlibExt.curtis_hedlund_lyndon F


-- created on 2026-10-20
