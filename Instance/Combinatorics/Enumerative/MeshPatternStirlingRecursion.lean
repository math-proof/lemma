/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.MeshPatternStirlingRecursion

@[expose] public section

section

namespace MetaMathlibExt

instance decMatchPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    DecidablePred (MatchPred r σ) := by
  intro i
  unfold MatchPred
  infer_instance

instance decZeroPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    Decidable (ZeroPred r σ) := by
  unfold ZeroPred
  infer_instance

end MetaMathlibExt
end
