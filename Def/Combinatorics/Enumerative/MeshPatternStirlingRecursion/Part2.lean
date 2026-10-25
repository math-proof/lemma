/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Instance.Combinatorics.Enumerative.MeshPatternStirlingRecursion


section

namespace MetaMathlibExt

/-- Canonical mesh-pattern count statistic: number of `MatchPred` positions plus one when
`ZeroPred` holds. Shared by the recursion and the coefficient theorem. -/
def meshN {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter (MatchPred r σ)).card + if ZeroPred r σ then 1 else 0

/-- Canonical mesh-pattern counting polynomial: `∑ σ, X ^ meshN r σ`. Shared by the
recursion and the coefficient theorem. -/
noncomputable def PolyN : ℕ → ℕ → Polynomial ℕ := fun m r =>
  ∑ σ : Equiv.Perm (Fin m), (Polynomial.X : Polynomial ℕ) ^ meshN r σ

/-- Mirror of the `C` let-binding. -/
noncomputable def CoefN : ℕ → ℕ → ℕ → ℕ := fun m r s => (PolyN m r).coeff s

/-- Insertion map: plant value `0` at position `p`, shifting `τ` up by one elsewhere. -/
def Phi (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m.succ)) :=
  (Equiv.Perm.decomposeFin.symm (0, τ)) * p.cycleRange

end MetaMathlibExt
end
