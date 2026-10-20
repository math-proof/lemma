import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MeshPatternStirlingRecursion
open MetaMathlibExt


/--
[meshPatternCount_stirlingRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma meshPatternCount_stirlingRecursion_eq
  {k n j : ℕ}
-- given
  (hk : 1 < k)
  (hn : k ≤ n)
  (hj : 0 < j) :
-- imply
  let isMeshMatch : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Fin m → Prop := by
-- proof
  apply MetaMathlibExt.meshPatternCount_stirlingRecursion k n j hk hn hj


-- created on 2026-10-20
