/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part41
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagReflectConfigEquiv
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagPlaneConfigBy n hn k l ≃ ZagPlaneConfigBy n hn l k where
  toFun := zagReflectConfig n hn k l
  invFun := zagReflectConfig n hn l k
  left_inv := zagReflectConfig_involutive n hn k l
  right_inv := zagReflectConfig_involutive n hn l k

noncomputable def zagReflectedTotalEquivOriginalTotal
    (n k : ℕ) (hn : 0 < n) :
    ZagReflectedTotal n hn k ≃ ZagOriginalTotal n hn 1 k :=
  Equiv.sigmaCongr (zagReflectConfigEquiv n hn k 1) fun _q => Equiv.refl _

end MetaMathlibExt
