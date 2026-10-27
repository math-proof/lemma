import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeABridge
open TypeABridge


namespace Definitions
end Definitions
namespace TypeABridge

/--
[glnCoxeterMatrixA_eq_typeA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeABridge.lean)
-/
@[path]
private lemma glnCoxeterMatrixA_eq_typeA
  {n : ℕ} :
-- imply
  glnCoxeterMatrixA n = (CoxeterMatrix.A n).M := by
-- proof
  ext i j
  simp only [glnCoxeterMatrixA, CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
      simp [hadj, hadj']
    · have hadj' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      intro h; exact hadj h.symm
      simp [hadj, hadj']

end TypeABridge


-- created on 2026-10-24
