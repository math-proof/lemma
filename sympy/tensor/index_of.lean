import sympy.Basic

/-!
SymPy's `index[v](x[:n])` (`Lemma/Finset/Eq/of/Eq/index/indexOf_Get.py`): the first position of the value `v`
among `x[0], …, x[n-1]`, and `n` when `v` does not occur (the `List.idxOf` convention).
-/

namespace IndexOf

def index {α : Type*} [DecidableEq α] (v : α) (x : ℕ → α) (n : ℕ) : ℕ :=
  ((List.range n).map x).idxOf v

end IndexOf
