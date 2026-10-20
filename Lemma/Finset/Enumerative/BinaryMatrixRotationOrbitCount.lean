import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BinaryMatrixRotationOrbitCount
open scoped BigOperators
open MetaMathlibExt


/--
[binaryMatrixRotationOrbitCount](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean)
-/
@[path]
private lemma binaryMatrixRotationOrbitCount_eq
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (Finset.univ.filter (fun x : Fin m → Fin n → Bool =>
    ∀ i : Fin m, ∀ j : Fin n,
    (∑ r : Fin m, ∑ s : Fin n,
    (if x r s = true then 1 else 0) * 2 ^ (r.val * n + s.val)) ≤
    (∑ r : Fin m, ∑ s : Fin n,
    (if x (r + i) (s + j) = true then 1 else 0) *
    2 ^ (r.val * n + s.val)))).card =
    (∑ c ∈ m.divisors, ∑ d ∈ n.divisors,
    Nat.totient c * Nat.totient d *
    2 ^ ((m * n) / Nat.lcm c d)) / (m * n) := by
-- proof
  apply MetaMathlibExt.binaryMatrixRotationOrbitCount m n hm hn


-- created on 2026-10-20
