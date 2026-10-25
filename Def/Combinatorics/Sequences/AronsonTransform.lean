/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/AronsonTransform.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat


namespace MetaMathlibExt

noncomputable def aronsonChoose (n₀ : ℕ) (β : ℕ → ℕ) (l : List ℕ) : ℕ :=
  if _ : l = [] then
    sInf {m | n₀ ≤ m ∧ ((m = n₀) ↔ m ∈ Set.range β)}
  else
    let i := l.length - 1
    let n := n₀ + i + 1
    let c := l.getLastD n₀
    let Q : Prop := ∃ j, j ≤ i ∧ l[j]? = some n
    sInf {m | c < m ∧ (((Q ∨ m = n) ↔ m ∈ Set.range β))}

noncomputable def aronsonHist (n₀ : ℕ) (β : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | (k + 1) => (aronsonHist n₀ β k) ++ [aronsonChoose n₀ β (aronsonHist n₀ β k)]

noncomputable def aronsonSeq (n₀ : ℕ) (β : ℕ → ℕ) (k : ℕ) : ℕ :=
  aronsonChoose n₀ β (aronsonHist n₀ β k)

end MetaMathlibExt
