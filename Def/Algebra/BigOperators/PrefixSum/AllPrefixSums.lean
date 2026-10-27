import Initialize.Tactic.Attr.Basic
import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part3


-- Define the all-prefix-sums function
def all_prefix_sums [Inhabited α] [OPlus α] (s : List α) (t : α := default) : List α :=
  match s, t with
  | [], _  => []
  | s₀ :: s, sum => (sum ⊕ s₀) :: all_prefix_sums s (sum ⊕ s₀)


