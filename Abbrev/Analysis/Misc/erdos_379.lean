import Mathlib
import Theorem.Analysis.Misc.erdos_379
open Nat

/-! Formalizing a proof of Erdos problem \#379, arising from conversations between Stijn Cambie, Vjeko Kovac, and Terry Tao.  See the discussion at https://www.erdosproblems.com/forum/thread/379 -/


noncomputable abbrev S (n:ℕ) : ℕ := sSup { r | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ (n.choose k) }

