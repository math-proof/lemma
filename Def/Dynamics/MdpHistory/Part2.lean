import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Def.Dynamics.MarkovDecisionProcess.Part5
import Abbrev.Dynamics.MdpHistory
universe u v

/-!
# Histories of a Markov decision process

Ported from MDPLib `MDPLib/MDP/Histories.lean`.

MDPLib fixes an MDP `M` with states `Fin M.S` and actions `Fin M.A` and indexes histories by
it; the history constructions only use the state and action types, so here they are generic
in `S` and `A` (for an `M : MDPSpec S A`, `M.History` is `Hist S A`).

* `Hist S A`: `init s` or `foll h a s` (history `h`, then action `a`, then state `s`).
* `Hist.length` (number of actions), `Hist.last` (last state), `Hist.prefix k`,
  `Hist.isPrefix`.
* `Hist.histories h t`: all histories that follow `h` for `t` decisions;
  `Hist.historiesHorizon S A t`: all histories of length `t`.
* `Hist.OfLength S A t`: histories of length `t`, a `Fintype` via
  `OfLength S A 0 ≃ S` and `OfLength S A (t + 1) ≃ OfLength S A t × A × S`.
  This replaces MDPLib's explicit index maps `MDP.idxToHist` / `MDP.histToIdx` (whose
  inverse laws were left as `sorry`).
-/


namespace Hist

variable {S : Type u} {A : Type v}

-- histories of length 0 are states
def ofLengthZeroEquiv : OfLength S A 0 ≃ S where
  toFun h := h.1.last
  invFun s := ⟨init s, rfl⟩
  left_inv := fun ⟨h, hh⟩ => by
    cases h with
    | init s => rfl
    | foll _ _ _ => simp [length] at hh
  right_inv := fun _ => rfl

-- a history of length t + 1 is a history of length t, an action and a state
def ofLengthSuccEquiv (t : ℕ) : OfLength S A (t + 1) ≃ OfLength S A t × A × S where
  toFun
    | ⟨init _, hh⟩ => absurd hh (by simp [length])
    | ⟨foll h a s, hh⟩ => (⟨h, Nat.succ.inj hh⟩, a, s)
  invFun x := ⟨foll x.1.1 x.2.1 x.2.2, congrArg (· + 1) x.1.2⟩
  left_inv := fun ⟨h, hh⟩ => by
    cases h with
    | init s => simp [length] at hh
    | foll _ _ _ => rfl
  right_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl

end Hist
