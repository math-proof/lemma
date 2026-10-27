import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Def.Dynamics.MarkovDecisionProcess.Part5
import Def.Dynamics.MdpHistory
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


variable (S : Type u) (A : Type v) in
abbrev Hist.OfLength (t : ℕ) := {h : Hist S A // h.length = t}

