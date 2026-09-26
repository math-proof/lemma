import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import sympy.stats.markov_decision_process

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

universe u v

-- a history of states and actions (MDPLib: `Hist M`)
inductive Hist (S : Type u) (A : Type v) : Type (max u v) where
  | init : S → Hist S A
  | foll : Hist S A → A → S → Hist S A

namespace Hist

variable {S : Type u} {A : Type v}

-- number of actions taken (MDPLib: `Hist.length`)
def length : Hist S A → ℕ
  | init _ => 0
  | foll h _ _ => h.length + 1

-- the last state (MDPLib: `Hist.last`, `MDP.histToState`)
def last : Hist S A → S
  | init s => s
  | foll _ _ s => s

end Hist

-- the prefix of length k (MDPLib: `Hist.prefix`)
def Hist.prefix {S : Type u} {A : Type v} (k : ℕ) : Hist S A → Hist S A
  | init s => init s
  | foll hp a s => if hp.length + 1 ≤ k then foll hp a s else hp.prefix k

namespace Hist

variable {S : Type u} {A : Type v}

-- whether the first history is a prefix of the second (MDPLib: `isPrefix`)
def isPrefix [DecidableEq S] [DecidableEq A] : Hist S A → Hist S A → Bool
  | init s₁, init s₂ => s₁ = s₂
  | init s₁, foll hp _ _ => isPrefix (init s₁) hp
  | foll _ _ _, init _ => false
  | foll h₁ a₁ s₁, foll h₂ a₂ s₂ =>
    if h₂.length < h₁.length then false
    else if h₁.length < h₂.length then isPrefix (foll h₁ a₁ s₁) h₂
    else a₁ = a₂ ∧ s₁ = s₂ ∧ isPrefix h₁ h₂

-- a state as a history of length 0 (MDPLib: `stateToHistEmbedding`)
@[simps]
def initEmbedding : S ↪ Hist S A := ⟨init, fun _ _ h => init.inj h⟩

-- extending a history by an action and a state (MDPLib: `tupleToHistEmbedding`)
@[simps]
def follEmbedding : Hist S A × A × S ↪ Hist S A :=
  ⟨fun x => foll x.1 x.2.1 x.2.2, fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by
    obtain ⟨rfl, rfl, rfl⟩ := foll.inj h
    rfl⟩

variable [Fintype S] [Fintype A]

-- all histories that follow h for t decisions (MDPLib: `histories`, `ℋ`)
def histories (h : Hist S A) : ℕ → Finset (Hist S A)
  | 0 => {h}
  | t + 1 => (histories h t ×ˢ Finset.univ ×ˢ Finset.univ).map follEmbedding

-- all histories of length t (MDPLib: `MDP.historiesHorizon`, `ℋₜ`)
variable (S A) in
def historiesHorizon : ℕ → Finset (Hist S A)
  | 0 => Finset.univ.map initEmbedding
  | t + 1 => (historiesHorizon t ×ˢ Finset.univ ×ˢ Finset.univ).map follEmbedding

end Hist

-- histories of length t (MDPLib: `MDP.HistOfLength`)
variable (S : Type u) (A : Type v) in
abbrev Hist.OfLength (t : ℕ) := {h : Hist S A // h.length = t}

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

-- (MDPLib: `instance : Fintype (M.HistOfLength t)`)
instance instFintypeOfLength [Fintype S] [Fintype A] : (t : ℕ) → Fintype (OfLength S A t)
  | 0 => Fintype.ofEquiv S ofLengthZeroEquiv.symm
  | t + 1 =>
    have := instFintypeOfLength t
    Fintype.ofEquiv _ (ofLengthSuccEquiv t).symm

end Hist

-- the histories of an MDP with state space S and action space A
abbrev MDPSpec.History {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A] (_ : MDPSpec S A) : Type (max u v) :=
  Hist S A
