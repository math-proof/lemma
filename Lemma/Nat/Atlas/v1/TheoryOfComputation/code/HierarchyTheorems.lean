import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems
open TuringMachine HierarchyTheorems SpaceComplexity
open SpaceComplexity


namespace HierarchyTheorems

/--
[IsLittleO.isBigO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma IsLittleO.isBigO
  {g f : ℕ → ℕ}
-- given
  (h : IsLittleO g f) :
-- imply
  IsBigO g f := by
-- proof
  obtain ⟨n₀, hn₀⟩ := h 1 Nat.one_pos
  exact ⟨1, n₀, Nat.one_pos, fun n hn => by
    simp only [one_mul]
    exact Nat.le_of_lt (by simpa using hn₀ n hn)⟩
end HierarchyTheorems


namespace TuringMachine

/--
[isBigO_div_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma isBigO_div_log
  {f : ℕ → ℕ} :
-- imply
  IsBigO (fun n => f n / Nat.log 2 (f n)) f :=
-- proof
  ⟨1, 0, Nat.one_pos, fun n _ => by simp only [one_mul]; exact Nat.div_le_self _ _⟩
end TuringMachine
open TuringMachine HierarchyTheorems


/--
[TM.run_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma TM.run_add
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {n m : ℕ} :
-- imply
  M.run c (n + m) = M.run (M.run c n) m := by
-- proof
  induction m with
  | zero => simp [TM.run]
  | succ m ih => simp [TM.run, ih]

/--
[tm_swap_step_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma tm_swap_step_eq
  {Q Γ : Type}
  [DecidableEq Q]
  {sim : TM Q Γ}
  {c : Config Q Γ} :
-- imply
  let D : TM Q Γ := { sim with qAccept := sim.qReject qReject := sim.qAccept qReject_ne_qAccept := Ne.symm sim.qReject_ne_qAccept } D.step c = sim.step c := by
-- proof
  simp only [TM.step]
  congr 1
  exact propext Or.comm

/--
[tm_swap_run_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma tm_swap_run_eq
  {Q Γ : Type}
  [DecidableEq Q]
  {sim : TM Q Γ}
  {c : Config Q Γ}
  {n : ℕ} :
-- imply
  let D : TM Q Γ := { sim with qAccept := sim.qReject qReject := sim.qAccept qReject_ne_qAccept := Ne.symm sim.qReject_ne_qAccept } D.run c n = sim.run c n := by
-- proof
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    simp only [TM.run]
    rw [ih]
    exact tm_swap_step_eq sim (sim.run c n)
/--
**Existence of a time-diagonalizer.** From a time-constructible bound `f` we
construct a decider `D` running in time `O(f)` whose language differs from the
language of every decider `M` running in time `O(f(n)/log(f(n)))`. `D` is built by
swapping accept/reject on the universal simulator from
`universal_simulation_overhead`, so that it accepts exactly the encodings rejected
by the simulator — a Cantor-style diagonalization within `TIME(f)`.
-/

namespace SpaceComplexity

/--
[diagLang_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma diagLang_iff
  {Γ : Type}
  {encode : TMDesc Γ → List Γ}
  {d : TMDesc Γ}
-- given
  (h_inj : Function.Injective encode) :
-- imply
  encode d ∈ diagLang encode ↔ ¬d.machine.accepts (encode d) := by
-- proof
  simp only [diagLang, Set.mem_setOf_eq]
  constructor
  · intro h; exact h d rfl
  · intro hna d' heq
    have := h_inj heq; subst this; exact hna

end SpaceComplexity

namespace SpaceComplexity

/--
[diagLang_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean)
-/
@[path]
lemma diagLang_ne
  {Γ : Type}
  {encode : TMDesc Γ → List Γ}
  {d : TMDesc Γ}
-- given
  (h_inj : Function.Injective encode) :
-- imply
  diagLang encode ≠ d.machine.language := by
-- proof
  intro heq
  have hiff := diagLang_iff h_inj d
  have hmem : encode d ∈ diagLang encode ↔ d.machine.accepts (encode d) := by
    rw [heq]; exact Iff.rfl
  by_cases ha : d.machine.accepts (encode d)
  · exact (hiff.mp (hmem.mpr ha)) ha
  · exact ha (hmem.mp (hiff.mpr ha))
end SpaceComplexity
/--
**Space-bounded universal simulation.** Given a space-constructible bound `f`,
there exists an injective encoding of TM descriptions and a single decider `D`
whose language is the diagonal language `diagLang encode`, runs in space `O(f)`,
and such that every TM `M` running in space `o(f)` is represented (up to language)
by some description `d`. This is the space analogue of
`universal_simulation_overhead` and the engine of the Space Hierarchy Theorem.
-/
namespace SpaceComplexity
/--
**Existence of a space-diagonalizer.** From a space-constructible bound `f` we
build a TM `D` that runs in space `O(f)` and whose language differs from the
language of every TM `M` running in space `g = o(f)`. Combines `sim_overhead`
with `diagLang_ne` to produce the witness used in the Space Hierarchy Theorem.
-/
end SpaceComplexity
open SpaceComplexity
namespace OracleComputation
open TuringMachine



-- created on 2026-10-23
