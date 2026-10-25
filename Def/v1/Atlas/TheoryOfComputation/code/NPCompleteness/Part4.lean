/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Instance.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part2


namespace CookLevin

open TuringMachine NPCompleteness

/-- An NTM that decides `ThreeSATLang` in one step: accepts `[φ]` iff `φ` is a
satisfiable 3CNF formula. Witnesses that `3SAT ∈ NP`. -/
noncomputable def threeSATNTM : NTM ThreeSATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Is3CNF ∧ γ.Satisfiable
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

/-- Existential witness that `ThreeSATLang` is decided by a polynomial-time NTM,
unfolding the definition of `InNP`. -/
def maxVarSucc : BoolFormula → ℕ
  | .var n => n + 1
  | .trueConst | .falseConst => 0
  | .not φ => maxVarSucc φ
  | .and φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)
  | .or φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)

/-- Build a 3-literal clause `l₁ ∨ l₂ ∨ l₃` (right-associated). -/
def mk3Clause (l₁ l₂ l₃ : BoolFormula) : BoolFormula :=
  .or l₁ (.or l₂ l₃)

/--
Core of the **Tseitin transformation**. Given a formula `φ` and a fresh-variable
counter, produces `(rootVar, clauses, fresh')` where:
- `rootVar` is a variable whose truth value tracks `φ.eval σ` under any
  satisfying assignment of the clauses;
- `clauses` is a list of 3-clauses encoding the gates of `φ`;
- `fresh'` is the next available fresh variable index.
This is the standard linear-size CNF (in fact 3CNF) encoding of an arbitrary
Boolean formula introducing one auxiliary variable per subformula.
-/
def tseitinAux : BoolFormula → ℕ → (ℕ × List BoolFormula × ℕ)
  | .var n, fresh => (n, [], fresh)
  | .trueConst, fresh =>

    (fresh, [mk3Clause (.var fresh) (.var fresh) (.var fresh)], fresh + 1)
  | .falseConst, fresh =>

    (fresh, [mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))],
     fresh + 1)
  | .not φ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let z := fresh1


    (z, clsφ ++ [mk3Clause (.var vφ) (.var z) (.var z),
                  mk3Clause (.not (.var vφ)) (.not (.var z)) (.not (.var z))],
     fresh1 + 1)
  | .and φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.not (.var z)),
      mk3Clause (.not (.var vφ)) (.var vψ) (.not (.var z)),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)
  | .or φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.var z),
      mk3Clause (.not (.var vφ)) (.var vψ) (.var z),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)

/-- Conjoin a list of clauses into a single CNF formula (returns a dummy 3-clause if empty,
keeping the result a valid 3CNF). -/
def conjoinClauses : List BoolFormula → BoolFormula
  | [] => mk3Clause (.var 0) (.var 0) (.var 0)
  | [c] => c
  | c :: cs => .and c (conjoinClauses cs)

/--
**Tseitin transformation**: convert any Boolean formula `φ` into an
equisatisfiable 3CNF formula. Returns the conjunction of the clauses generated
by `tseitinAux` together with a clause forcing the root variable to be true.
-/
def tseitinTransform (φ : BoolFormula) : BoolFormula :=
  let fresh := maxVarSucc φ
  let (rootVar, clauses, _) := tseitinAux φ fresh
  let rootClause := mk3Clause (.var rootVar) (.var rootVar) (.var rootVar)
  conjoinClauses (clauses ++ [rootClause])

/-- The reduction function from `SATLang` to `ThreeSATLang`: applies the Tseitin
transformation to a singleton input `[φ]`. -/
def satTo3SATFn : List BoolFormula → List BoolFormula
  | [φ] => [tseitinTransform φ]
  | _ => []

end CookLevin
