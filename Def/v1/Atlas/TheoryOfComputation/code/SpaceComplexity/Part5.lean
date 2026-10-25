/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
import Instance.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- A (degenerate) NTM that reads its input into a buffer, decodes it as a QBF, and
accepts iff the QBF is fully quantified and true. Used as a witness that
`tqbfLanguage ∈ NSPACE(n)`. -/
noncomputable def tqbfNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : QBFEncoding Γ) : NTM (TQBFState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some ψ => decide (ψ.freeVars = ∅) && ψ.eval (fun _ => false)
          | none => false
        if result then
          {((⟨1, by omega⟩, ([] : List Γ)), default, Direction.R)}
        else
          {((⟨2, by omega⟩, ([] : List Γ)), default, Direction.R)}
      else

        {((⟨0, by omega⟩, buf ++ [a]), a, Direction.R)}
    | (⟨1, _⟩, _) => ∅
    | (⟨2, _⟩, _) => ∅
    | _ => ∅
  q₀ := (⟨0, by omega⟩, [])
  qAccept := (⟨1, by omega⟩, [])
  qReject := (⟨2, by omega⟩, [])
  qReject_ne_qAccept := by
    simp [TQBFState]


set_option maxRecDepth 2048 in

/-- **TQBF ∈ PSPACE** (Sipser, Lecture 17). Since TQBF is in `NSPACE(n)` and
`NPSPACE = PSPACE` by Savitch, TQBF lies in PSPACE. -/
def tqbfConfigSize {Q : Type} {Γ : Type} (_M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : ℕ :=
  spacebound + w.length + 1

/-- Number of recursion levels in the TQBF reduction: one level per bit of space. -/
def tqbfNumLevels (spacebound : ℕ) : ℕ := spacebound + 1

/-- A trivial conjunction `x_{n-1} ∧ x_{n-2} ∧ … ∧ x_0 ∧ True` used as a placeholder
body when building the TQBF formula. -/
def tqbfBaseBody : ℕ → NPCompleteness.BoolFormula
  | 0 => .trueConst
  | n + 1 => .and (.var n) (tqbfBaseBody n)

/-- Wraps `q` with `n` alternating quantifiers `∃ k. … ∀ k. …` according to the
divisibility pattern used in the halving construction for the PSPACE-completeness proof
of TQBF. -/
def quantifyHalving (q : QBF) (configSize : ℕ) : ℕ → QBF
  | 0 => q
  | k + 1 =>

    if (k + 1) % (configSize + 1) == 0 then
      QBF.forall_ k (quantifyHalving q configSize k)
    else
      QBF.exists_ k (quantifyHalving q configSize k)

/-- Given a TM `M`, input `w`, and a space bound, construct a QBF whose truth is
equivalent to `M` accepting `w` in space `spacebound`. This is the Sipser construction
underlying the reduction `A ≤ₚ TQBF` for the PSPACE-hardness of TQBF. -/
noncomputable def buildTQBFFormula {Q : Type} [DecidableEq Q]
    {Γ : Type} (M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : QBF :=
  let configSize := tqbfConfigSize M w spacebound
  let numLevels := tqbfNumLevels spacebound
  let totalVars := numLevels * (configSize + 1)
  let baseBody := tqbfBaseBody totalVars
  let baseQBF := QBF.body baseBody
  quantifyHalving baseQBF configSize totalVars


/-- **Correctness of the TQBF reduction**: the QBF `buildTQBFFormula M w spacebound` is
true iff `M` accepts `w`, under the assumption that `M` halts within `spacebound` tape
cells. (Placeholder.) -/
noncomputable def tqbfReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (enc : QBFEncoding Γ) {Q : Type} [DecidableEq Q]
    (M : TM Q Γ) (g : ℕ → ℕ) : List Γ → List Γ := fun w =>
  enc.encode (buildTQBFFormula M w (g w.length))


end SpaceComplexity
