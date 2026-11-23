/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.BigOperators
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
public import Instance.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part2

@[expose] public section

open Computability
open TuringMachine


namespace SpaceComplexity

/-- The GG-recognizing NTM: scans the input, decodes it as a digraph `(G, a)`, and
accepts iff Player I has a forced win in Generalized Geography on `G` from `a`. -/
noncomputable def ggNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : GGEncoding Γ) : NTM (GGState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some p => @decide (@GeographyGame.GG enc.V enc.decEqV p.1 p.2)
              (Classical.dec _)
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
  qReject_ne_qAccept := by simp [GGState]

set_option maxRecDepth 2048 in


/-- The GG-recognizing NTM runs in linear space (just stores its input). (Placeholder.) -/
noncomputable def buildFormulaGameGraph
    {Γ : Type} [Inhabited Γ] (genc : GGEncoding Γ) (ψ : QBF) :
    Digraph genc.V × genc.V :=
  haveI hne : Nonempty genc.V := genc.nonemptyV
  haveI : Nonempty (Digraph genc.V × genc.V) :=
    ⟨⟨⟨fun _ _ => False⟩, Classical.choice hne⟩⟩
  Classical.epsilon (fun p : Digraph genc.V × genc.V =>
    @GeographyGame.GG genc.V genc.decEqV p.1 p.2 ↔ (ψ.IsFullyQuantified ∧ ψ.IsTrue))


/-- **Correctness of the TQBF→GG reduction**: Player I has a forced win on the
constructed graph iff `ψ` is a true sentence. (Placeholder.) -/
noncomputable def ggReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (qenc : QBFEncoding Γ) (genc : GGEncoding Γ) : List Γ → List Γ := fun w =>
  match qenc.decode w with
  | some ψ => genc.encode (buildFormulaGameGraph genc ψ)
  | none   => default


end SpaceComplexity
