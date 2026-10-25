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
import Inductive.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part4


namespace CookLevin

open TuringMachine NPCompleteness

/-- Number of vertices `n` in the graph encoded by a `HampathSymbol`. -/
def HampathSymbol.numVertices : HampathSymbol → ℕ
  | .mk n _ _ _ => n

/-- The underlying directed graph on `Fin (numVertices sym)` encoded by a `HampathSymbol`. -/
def HampathSymbol.toDigraph : (sym : HampathSymbol) → DiGraph (Fin sym.numVertices)
  | .mk _ edges _ _ => ⟨fun u v => edges u v = true⟩

/-- Source vertex `s` of the encoded HAMPATH instance. -/
def HampathSymbol.source : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ s _ => s

/-- Target vertex `t` of the encoded HAMPATH instance. -/
def HampathSymbol.target : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ _ t => t

/-- The encoded instance is a YES instance of HAMPATH iff its graph has a
Hamiltonian path from `source` to `target`. -/
def HampathSymbol.isYesInstance (sym : HampathSymbol) : Prop :=
  sym.toDigraph.HasHamiltonianPath (Fin sym.numVertices) sym.source sym.target

/-- `HampathLang` is the language of one-symbol-encoded YES instances of HAMPATH. -/
def HampathLang : Set (List HampathSymbol) :=
  {w | ∃ sym : HampathSymbol, w.head? = some sym ∧ sym.isYesInstance}

end CookLevin
