/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Theorem.Combinatorics.DensityHalesJewett.Part13
import Lemma.Finset.DensityHalesJewett
import Mathlib.Tactic
/-!
# Szemerédi's theorem

This file proves the finitary density form of Szemerédi's theorem.
-/


namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

open scoped Finset

def szemWeight {k M : ℕ} (x : Fin M → Fin k) : ℕ :=
  ∑ i, (x i : ℕ)

def szemWildcards {k M : ℕ} (l : Combinatorics.Line (Fin k) (Fin M)) :
    Finset (Fin M) :=
  {i | l.idxFun i = none}

def szemFixed {k M : ℕ} (l : Combinatorics.Line (Fin k) (Fin M)) : ℕ :=
  ∑ i ∈ (szemWildcards l)ᶜ, ((l.idxFun i).map fun x => (x : ℕ)).getD 0

end MathlibExt.Combinatorics.Additive.SzemerediWanted
