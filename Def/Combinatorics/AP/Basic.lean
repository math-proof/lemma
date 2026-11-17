/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


/-- A set is an arithmetic progression of length `l` with first term `a` and difference `d`. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length `l` for some first term and difference. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

variable {s : Set α} {l : ℕ∞}

end Set.IsAPOfLength

/-- A list is an arithmetic progression of length `l` with first term `a` and difference `d`. -/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨
    s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- A list is an arithmetic progression of length `l` for some first term and difference. -/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- `f` contains a monotone arithmetic progression of length `k`. -/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

/-- A set is free of nontrivial arithmetic progressions of length `l`. -/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/-- A finite set is free of nontrivial arithmetic progressions of length `l`. -/
def Finset.IsAPOfLengthFree (s : Finset α) (l : ℕ∞) : Prop :=
  (s : Set α).IsAPOfLengthFree l

