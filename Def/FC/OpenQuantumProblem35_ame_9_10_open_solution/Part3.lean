/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def graphPhase {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1),
    G i j * x i * x j

def q2Label (a : Fin 2 → ZMod 2) (i : Fin 9) : ZMod 2 :=
  a 0 * (if i.1 ∈ ([0, 1, 3, 4, 6, 7] : List ℕ) then 1 else 0) +
  a 1 * (if i.1 ∈ ([0, 2, 3, 5, 6, 8] : List ℕ) then 1 else 0)

set_option maxRecDepth 10000 in

def q5Logical (a : Fin 2 → ZMod 2) : ZMod 5 :=
  ((a 0).val + 2 * (a 1).val : ℕ)

def binaryPhase (a : Fin 2 → ZMod 2) (u : Fin 9 → ZMod 2) : ZMod 2 :=
  graphPhase q2Cycle u + ∑ i, q2Label a i * u i

def quinaryWord (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : Fin 10 → ZMod 5
  | ⟨0, _⟩ => q5Logical a
  | ⟨i + 1, h⟩ => v ⟨i, by omega⟩

end OpenQuantumProblem35
