/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part2
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def quinaryPhase (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : ZMod 5 :=
  graphPhase q5Graph (quinaryWord a v)

noncomputable def ameAmplitude (x : Config 9 10) : ℂ :=
  let u : Fin 9 → ZMod 2 := fun i => bitPart (x i)
  let v : Fin 9 → ZMod 5 := fun i => quintPart (x i)
  ((Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹) *
    ∑ a : Fin 2 → ZMod 2,
      ZMod.stdAddChar (binaryPhase a u) * ZMod.stdAddChar (quinaryPhase a v)

noncomputable def ameState : StateVector 9 10 := mkStateVector ameAmplitude

def ame_9_10_open_statement : Prop := ExistsAME 9 10

def pasteOn {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) : ι → R :=
  fun i => if hi : i ∈ A then x ⟨i, hi⟩ else z ⟨i, hi⟩

end OpenQuantumProblem35
