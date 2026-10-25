/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

theorem triangularTorusDartToGraphDart_bijective
    (L : Nat) [Fact (2 < L)] :
    Function.Bijective (triangularTorusDartToGraphDart L) := by
  constructor
  · intro d e hde
    have hp : d.1 = e.1 := congrArg (fun z => z.fst) hde
    have hq : d.1 - triangularTorusDirectionStep L d.2 =
        e.1 - triangularTorusDirectionStep L e.2 :=
      congrArg (fun z => z.snd) hde
    apply Prod.ext hp
    apply triangularTorusDirectionStep_injective L
    rw [hp] at hq
    exact sub_right_injective hq
  · rintro ⟨⟨p, q⟩, hpq⟩
    change triangularTorusAdj L p q at hpq
    unfold triangularTorusAdj at hpq
    rcases hpq with hsquare | hdiag
    · rcases hsquare with ⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩
      · refine ⟨(p, (2 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (3 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (0 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (1 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
    · rcases hdiag with hdiag | hdiag
      · refine ⟨(p, (4 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination hdiag.1 | linear_combination hdiag.2
      · refine ⟨(p, (5 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination hdiag.1 | linear_combination hdiag.2


end StatMech.FrontierA
