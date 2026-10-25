/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part4
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem reimer_wprobCore_of_butterflyMono (h : ∀ n, ReimerButterflyMono n) : ReimerWprobCore :=
  reimer_wprobCore_of_sliceStep h


theorem reimerButterflyMono_of_increasing (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob ψ (disjointOccurrence (slice A false) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                    ∩ disjointOccurrence (slice A true) (slice B false))
    ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (slice A true) * wprob ψ (slice B true) :=
  reimerSliceStep_holds_on_increasing n ψ hψ0 hψ1 A B hA hB


theorem reimerButterflyMono_satisfiable (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
    wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
              (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false))
        ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                    (slice Set.univ true)
                    ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
    ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                (slice Set.univ true)
                ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
        ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true)
            * wprob ψ (slice Set.univ true) :=
  reimerSliceStep_satisfiable n ψ hψ0 hψ1


end StatMech
