/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part13
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma centerPathEquiv_apply (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (k : Fin (2 * n + 1)) :
    centerPathEquiv E n (s,(l,r)) k =
      Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
  rfl

lemma centerPathEquiv_center (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) :
    centerPathEquiv E n (s,(l,r)) ⟨n, by omega⟩ = s := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨n, by omega⟩ : Fin (2*n+1)) =
    Fin.natAdd n (0 : Fin (n+1)) by apply Fin.ext; simp]
  rw [Fin.append_right, Fin.cons_zero]


lemma centerPathEquiv_left (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (i : Fin n) :
    centerPathEquiv E n (s,(l,r)) ⟨i.val, by omega⟩ = l i := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨i.val, by omega⟩ : Fin (2*n+1)) =
    Fin.castAdd (n+1) i by apply Fin.ext; simp]
  rw [Fin.append_left]

lemma centerPathEquiv_right (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (i : Fin n) :
    centerPathEquiv E n (s,(l,r)) ⟨n + 1 + i.val, by omega⟩ = r i := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨n+1+i.val, by omega⟩ : Fin (2*n+1)) =
    Fin.natAdd n (Fin.succ i) by
      apply Fin.ext
      change n + 1 + i.val = n + (i.val + 1)
      omega]
  rw [Fin.append_right, Fin.cons_succ]

end StatMech.FrontierB
