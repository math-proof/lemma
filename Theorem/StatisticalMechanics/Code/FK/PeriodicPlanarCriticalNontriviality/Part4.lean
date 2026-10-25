/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part5
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


@[simp] theorem RootedWalkCode.toWalk_ofWalk_endpoint
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) :
    ((RootedWalkCode.ofWalk G p).toWalk G).1 = v := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa [RootedWalkCode.ofWalk, RootedWalkCode.toWalk] using ih

theorem RootedWalkCode.toWalk_ofWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) :
    (RootedWalkCode.ofWalk G p).toWalk G = ⟨v, p⟩ := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      simp only [RootedWalkCode.ofWalk]
      change (let pp := (RootedWalkCode.ofWalk G p).toWalk G
        (⟨pp.1, pp.2.cons h⟩ : Sigma (fun x : V => G.Walk u x))) =
          (⟨w, Walk.cons h p⟩ : Sigma (fun x : V => G.Walk u x))
      rw [ih]

theorem RootedWalkCode.toWalk_cast
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u : V} {m n : Nat} (h : m = n) (c : RootedWalkCode G u m) :
    (h ▸ c).toWalk G = c.toWalk G := by
  cases h
  rfl


theorem card_rootedWalkCode_le
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {D : Nat} (hD : ∀ v, G.degree v ≤ D) (u : V) (n : Nat) :
    Fintype.card (RootedWalkCode G u n) ≤ D ^ n := by
  induction n generalizing u with
  | zero => simp [RootedWalkCode]
  | succ n ih =>
      change Fintype.card (Σ w : G.neighborSet u, RootedWalkCode G w n) ≤ D ^ (n + 1)
      rw [Fintype.card_sigma]
      calc
        ∑ w : G.neighborSet u, Fintype.card (RootedWalkCode G w n)
            ≤ ∑ _w : G.neighborSet u, D ^ n :=
              Finset.sum_le_sum fun w _ => ih w
        _ = Fintype.card (G.neighborSet u) * D ^ n := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ]
        _ = G.degree u * D ^ n := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
        _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
        _ = D ^ (n + 1) := by rw [pow_succ']


end StatMech.FK.PeriodicPlanar
