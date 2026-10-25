/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
open Finset
open scoped symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


theorem connK_sdiff_or_meets_edgeConnected
    (ends : ι -> Sym2 V) (H X : Finset ι) (i k v : V)
    (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
    (hiv : connK ends H i v) :
    connK ends (H \ X) i v ∨
      ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
  induction hiv with
  | refl =>
      exact Or.inl Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      rcases ih with hprefix | hmeet
      · rcases hstep with ⟨e, heH, hb, hc, hbc⟩
        by_cases heX : e ∈ X
        · exact Or.inr ⟨b, hprefix, hXconn e heX b hb⟩
        · exact Or.inl (hprefix.tail
            ⟨e, Finset.mem_sdiff.mpr ⟨heH, heX⟩, hb, hc, hbc⟩)
      · exact Or.inr hmeet


theorem exists_connK_sdiff_meets_of_edgeConnected
    (ends : ι -> Sym2 V) (H X : Finset ι) (i k : V)
    (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
    (hik : connK ends H i k) :
    ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
  rcases connK_sdiff_or_meets_edgeConnected ends H X i k k hXconn hik with
    hsurvives | hmeet
  · exact ⟨k, hsurvives, Relation.ReflTransGen.refl⟩
  · exact hmeet

theorem edgeComponent_subset_edges
    (ends : ι -> Sym2 V) (K : Finset ι) (k : V) :
    edgeComponent ends K k ⊆ K := by
  intro e he
  rw [edgeComponent, Finset.mem_filter] at he
  exact he.1


theorem connK_edgeComponent_of_conn
    (ends : ι -> Sym2 V) (K : Finset ι) (k x : V)
    (hkx : connK ends K k x) :
    connK ends (edgeComponent ends K k) k x := by
  induction hkx with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hstep ih =>
      rcases hstep with ⟨e, heK, ha, hb, hab⟩
      have hka : connK ends K k a :=
        connK_mono (edgeComponent_subset_edges ends K k) ih
      exact ih.tail ⟨e,
        mem_edgeComponent_of_reachable_endpoint hka heK ha,
        ha, hb, hab⟩


theorem edgeComponent_endpoint_connK
    (ends : ι -> Sym2 V) (K : Finset ι) (k : V) :
    ∀ e ∈ edgeComponent ends K k, ∀ x ∈ ends e,
      connK ends (edgeComponent ends K k) k x := by
  intro e he x hx
  rw [edgeComponent, Finset.mem_filter] at he
  exact connK_edgeComponent_of_conn ends K k x (he.2 x hx)


end StatMech.FrontierA
