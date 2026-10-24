/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLatticeSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QBinomial
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.QBinomial
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

open SpernerProperty YoungLattice YoungLattice.Lmn Finset

namespace SubsetSum

noncomputable def subsetSumCount (k : ℕ) (S : Finset ℝ) (α : ℝ) : ℕ :=
  ((powersetCard k S).filter (fun T => T.sum id = α)).card

def iccNat (n : ℕ) : Finset ℕ := Finset.Icc 1 n

def subsetSumCountNat (k n α : ℕ) : ℕ :=
  ((powersetCard k (iccNat n)).filter (fun T => T.sum id = α)).card

lemma strictMono_fin_add_le {k : ℕ} {s : Fin k → ℕ} (hs : StrictMono s)
    (a b : Fin k) (hab : a ≤ b) : s a + (b.val - a.val) ≤ s b := by
  suffices key : ∀ (d : ℕ) (c e : Fin k), c.val + d = e.val → s c + d ≤ s e by
    exact key (b.val - a.val) a b (by omega)
  intro d
  induction d with
  | zero => intro c e h; have : c = e := Fin.ext (by omega); subst this; exact le_refl _
  | succ d ih =>
    intro c e hce
    let f : Fin k := ⟨e.val - 1, by omega⟩
    have h1 : s c + d ≤ s f := ih c f (by simp [f]; omega)
    have h2 : s f + 1 ≤ s e := Nat.succ_le_of_lt (hs (Fin.mk_lt_mk.mpr (by omega)))
    omega

noncomputable def lambdaMapForward (k m : ℕ) (p : Lmn k m) : Finset ℕ :=
  (Finset.univ : Finset (Fin k)).image (fun r => (p.val (Fin.rev r)).val + r.val + 1)

noncomputable def idxFun
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : Fin n :=
  (S.orderIsoOfFin hScard).symm
    ⟨T.orderEmbOfFin hTcard r, hTsub (Finset.orderEmbOfFin_mem T hTcard r)⟩

noncomputable def idxVal
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : ℕ :=
  (idxFun S n hScard T k hTcard hTsub r).val

lemma idxFun_strictMono
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S) :
    StrictMono (idxFun S n hScard T k hTcard hTsub) := by
  intro a b hab
  simp only [idxFun]
  apply (S.orderIsoOfFin hScard).symm.strictMono
  simp only [Subtype.mk_lt_mk]
  exact (T.orderEmbOfFin hTcard).strictMono hab

lemma idxVal_ge
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : r.val ≤ idxVal S n hScard T k hTcard hTsub r := by
  simp only [idxVal]
  have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
    fun a b hab => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hab
  have h0 : 0 ≤ (idxFun S n hScard T k hTcard hTsub ⟨0, r.pos⟩).val := Nat.zero_le _
  by_cases hr0 : r.val = 0
  · have : r = ⟨0, r.pos⟩ := Fin.ext (by omega); rw [this]; omega
  · have h0r : (⟨0, r.pos⟩ : Fin k) ≤ r := Fin.mk_le_mk.mpr (by omega)
    have := strictMono_fin_add_le hsm ⟨0, r.pos⟩ r h0r
    simp at this; omega

lemma idxVal_bound
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (hkn : k ≤ n)
    (r : Fin k) : idxVal S n hScard T k hTcard hTsub r - r.val ≤ n - k := by
  simp only [idxVal]
  have hk_pos : 0 < k := r.pos
  have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
    fun a b hab => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hab
  have hbound : (idxFun S n hScard T k hTcard hTsub r).val < n := (idxFun S n hScard T k hTcard hTsub r).isLt
  by_cases hrk : r.val = k - 1
  · have : r = ⟨k - 1, by omega⟩ := Fin.ext (by omega); rw [this]; omega
  · have hlt : r < ⟨k - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have hlast_bound : (idxFun S n hScard T k hTcard hTsub ⟨k - 1, by omega⟩).val < n :=
      (idxFun S n hScard T k hTcard hTsub ⟨k - 1, by omega⟩).isLt
    have := strictMono_fin_add_le hsm r ⟨k - 1, by omega⟩ (le_of_lt hlt)
    simp at this; omega

noncomputable def toLmn
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (hkn : k ≤ n) : Lmn k (n - k) :=
  ⟨fun i => ⟨idxVal S n hScard T k hTcard hTsub (Fin.rev i) -
    (Fin.rev i).val, by
    have := idxVal_bound S n hScard T k hTcard hTsub hkn (Fin.rev i); omega⟩,
  fun a b hab => by
    simp only [Fin.le_def]
    have hrev := Fin.rev_le_rev.mpr hab
    have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
      fun x y hxy => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hxy
    have h := strictMono_fin_add_le hsm (Fin.rev b) (Fin.rev a) hrev
    have hge_a := idxVal_ge S n hScard T k hTcard hTsub (Fin.rev a)
    have hge_b := idxVal_ge S n hScard T k hTcard hTsub (Fin.rev b)
    simp only [idxVal] at *
    omega⟩
