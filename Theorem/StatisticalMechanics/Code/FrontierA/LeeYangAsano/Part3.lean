/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part2
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem leeYangHalfEdgeProduct_eq (beta : ℝ) (z : LeeYangVar G → ℂ) :
    leeYangHalfEdgeProduct G beta z =
      leeYangAnchorProduct G z * leeYangEdgeProduct G beta z := rfl

omit [DecidableEq V] in
theorem leeYangNormalizedEdgeFactor_ne_zero {beta : ℝ} (hbeta : 0 ≤ beta)
    (e : ↑G.edgeFinset) (z : LeeYangVar G → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    leeYangNormalizedEdgeFactor G beta e z ≠ 0 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      apply leeYang_edgeFactor_ne_zero (r := Real.exp (-2 * beta))
      · positivity
      · rw [Real.exp_le_one_iff]
        linarith
      · exact hz _
      · exact hz _

omit [DecidableEq V] in
theorem leeYangHalfEdgeProduct_stable {beta : ℝ} (hbeta : 0 ≤ beta) :
    PolydiscStable (leeYangHalfEdgeProduct G beta) := by
  intro z hz
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun v _ hv ↦ by
      have heq : z (leeYangAnchor G v) = -1 := by linear_combination hv
      have := hz (leeYangAnchor G v)
      rw [heq] at this
      norm_num at this
  · exact Finset.prod_ne_zero_iff.mpr fun e _ ↦
      leeYangNormalizedEdgeFactor_ne_zero G hbeta e z hz

theorem leeYangNormalizedEdgeFactor_affine (beta : ℝ)
    (e : ↑G.edgeFinset) (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangHalf G w e) t) =
      leeYangNormalizedEdgeFactor G beta e
          (Function.update z (leeYangHalf G w e) 0) +
        t * (leeYangNormalizedEdgeFactor G beta e
            (Function.update z (leeYangHalf G w e) 1) -
          leeYangNormalizedEdgeFactor G beta e
            (Function.update z (leeYangHalf G w e) 0)) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        apply SimpleGraph.Adj.ne
        simpa [SimpleGraph.mem_edgeFinset] using he
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      by_cases hwu : w = u
      · subst w
        have hpair : (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
            (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
          intro h
          exact huv (Prod.mk.inj h).1
        simp [leeYangHalf, Ne.symm hpair]
        ring
      · by_cases hwv : w = v
        · subst w
          have hpair : (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact huv (Prod.mk.inj h).1
          simp [leeYangHalf, hpair]
          ring
        · have hpairu : (w, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact hwu (Prod.mk.inj h).1
          have hpairv : (w, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact hwv (Prod.mk.inj h).1
          simp [leeYangHalf, Ne.symm hpairu, Ne.symm hpairv]

theorem leeYangNormalizedEdgeFactor_update_other (beta : ℝ)
    {e e' : ↑G.edgeFinset} (hee : e' ≠ e) (w : V)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangHalf G w e') t) =
      leeYangNormalizedEdgeFactor G beta e z := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hpairu : (w, e') ≠ (u, ⟨s(u, v), he⟩) := by
        intro h
        apply hee
        exact congrArg Prod.snd h
      have hpairv : (w, e') ≠ (v, ⟨s(u, v), he⟩) := by
        intro h
        apply hee
        exact congrArg Prod.snd h
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      rw [show Function.update z (leeYangHalf G w e') t
          (leeYangHalf G u ⟨s(u, v), he⟩) =
          z (leeYangHalf G u ⟨s(u, v), he⟩) by
            simp [leeYangHalf, Ne.symm hpairu],
        show Function.update z (leeYangHalf G w e') t
          (leeYangHalf G v ⟨s(u, v), he⟩) =
          z (leeYangHalf G v ⟨s(u, v), he⟩) by
            simp [leeYangHalf, Ne.symm hpairv]]

theorem leeYangNormalizedEdgeFactor_update_anchor (beta : ℝ)
    (e : ↑G.edgeFinset) (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangAnchor G w) t) =
      leeYangNormalizedEdgeFactor G beta e z := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp [leeYangNormalizedEdgeFactor, leeYangHalf, leeYangAnchor]

theorem leeYangAnchorProduct_affine (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) t) =
      leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0) +
        t * (leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 1) -
          leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0)) := by
  let R : ℂ := ∏ v ∈ (Finset.univ.erase w), (1 + z (leeYangAnchor G v))
  have hfactor (u : ℂ) :
      leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) u) =
        (1 + u) * R := by
    unfold leeYangAnchorProduct
    rw [← Finset.mul_prod_erase Finset.univ
      (fun v ↦ 1 + Function.update z (leeYangAnchor G w) u (leeYangAnchor G v))
      (Finset.mem_univ w)]
    congr 1
    · simp [leeYangAnchor]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
      simp [leeYangAnchor, hvw]
  rw [hfactor t, hfactor 0, hfactor 1]
  ring

theorem leeYangAnchorProduct_update_half (w : V) (e : ↑G.edgeFinset)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangAnchorProduct G (Function.update z (leeYangHalf G w e) t) =
      leeYangAnchorProduct G z := by
  unfold leeYangAnchorProduct
  apply Finset.prod_congr rfl
  intro v hv
  simp [leeYangAnchor, leeYangHalf]

theorem leeYangEdgeProduct_update_anchor (beta : ℝ) (w : V)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangEdgeProduct G beta (Function.update z (leeYangAnchor G w) t) =
      leeYangEdgeProduct G beta z := by
  unfold leeYangEdgeProduct
  apply Finset.prod_congr rfl
  intro e he
  exact leeYangNormalizedEdgeFactor_update_anchor G beta e w z t

theorem leeYangEdgeProduct_affine (beta : ℝ) (w : V) (e : ↑G.edgeFinset)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) t) =
      leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0) +
        t * (leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 1) -
          leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0)) := by
  let R : ℂ := ∏ f ∈ (Finset.univ.erase e), leeYangNormalizedEdgeFactor G beta f z
  have hfactor (u : ℂ) :
      leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) u) =
        leeYangNormalizedEdgeFactor G beta e
          (Function.update z (leeYangHalf G w e) u) * R := by
    unfold leeYangEdgeProduct
    rw [← Finset.mul_prod_erase Finset.univ
      (fun f ↦ leeYangNormalizedEdgeFactor G beta f
        (Function.update z (leeYangHalf G w e) u)) (Finset.mem_univ e)]
    congr 1
    apply Finset.prod_congr rfl
    intro f hf
    have hfe : e ≠ f := Ne.symm (Finset.mem_erase.mp hf).1
    rw [leeYangNormalizedEdgeFactor_update_other G beta hfe w z u]
  rw [hfactor t, hfactor 0, hfactor 1,
    leeYangNormalizedEdgeFactor_affine G beta e w z t]
  ring

theorem leeYangHalfEdgeProduct_multiAffine (beta : ℝ) :
    IsMultiAffine (leeYangHalfEdgeProduct G beta) := by
  intro k z t
  rcases k with w | ⟨w, e⟩
  · change leeYangHalfEdgeProduct G beta
        (Function.update z (leeYangAnchor G w) t) = _
    simp_rw [leeYangHalfEdgeProduct_eq]
    rw [leeYangAnchorProduct_affine G w z t]
    simp only [leeYangAnchor]
    have hedge (u : ℂ) :
        leeYangEdgeProduct G beta (Function.update z (Sum.inl w) u) =
          leeYangEdgeProduct G beta z := by
      simpa only [leeYangAnchor] using leeYangEdgeProduct_update_anchor G beta w z u
    simp_rw [hedge]
    ring
  · change leeYangHalfEdgeProduct G beta
        (Function.update z (leeYangHalf G w e) t) = _
    simp_rw [leeYangHalfEdgeProduct_eq]
    rw [leeYangEdgeProduct_affine G beta w e z t]
    simp only [leeYangHalf]
    have hanchor (u : ℂ) :
        leeYangAnchorProduct G (Function.update z (Sum.inr (w, e)) u) =
          leeYangAnchorProduct G z := by
      simpa only [leeYangHalf] using leeYangAnchorProduct_update_half G w e z u
    simp_rw [hanchor]
    ring

end StatMech.FrontierA
