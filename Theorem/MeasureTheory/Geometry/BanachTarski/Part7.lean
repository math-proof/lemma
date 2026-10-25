/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part7


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Casting commutes with the integer generator step. -/
theorem btIntGen_cast (s : Fin 2 × Bool) (v : Fin 3 → ℤ) :
    (fun i => ((btIntGen s v i : ℤ) : ZMod 5)) =
      btIntGenMod s (fun i => ((v i : ℤ) : ZMod 5)) := by
  obtain ⟨x, b⟩ := s
  fin_cases x <;> cases b <;>
    ext i <;> fin_cases i <;>
    simp [btIntGen, btIntGenMod]

/-- Base case: the generator applied to `e_y` is a nonzero multiple of the
letter direction. -/
theorem btIntWord_base :
    ∀ s : Fin 2 × Bool, ∃ c : ZMod 5, c ≠ 0 ∧
      (fun i => ((btIntGen s ![0, 1, 0] i : ℤ) : ZMod 5)) = c • btEll s := by
  decide

/-- Step case: applying a generator to a nonzero multiple of a non-inverse
letter direction stays a nonzero multiple of the new direction. -/
theorem btIntWord_step :
    ∀ (s t : Fin 2 × Bool) (c : ZMod 5), (t.1 ≠ s.1 ∨ t.2 = s.2) → c ≠ 0 →
      ∃ c' : ZMod 5, c' ≠ 0 ∧
        btIntGenMod s (c • btEll t) = c' • btEll s := by
  decide

/-- The mod-5 reduction of a reduced word is a nonzero multiple of the first
letter's direction. -/
theorem btIntWord_mod_five (s : Fin 2 × Bool) (L : List (Fin 2 × Bool))
    (h : FreeGroup.IsReduced (s :: L)) :
    ∃ c : ZMod 5, c ≠ 0 ∧
      (fun i => ((btIntWord (s :: L) i : ℤ) : ZMod 5)) = c • btEll s := by
  have aux : ∀ (L : List (Fin 2 × Bool)) (s : Fin 2 × Bool),
      FreeGroup.IsReduced (s :: L) →
      ∃ c : ZMod 5, c ≠ 0 ∧
        (fun i => ((btIntWord (s :: L) i : ℤ) : ZMod 5)) = c • btEll s := by
    intro L
    induction L with
    | nil =>
      intro s _
      have hfold : btIntWord [s] = btIntGen s ![0, 1, 0] := rfl
      rw [hfold]
      exact btIntWord_base s
    | cons t L' ih =>
      intro s hs
      have hcons := (FreeGroup.isReduced_cons_cons).mp hs
      have hside : t.1 ≠ s.1 ∨ t.2 = s.2 := by
        by_cases he : t.1 = s.1
        · right
          exact (hcons.1 he.symm).symm
        · left
          exact he
      obtain ⟨c, hcne, hc⟩ := ih t hcons.2
      obtain ⟨c', hc'ne, hc'⟩ := btIntWord_step s t c hside hcne
      refine ⟨c', hc'ne, ?_⟩
      have hfold : btIntWord (s :: t :: L') = btIntGen s (btIntWord (t :: L')) := rfl
      rw [hfold, btIntGen_cast, hc]
      exact hc'
  exact aux L s h

/-- The real `e_y` agrees with the cast of the integer `e_y`, coordinatewise. -/
theorem btEy_cast (i : Fin 3) :
    ((![0, 1, (0 : ℤ)] i : ℤ) : ℝ) = ![0, 1, (0 : ℝ)] i := by
  fin_cases i <;> simp

/-- No nontrivial word fixes a nonzero multiple of `e_y`. -/
theorem btRho_ey_ne (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (s : ℝ) (hs : s ≠ 0) :
    ¬ Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) (s • ![0, 1, (0 : ℝ)]) =
      s • ![0, 1, (0 : ℝ)] := by
  intro hfix
  have h1 : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, (0 : ℝ)] =
      ![0, 1, (0 : ℝ)] := by
    have h2 : s • Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, (0 : ℝ)] =
        s • ![0, 1, (0 : ℝ)] := by
      rw [← Matrix.mulVec_smul]
      exact hfix
    ext i
    have hi := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hs hi
  have hne : w.toWord ≠ [] :=
    fun hempty => hw (FreeGroup.toWord_eq_nil_iff.mp hempty)
  cases hL : w.toWord with
  | nil => exact absurd hL hne
  | cons s0 L' =>
    have hred : FreeGroup.IsReduced (s0 :: L') := by
      rw [← hL]
      exact FreeGroup.isReduced_toWord
    have hmk : FreeGroup.mk (s0 :: L') = w := by
      rw [← hL]
      exact FreeGroup.mk_toWord
    have hspec := btIntWord_spec (s0 :: L')
    rw [hmk, h1] at hspec
    have hcast : ∀ i : Fin 3,
        ((5 * (5 ^ L'.length * ![0, 1, (0 : ℤ)] i) : ℤ) : ℝ) =
        (5 ^ (s0 :: L').length : ℝ) * ![0, 1, (0 : ℝ)] i := by
      intro i
      push_cast
      rw [btEy_cast i, List.length_cons, pow_succ]
      ring
    have hint : ∀ i, btIntWord (s0 :: L') i =
        5 * (5 ^ L'.length * ![0, 1, (0 : ℤ)] i) := by
      intro i
      have hi := congrFun hspec i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [← hcast i] at hi
      exact (Int.cast_injective hi).symm
    have hzero : (fun i => ((btIntWord (s0 :: L') i : ℤ) : ZMod 5)) = 0 := by
      ext i
      simp only [hint i, Pi.zero_apply]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_mul_right 5 _
    obtain ⟨c, hcne, hc⟩ := btIntWord_mod_five s0 L' hred
    rw [hzero] at hc
    have hell : ∀ t : Fin 2 × Bool, ∀ d : ZMod 5, d • btEll t = 0 → d = 0 := by
      decide
    exact hcne (hell s0 c hc.symm)

/-- A nontrivial word fixing `u` and `v` forces `u ⨯₃ v = 0`. -/
theorem btFix_cross_eq_zero (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (u v : Fin 3 → ℝ)
    (hu : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u = u)
    (hv : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v = v) :
    crossProduct u v = 0 := by
  by_contra hne
  have hnn : dotProduct (crossProduct u v) (crossProduct u v) ≠ 0 :=
    fun h0 => hne ((dotProduct_self_eq_zero).mp h0)
  have hMn : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
      (crossProduct u v) = crossProduct u v := by
    rw [← btRho_cross, hu, hv]
  have hdu : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) u
        = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x) u =
        dotProduct x u := by
      have e := btRho_dot w x u
      rw [hu] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hdv : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) v
        = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x) v =
        dotProduct x v := by
      have e := btRho_dot w x v
      rw [hv] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hdn : ∀ x : Fin 3 → ℝ,
      dotProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (crossProduct u v) = 0 := by
    intro x
    have hMx : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x)
        (crossProduct u v) =
        dotProduct x (crossProduct u v) := by
      have e := btRho_dot w x (crossProduct u v)
      rw [hMn] at e
      exact e
    rw [sub_dotProduct, hMx, sub_self]
  have hcross : ∀ x : Fin 3 → ℝ,
      crossProduct (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (crossProduct u v) = 0 := by
    intro x
    have e := cross_cross_eq_smul_sub_smul'
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) u v
    have e2 : dotProduct u
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) = 0 := by
      rw [dotProduct_comm u, hdu x]
    rw [e, hdv x, e2]
    simp
  have hall : ∀ x : Fin 3 → ℝ,
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x = x := by
    intro x
    have e := cross_dot_cross
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
      (crossProduct u v)
      (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
      (crossProduct u v)
    rw [hcross x] at e
    simp only [zero_dotProduct] at e
    rw [hdn x] at e
    simp only [zero_mul, sub_zero] at e
    have eyy : dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) x - x) = 0 :=
      (mul_eq_zero.mp e.symm).resolve_right hnn
    rw [dotProduct_self_eq_zero] at eyy
    exact sub_eq_zero.mp eyy
  have hey := hall ![0, 1, (0 : ℝ)]
  exact btRho_ey_ne w hw 1 one_ne_zero (by simpa using hey)

/-- Fixed vectors of a nontrivial word lie on one line through a unit vector
with `(u 0, u 2) ≠ (0, 0)`. -/
theorem btAxis (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    ∃ u : Fin 3 → ℝ, dotProduct u u = 1 ∧ (u 0, u 2) ≠ (0, 0) ∧
      ∀ x : btE, btAct w x = x → ∃ s : ℝ, WithLp.ofLp x = s • u := by
  by_cases hfix : ∃ p : Fin 3 → ℝ, p ≠ 0 ∧
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) p = p
  · obtain ⟨p, hpne, hpp⟩ := hfix
    have hne : dotProduct p p ≠ 0 :=
      fun h0 => hpne ((dotProduct_self_eq_zero).mp h0)
    have hnn : 0 ≤ dotProduct p p := by
      change (0 : ℝ) ≤ ∑ i, p i * p i
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (p i))
    have hpos : 0 < dotProduct p p := lt_of_le_of_ne hnn (Ne.symm hne)
    have hrne : Real.sqrt (dotProduct p p) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hrsq : Real.sqrt (dotProduct p p) * Real.sqrt (dotProduct p p) =
        dotProduct p p :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have key : ∀ (r X : ℝ), r ≠ 0 → r * r = X →
        (1 / r) * ((1 / r) * X) = 1 := by
      intro r X hr hrr
      rw [← hrr, one_div, ← mul_assoc, ← mul_inv]
      exact inv_mul_cancel₀ (mul_ne_zero hr hr)
    have huu : dotProduct ((1 / Real.sqrt (dotProduct p p)) • p)
        ((1 / Real.sqrt (dotProduct p p)) • p) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      exact key _ _ hrne hrsq
    have hnsub : (((1 / Real.sqrt (dotProduct p p)) • p) 0,
        ((1 / Real.sqrt (dotProduct p p)) • p) 2) ≠ (0, 0) := by
      intro hcon
      have hcon0 := congrArg Prod.fst hcon
      have hcon2 := congrArg Prod.snd hcon
      simp only [Pi.smul_apply, smul_eq_mul] at hcon0 hcon2
      have h0 : p 0 = 0 :=
        (mul_eq_zero.mp hcon0).resolve_left (div_ne_zero one_ne_zero hrne)
      have h2 : p 2 = 0 :=
        (mul_eq_zero.mp hcon2).resolve_left (div_ne_zero one_ne_zero hrne)
      have hp1 : p 1 ≠ 0 := by
        intro hz
        apply hpne
        ext i
        fin_cases i
        · simpa using h0
        · simpa using hz
        · simpa using h2
      have hpe : p = (p 1) • ![0, 1, (0 : ℝ)] := by
        ext i
        fin_cases i
        · simp [h0, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
        · simp [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
            Matrix.cons_val_zero]
        · simp [h2, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons]
      have hfix1 : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
          ((p 1) • ![0, 1, (0 : ℝ)]) = (p 1) • ![0, 1, (0 : ℝ)] := by
        rw [← hpe]
        exact hpp
      exact btRho_ey_ne w hw (p 1) hp1 hfix1
    refine ⟨(1 / Real.sqrt (dotProduct p p)) • p, huu, hnsub, ?_⟩
    intro x hx
    have hMx : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
        (WithLp.ofLp x) = WithLp.ofLp x :=
      congrArg WithLp.ofLp hx
    have hMu : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
        ((1 / Real.sqrt (dotProduct p p)) • p) =
        (1 / Real.sqrt (dotProduct p p)) • p := by
      rw [Matrix.mulVec_smul, hpp]
    have hcr := btFix_cross_eq_zero w hw _ _ hMx hMu
    have hz : crossProduct ((1 / Real.sqrt (dotProduct p p)) • p) 0 = 0 := by
      simp
    have e := cross_cross_eq_smul_sub_smul'
      ((1 / Real.sqrt (dotProduct p p)) • p) (WithLp.ofLp x)
      ((1 / Real.sqrt (dotProduct p p)) • p)
    rw [hcr, hz, huu, one_smul] at e
    exact ⟨dotProduct (WithLp.ofLp x)
      ((1 / Real.sqrt (dotProduct p p)) • p), sub_eq_zero.mp e.symm⟩
  · refine ⟨![1, 0, (0 : ℝ)], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
    · have e0 : (![1, 0, (0 : ℝ)] : Fin 3 → ℝ) 0 = 1 := by
        simp [Matrix.cons_val_zero]
      have e2 : (![1, 0, (0 : ℝ)] : Fin 3 → ℝ) 2 = 0 := by
        simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [e0, e2]
      simp
    · intro x hx
      have hMx : Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
          (WithLp.ofLp x) = WithLp.ofLp x :=
        congrArg WithLp.ofLp hx
      refine ⟨0, ?_⟩
      simp only [zero_smul]
      by_contra hcon
      exact hfix ⟨WithLp.ofLp x, hcon, hMx⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
