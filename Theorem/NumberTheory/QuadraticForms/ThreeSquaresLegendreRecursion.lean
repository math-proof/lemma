/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion


namespace MetaMathlibExt

lemma r3leg_pure_injective : Function.Injective r3legPure := by
  intro x y h
  have hI := congrArg (fun q : Quaternion ℤ => q.imI) h
  have hJ := congrArg (fun q : Quaternion ℤ => q.imJ) h
  have hK := congrArg (fun q : Quaternion ℤ => q.imK) h
  exact Prod.ext (Prod.ext hI hJ) hK

lemma r3leg_normSq_pure (x : r3legIntVec) :
    Quaternion.normSq (r3legPure x) = r3legQ x := by
  simp [Quaternion.normSq_def', r3legPure, r3legQ]

lemma r3leg_sandwich_re (q : Quaternion ℤ) (x : r3legIntVec) :
    (q * r3legPure x * star q).re = 0 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, r3legPure]
  ring

lemma r3leg_pure_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPure (r3legPhi q x) = q * r3legPure x * star q := by
  apply Quaternion.ext
  · exact (r3leg_sandwich_re q x).symm
  · rfl
  · rfl
  · rfl

lemma r3leg_phi_comp (q r : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legPhi r x) = r3legPhi (q * r) x := by
  apply r3leg_pure_injective
  calc
    r3legPure (r3legPhi q (r3legPhi r x)) =
        q * r3legPure (r3legPhi r x) * star q := r3leg_pure_phi q _
    _ = q * (r * r3legPure x * star r) * star q := by
      rw [r3leg_pure_phi]
    _ = (q * r) * r3legPure x * star (q * r) := by
      rw [star_mul]
      simp only [mul_assoc]
    _ = r3legPure (r3legPhi (q * r) x) := (r3leg_pure_phi _ _).symm

lemma r3leg_q_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legQ (r3legPhi q x) = Quaternion.normSq q ^ 2 * r3legQ x := by
  calc
    r3legQ (r3legPhi q x) =
        Quaternion.normSq (r3legPure (r3legPhi q x)) :=
      (r3leg_normSq_pure _).symm
    _ = Quaternion.normSq (q * r3legPure x * star q) := by
      rw [r3leg_pure_phi]
    _ = Quaternion.normSq q ^ 2 * r3legQ x := by
      rw [map_mul, map_mul, Quaternion.normSq_star, r3leg_normSq_pure]
      ring

lemma r3leg_phi_fst_fst (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).1.1 =
      (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2) * x.1.1 +
      2 * (q.imI * q.imJ - q.re * q.imK) * x.1.2 +
      2 * (q.imI * q.imK + q.re * q.imJ) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imI_mul,
    Quaternion.re_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

lemma r3leg_phi_fst_snd (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).1.2 =
      2 * (q.imI * q.imJ + q.re * q.imK) * x.1.1 +
      (q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2) * x.1.2 +
      2 * (q.imJ * q.imK - q.re * q.imI) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imJ_mul,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

lemma r3leg_phi_snd (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).2 =
      2 * (q.imI * q.imK - q.re * q.imJ) * x.1.1 +
      2 * (q.imJ * q.imK + q.re * q.imI) * x.1.2 +
      (q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imK_mul,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

lemma r3leg_phi_smul (c : ℤ) (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi (c • q) x = r3legScale (c ^ 2) (r3legPhi q x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      simp
      ring
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      simp
      ring
  · simp only [r3legScale]
    rw [r3leg_phi_snd, r3leg_phi_snd]
    simp
    ring

lemma r3leg_phi_intCast (c : ℤ) (x : r3legIntVec) :
    r3legPhi (c : Quaternion ℤ) x = r3legScale (c ^ 2) x := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst]
      simp
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd]
      simp
  · simp only [r3legScale]
    rw [r3leg_phi_snd]
    simp

lemma r3leg_phi_star_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legPhi (star q) x) =
      r3legScale (Quaternion.normSq q ^ 2) x := by
  rw [r3leg_phi_comp, Quaternion.self_mul_star]
  exact r3leg_phi_intCast _ _

lemma r3leg_phi_phi_star (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi (star q) (r3legPhi q x) =
      r3legScale (Quaternion.normSq q ^ 2) x := by
  rw [r3leg_phi_comp, Quaternion.star_mul_self]
  exact r3leg_phi_intCast _ _

lemma r3leg_phi_adjoint (q : Quaternion ℤ) (z u : r3legIntVec) :
    r3legB (r3legPhi (star q) z) u = r3legB z (r3legPhi q u) := by
  simp only [r3legB]
  rw [r3leg_phi_fst_fst, r3leg_phi_fst_snd, r3leg_phi_snd,
    r3leg_phi_fst_fst, r3leg_phi_fst_snd, r3leg_phi_snd]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

end MetaMathlibExt
