import Mathlib
import sympy.Basic
open Polynomial Matrix
set_option maxHeartbeats 1000000


private lemma aeval_mulVec_of_mulVec_eq_smul
  [Field F]
  {n : Type u} [Fintype n] [DecidableEq n]
  (M : Matrix n n F) (μ : F) (v : n → F)
-- given
  (hv : M *ᵥ v = μ • v)
  (p : F[X]) :
-- imply
  (aeval M p) *ᵥ v = (p.eval μ) • v := by
-- proof
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, eval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, mul_smul]
    congr 1
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']


/--
[Algebra_isIntegral_trace_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isIntegral_trace_of_finiteDimensional.lean)
-/
@[path]
private lemma main
  [CommRing R] [Field K] [Algebra R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [FiniteDimensional K A]
  {x : A}
-- given
  (hx : IsIntegral R x) :
-- imply
  IsIntegral R (Algebra.trace K A x) := by
-- proof
  classical
  obtain ⟨p, hpmon, hpx⟩ := hx
  have hpx' : aeval x p = 0 := hpx
  let Kb := AlgebraicClosure K
  let bA := Module.Free.chooseBasis K A
  set M : Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) K :=
    Algebra.leftMulMatrix bA x with hMdef
  have htr : Algebra.trace K A x = M.trace := Algebra.trace_eq_matrix_trace bA x
  set Mb : Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) Kb :=
    M.map (algebraMap K Kb) with hMbdef
  have hM : aeval M p = 0 := by
    have h := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix bA).restrictScalars R) x p
    rw [AlgHom.restrictScalars_apply] at h
    rw [hMdef, h, hpx', map_zero]
  have hMb : aeval Mb (p.map (algebraMap R Kb)) = 0 := by
    rw [aeval_map_algebraMap]
    have h := Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (IsScalarTower.toAlgHom R K Kb) :
        Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) K →ₐ[R]
          Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) Kb) M p
    rw [hM, map_zero] at h
    rw [← h]
    rfl
  rw [htr, ← isIntegral_algebraMap_iff (R := R) (A := K) (B := Kb) (x := M.trace)]
  have htrmap : algebraMap K Kb M.trace = Mb.trace := by
    simp [Matrix.trace, hMbdef, map_sum]
  rw [htrmap, Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : Mb.charpoly.IsRoot μ := (mem_roots (Matrix.charpoly_monic Mb).ne_zero).mp hμ
  have hdet : (Matrix.scalar _ μ - Mb).det = 0 := by
    rwa [← Matrix.eval_charpoly]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hev : Mb *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have heval : (p.map (algebraMap R Kb)).eval μ = 0 := by
    have h1 := aeval_mulVec_of_mulVec_eq_smul Mb μ v hev (p.map (algebraMap R Kb))
    rw [hMb, Matrix.zero_mulVec] at h1
    by_contra hne
    exact hv0 ((smul_eq_zero.mp h1.symm).resolve_left hne)
  exact ⟨p, hpmon, by rwa [eval_map] at heval⟩


-- created on 2026-10-13
