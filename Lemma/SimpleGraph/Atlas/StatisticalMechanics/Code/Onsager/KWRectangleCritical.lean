import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWRectangleCritical
open StatMech StatMech.Onsager


/--
[ons_rectTailDartEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectTailDartEquiv_apply_eq
  {M N : Nat}
  {d : ons_RectDart M N} :
-- imply
  ons_rectTailDartEquiv M N d = (ons_rectDirStep M N (d.2 + 2) d.1, d.2) := by
-- proof
  apply StatMech.Onsager.ons_rectTailDartEquiv_apply M N d

/--
[ons_rectDartBoundaryRank_tail_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectDartBoundaryRank_tail_lt_eq
  {M N : Nat}
  {d : ons_RectDart M N}
-- given
  (hd : ons_rectDartValid M N d)
  (htail : ons_rectDartValid M N (ons_rectTailDartEquiv M N d)) :
-- imply
  ons_rectDartBoundaryRank M N (ons_rectTailDartEquiv M N d) < ons_rectDartBoundaryRank M N d := by
-- proof
  apply StatMech.Onsager.ons_rectDartBoundaryRank_tail_lt M N d hd htail

/--
[ons_arrivalTurnMatrixOf_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrixOf_isHermitian_eq
  {S : Type*}
  [DecidableEq S] :
-- imply
  (ons_arrivalTurnMatrixOf S).IsHermitian := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrixOf_isHermitian S

/--
[ons_arrivalTurnMatrixOf_centered_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrixOf_centered_apply_eq
  {S : Type*}
  [DecidableEq S]
  {d2 d1 : S × Fin 4} :
-- imply
  (ons_arrivalTurnMatrixOf S - 1) d2 d1 = if d2.1 = d1.1 then (ons_turnMatrix ons_turnRoot - 1) d2.2 d1.2 else 0 := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrixOf_centered_apply S d2 d1

/--
[ons_arrivalTurnMatrixOf_centered_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrixOf_centered_sq_eq
  {S : Type*}
  [Fintype S]
  [DecidableEq S] :
-- imply
  (ons_arrivalTurnMatrixOf S - 1) * (ons_arrivalTurnMatrixOf S - 1) = (2 : Complex) • (1 : Matrix (S × Fin 4) (S × Fin 4) Complex) := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrixOf_centered_sq S

/--
[norm_ons_arrivalTurnMatrixOf_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_ons_arrivalTurnMatrixOf_centered_eq
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  [Nonempty S] :
-- imply
  letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) := Matrix.instL2OpNormedRing ‖ons_arrivalTurnMatrixOf S - 1‖ = Real.sqrt 2 := by
-- proof
  apply StatMech.Onsager.norm_ons_arrivalTurnMatrixOf_centered S

/--
[norm_ons_arrivalTurnMatrixOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_ons_arrivalTurnMatrixOf_le_eq
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  [Nonempty S] :
-- imply
  letI : NormedRing (Matrix (S × Fin 4) (S × Fin 4) Complex) := Matrix.instL2OpNormedRing ‖ons_arrivalTurnMatrixOf S‖ <= Real.sqrt 2 + 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_arrivalTurnMatrixOf_le S

/--
[norm_sq_arrivalTurnMatrixOf_centered_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_sq_arrivalTurnMatrixOf_centered_apply_eq
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  [Nonempty S]
  {z : EuclideanSpace Complex (S × Fin 4)} :
-- imply
  let B := ons_arrivalTurnMatrixOf S - 1 ‖Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) B z‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
-- proof
  apply StatMech.Onsager.norm_sq_arrivalTurnMatrixOf_centered_apply S z

/--
[arrivalTurnMatrixOf_apply_eq_of_norm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma arrivalTurnMatrixOf_apply_eq_of_norm_eq_eq
  {S : Type*}
  [Fintype S]
  [DecidableEq S]
  [Nonempty S]
  {z : EuclideanSpace Complex (S × Fin 4)}
-- given
  (hnorm : ‖Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S) z‖ = (Real.sqrt 2 + 1) * ‖z‖) :
-- imply
  Matrix.toEuclideanCLM (n := S × Fin 4) (𝕜 := Complex) (ons_arrivalTurnMatrixOf S) z = ((Real.sqrt 2 + 1 : Real) : Complex) • z := by
-- proof
  apply StatMech.Onsager.arrivalTurnMatrixOf_apply_eq_of_norm_eq S z hnorm

/--
[norm_ons_rectDartMask_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_ons_rectDartMask_le_eq
  {M N : Nat} :
-- imply
  letI : NormedRing (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) := by
-- proof
  apply StatMech.Onsager.norm_ons_rectDartMask_le M N

/--
[norm_ons_rectKWmat_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_ons_rectKWmat_sharp_eq
  {M N : Nat}
  {x : Complex} :
-- imply
  letI : NormedRing (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) := by
-- proof
  apply StatMech.Onsager.norm_ons_rectKWmat_sharp M N x

/--
[ons_rectDartMask_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectDartMask_apply_eq
  {M N : Nat}
  {z : EuclideanSpace Complex (ons_RectDart M N)}
  {d : ons_RectDart M N} :
-- imply
  (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectDartMask M N) z).ofLp d = if ons_rectDartValid M N d then z.ofLp d else 0 := by
-- proof
  apply StatMech.Onsager.ons_rectDartMask_apply M N z d

/--
[ons_rectTailPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectTailPerm_apply_eq
  {M N : Nat}
  {z : EuclideanSpace Complex (ons_RectDart M N)}
  {d : ons_RectDart M N} :
-- imply
  (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) ((ons_rectTailDartEquiv M N).permMatrix Complex) z).ofLp d = z.ofLp (ons_rectTailDartEquiv M N d) := by
-- proof
  apply StatMech.Onsager.ons_rectTailPerm_apply M N z d

/--
[norm_ons_rectTailPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_ons_rectTailPerm_apply_eq
  {M N : Nat}
  {z : EuclideanSpace Complex (ons_RectDart M N)} :
-- imply
  ‖Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) ((ons_rectTailDartEquiv M N).permMatrix Complex) z‖ = ‖z‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_rectTailPerm_apply M N z

/--
[ons_rectKWmat_toEuclideanCLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectKWmat_toEuclideanCLM_apply_eq
  {M N : Nat}
  {x : Complex}
  {z : EuclideanSpace Complex (ons_RectDart M N)} :
-- imply
  Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectKWmat M N x) z = x • Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectDartMask M N) (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_arrivalTurnMatrixOf (ons_RectVertex M N)) (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) ((ons_rectTailDartEquiv M N).permMatrix Complex) (Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectDartMask M N) z))) := by
-- proof
  apply StatMech.Onsager.ons_rectKWmat_toEuclideanCLM_apply M N x z

/--
[rectDartVector_eq_zero_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma rectDartVector_eq_zero_of_recurrence_eq
  {M N : Nat}
  {alpha : Complex}
  {z : EuclideanSpace Complex (ons_RectDart M N)}
-- given
  (halpha : alpha ≠ 0)
  (hboundary : ∀ d, ¬ons_rectDartValid M N d -> z.ofLp d = 0)
  (hrec : ∀ d, ons_rectDartValid M N d -> alpha * z.ofLp d = z.ofLp (ons_rectTailDartEquiv M N d)) :
-- imply
  z = 0 := by
-- proof
  apply StatMech.Onsager.rectDartVector_eq_zero_of_recurrence M N alpha halpha z hboundary hrec

/--
[ons_rectKWmat_no_unit_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectKWmat_no_unit_eigenvector_eq
  {M N : Nat}
  {alpha : Complex}
  {v : EuclideanSpace Complex (ons_RectDart M N)}
-- given
  (hunit : ‖alpha‖ = 1)
  (heigen : Matrix.toEuclideanCLM (n := ons_RectDart M N) (𝕜 := Complex) (ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)) v = alpha • v) :
-- imply
  v = 0 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmat_no_unit_eigenvector M N alpha v hunit heigen

/--
[norm_root_ons_rectKWmat_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma norm_root_ons_rectKWmat_le_eq
  {M N : Nat}
  {x alpha : Complex}
-- given
  (halpha : alpha ∈ (ons_rectKWmat M N x).charpoly.roots) :
-- imply
  ‖alpha‖ <= (Real.sqrt 2 + 1) * ‖x‖ := by
-- proof
  apply StatMech.Onsager.norm_root_ons_rectKWmat_le M N x alpha halpha

/--
[ons_rectKWmat_spectral_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectKWmat_spectral_critical_eq
  {M N : Nat} :
-- imply
  ∀ alpha ∈ (ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmat_spectral_critical M N

/--
[ons_rectKWmat_det_eq_walk_exp_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean)
-/
@[path]
private lemma ons_rectKWmat_det_eq_walk_exp_critical_eq
  {M N : Nat} :
-- imply
  (1 - ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex)).det = Complex.exp (- ∑' n : Nat, (∑ v : Fin (n + 1) -> ons_RectDart M N, ∏ k : Fin (n + 1), ons_rectKWmat M N (ons_signedLoopCriticalWeight : Complex) (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_rectKWmat_det_eq_walk_exp_critical M N


-- created on 2026-10-23
