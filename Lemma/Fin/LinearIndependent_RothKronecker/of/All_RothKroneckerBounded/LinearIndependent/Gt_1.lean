import Mathlib
import Lemma.Fin.RothKroneckerBounded_Sum.of.All_RothKroneckerBounded
import Lemma.Fin.RothKronecker.ne.Zero.of.Ne_0.Gt_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothKronecker_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k D : ℕ} [Field K]
-- given
  (f : Fin k → MvPolynomial (Fin m) K)
  (hD : 1 < D)
  (hf : LinearIndependent K f)
  (hb : ∀ j, rothKroneckerBounded D (f j)) :
-- imply
  LinearIndependent K (fun j ↦ rothKronecker D (f j)) := by
-- proof
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let P := ∑ a, c a • f a
  have hmap : rothKronecker D P = 0 := by
    dsimp [P]
    rw [map_sum]
    simpa [Algebra.smul_def, rothKronecker] using hc
  have hPb : rothKroneckerBounded D P := by
    dsimp [P]
    apply RothKroneckerBounded_Sum.of.All_RothKroneckerBounded Finset.univ
    intro a _ i hi h
    if hca : c a = 0 then
      simp [hca] at hi
    else
      have hsupp : (c a • f a).support = (f a).support :=
        MvPolynomial.support_smul_eq hca (f a)
      rw [hsupp] at hi
      exact hb a i hi h
  apply Fintype.linearIndependent_iff.mp hf c _ j
  by_contra hP
  exact RothKronecker.ne.Zero.of.Ne_0.Gt_1 hD hP hPb hmap


-- created on 2026-10-21
