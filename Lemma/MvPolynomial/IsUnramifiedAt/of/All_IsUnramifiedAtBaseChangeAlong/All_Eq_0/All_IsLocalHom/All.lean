import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_isUnramifiedAt_of_forall_point](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isUnramifiedAt_of_forall_point.lean)
-/
@[path]
private lemma main
  [CommRing P] [IsLocalRing P]
  {A : ι → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
  {ρ : GaloisRepAdic P}
  {q : ℕ}
-- given
  (χ : ∀ i, P →+* A i)
  (hχ : ∀ i, IsLocalHom (χ i))
  (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
  (h : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsUnramifiedAt q) :
-- imply
  ρ.IsUnramifiedAt q := by
-- proof
  classical
  intro Q hQ σ hσ
  let e : Module.Basis (Fin 2) P ρ.V := Module.finBasisOfFinrankEq P ρ.V ρ.finrank_eq

  have key : ∀ (k : ι) (i j : Fin 2), χ k (LinearMap.toMatrix e e (ρ.ρ σ - 1) i j) = 0 := by
    intro k i j
    letI : Algebra P (A k) := (χ k).toAlgebra
    have h1 : ((ρ.ρ σ - 1).baseChange (A k)) = 0 := by
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
      exact sub_eq_zero.mpr (h k Q hQ σ hσ)
    have h2 := congrArg (fun T => LinearMap.toMatrix (Algebra.TensorProduct.basis (A k) e)
      (Algebra.TensorProduct.basis (A k) e) T i j) h1
    simp only [LinearMap.toMatrix_baseChange, Matrix.map_apply, map_zero, Matrix.zero_apply] at h2
    rw [RingHom.algebraMap_toAlgebra] at h2
    exact h2
  have hzero : ρ.ρ σ - 1 = 0 :=
    (LinearMap.toMatrix e e).map_eq_zero_iff.mp (Matrix.ext fun i j => hinj _ fun k => key k i j)
  exact sub_eq_zero.mp hzero


-- created on 2026-10-23
