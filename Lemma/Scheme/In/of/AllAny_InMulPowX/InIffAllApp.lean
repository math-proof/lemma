import Mathlib
import Initialize.Tactic.Attr.Basic
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


attribute [instance] MvPolynomial.gradedAlgebra

private noncomputable def awayMk
  {n : ℕ} {k : Type} [CommRing k]
  (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n + 1)) :
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := Subtype.mk F ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)
      den := Subtype.mk (X i ^ d)
        ((MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d))
      den_mem := ⟨d, rfl⟩ }

/--
[AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero.lean)
-/
@[path]
private lemma main
  {n : ℕ} {k : Type} [Field k]
  {Zk : Scheme} {ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)}
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
-- given
  (hZ : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
    (F ∈ I ↔ ∀ i : Fin (n + 1),
      (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (awayMk d F hF i)) = 0))
  {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d)
  (hsat : ∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I) :
-- imply
  F ∈ I := by
-- proof
  rw [hZ d F hF]
  intro i
  obtain ⟨N, hN⟩ := hsat i
  have hG : (X i ^ N * F).IsHomogeneous (N + d) := (MvPolynomial.isHomogeneous_X_pow i N).mul hF
  have h := (hZ (N + d) (X i ^ N * F) hG).mp hN i
  have heq : awayMk (N + d) (X i ^ N * F) hG i = awayMk d F hF i := by
    apply HomogeneousLocalization.val_injective
    unfold awayMk
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp [OneMemClass.coe_one, one_mul]
    ring
  rw [← heq]
  apply h


-- created on 2026-10-20
