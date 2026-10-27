import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma range_toGL_eq_ker_det (p : ℕ) [Fact p.Prime] : (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).range = (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* Units (ZMod p)).ker := by
  ext g
  constructor
  ·
    rintro ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Matrix.SpecialLinearGroup.coeToGL_det s
  ·
    intro hg
    rw [MonoidHom.mem_ker] at hg
    have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
      have := congrArg Units.val hg
      simpa using this
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) (ZMod p)), hdet⟩, ?_⟩
    apply Units.ext
    rfl
private lemma det_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* Units (ZMod p)) := by
  intro u
  let A : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.diagonal (Matrix.vecCons (u : ZMod p) (Matrix.vecCons (1 : ZMod p) Matrix.vecEmpty))
  have hA : Matrix.det A = (u : ZMod p) := by
    simp [A, Matrix.det_diagonal, Fin.prod_univ_two]
  have hA0 : Matrix.det A ≠ 0 := by
    rw [hA]
    apply u.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0, ?_⟩
  apply Units.ext
  show Matrix.det ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = u
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hA]
private lemma card_GL_two (p : ℕ) [Fact p.Prime] : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [Matrix.card_GL_field 2, Fin.prod_univ_two, ZMod.card p]
  simp
/--
[Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime] :
  -- imply
  Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  -- proof
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set detH : GL (Fin 2) (ZMod p) →* Units (ZMod p) := Matrix.GeneralLinearGroup.det with hdetH
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup detH.ker
  have h2 : Nat.card (GL (Fin 2) (ZMod p) ⧸ detH.ker) = p - 1 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange detH).toEquiv, MonoidHom.range_eq_top.mpr (det_surjective p), Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]
  have h3 : Nat.card detH.ker = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [hdetH, ← range_toGL_eq_ker_det p]
    apply (Nat.card_congr (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv).symm
  rw [card_GL_two p, h2, h3] at h1
  have h4 : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  rw [h4] at h1
  have hp1 : 0 < p - 1 := by omega
  have h5 : (p - 1) * (p * (p ^ 2 - 1)) = (p - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [← h1]
    ring
  refine (Nat.eq_of_mul_eq_mul_left hp1 h5).symm


-- created on 2026-10-20
