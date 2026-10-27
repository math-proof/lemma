import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


attribute [local instance] Ideal.Quotient.field


private lemma residueFixed_algebraMap_quotient_surjective_of_forall_smul_sub_mem
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  {P : Ideal A} {Q : Ideal B} [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
-- given
  (hG : ∀ (g : G) (b : B), g • b - b ∈ Q) :
-- imply
  Function.Surjective (algebraMap (A ⧸ P) (B ⧸ Q)) := by
-- proof
  have : IsGalois (A ⧸ P) (B ⧸ Q) := { __ := Ideal.Quotient.normal (A := A) G P Q }
  have : FiniteDimensional (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.finite_of_isInvariant G P Q
  intro x
  rw [← Set.mem_range, IsGalois.mem_range_algebraMap_iff_fixed]
  intro f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq.mpr
  apply hG


/--
[Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  {P : Ideal A} {Q : Ideal B} [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
  {H : Subgroup G} {b : B}
-- given
  (hH : H ≤ Q.inertia G) :
-- imply
  ∃ b' : B, (∀ h ∈ H, h • b' = b') ∧ b - b' ∈ Q := by
-- proof
  let B' : Subalgebra A B := FixedPoints.subalgebra A B H
  have : SMulCommClass H B' B := ⟨fun h x y => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    apply congrArg (· * h • y) (x.2 h)⟩
  have : Algebra.IsInvariant B' B H := ⟨fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have : Algebra.IsIntegral B' B := Algebra.IsInvariant.isIntegral B' B H
  have : (Q.under B').IsMaximal := Ideal.IsMaximal.under B' Q
  have : IsScalarTower (A ⧸ P) (B' ⧸ Q.under B') (B ⧸ Q) :=
    IsScalarTower.of_algebraMap_eq (Quotient.ind fun x ↦ rfl)
  have : Algebra.IsSeparable (B' ⧸ Q.under B') (B ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ P) (B' ⧸ Q.under B') (B ⧸ Q)
  have hH' : ∀ (h : H) (x : B), h • x - x ∈ Q := fun h x => hH h.2 x
  obtain ⟨y, hy⟩ := residueFixed_algebraMap_quotient_surjective_of_forall_smul_sub_mem
    (P := Q.under B') (Q := Q) hH' (Ideal.Quotient.mk Q b)
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨b', fun h hh => b'.2 ⟨h, hh⟩, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hy
  apply Ideal.Quotient.eq.mp hy.symm


-- created on 2026-10-12
