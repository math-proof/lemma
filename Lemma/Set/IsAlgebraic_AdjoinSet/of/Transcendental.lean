import Mathlib
import sympy.Basic
open Set Cardinal


/--
[AlgebraicCurve_isAlgebraic_adjoin_of_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {x : F} [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
  {t : F}
-- given
  (ht : Transcendental K t) :
-- imply
  Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
-- proof
  have hx : Transcendental K x := by
    intro hxalg
    let _ : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    let _ : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    apply ht (Algebra.IsAlgebraic.isAlgebraic t)
  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    apply (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg
  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind
  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h


-- created on 2026-10-20
