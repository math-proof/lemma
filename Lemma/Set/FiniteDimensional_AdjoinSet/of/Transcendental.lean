import Mathlib
import sympy.Basic
open Set Cardinal


private lemma isAlgebraic_adjoin_of_transcendental'
  {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hx : Transcendental K x := by
    intro hxalg
    let _ : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    let _ : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)
  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg
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
private lemma finiteDimensional_adjoin_of_transcendental'
  {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  let halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    isAlgebraic_adjoin_of_transcendental' x ht
  set E := IntermediateField.adjoin K ({t} : Set F)
  set Kx := IntermediateField.adjoin K ({x} : Set F)
  let b := Module.finBasis Kx F
  let S : Set F := insert x (Set.range b)
  let _ : Finite S := Set.Finite.insert x (Set.finite_range b) |>.to_subtype
  let hM : FiniteDimensional E (IntermediateField.adjoin E S) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (halg.isAlgebraic y).isIntegral
  have htop : IntermediateField.adjoin E S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hKx : ∀ c : Kx, (c : F) ∈ IntermediateField.adjoin E S := by
      intro c
      have hle : Kx ≤ (IntermediateField.adjoin E S).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin E S (Set.mem_insert _ _)
      refine hle c.2
    rw [← b.sum_repr y]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [IntermediateField.smul_def]
    exact mul_mem (hKx _) (IntermediateField.subset_adjoin E S (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rw [htop] at hM
  apply (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

/--
[AlgebraicCurve_finiteDimensional_adjoin_of_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {x : F} [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
  {t : F}
-- given
  (ht : Transcendental K t) :
-- imply
  FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
-- proof
  apply finiteDimensional_adjoin_of_transcendental' x ht


-- created on 2026-10-20
