import Mathlib
import Initialize.Tactic.Attr.Basic
open IntermediateField


private lemma finiteDimensional_adjoin_of_transcendental
  {K F : Type} [Field K] [Field F] [Algebra K F]
  {x₀ t : F}
-- given
  (hx₀ : Transcendental K x₀)
  (hfd : FiniteDimensional K⟮x₀⟯ F)
  (ht : Transcendental K t) :
-- imply
  FiniteDimensional K⟮t⟯ F := by
-- proof
  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun _ : Fin 1 => x₀)) F := by
    have : Algebra.IsAlgebraic K⟮x₀⟯ F := Algebra.IsAlgebraic.of_finite _ _
    rw [Set.range_const]
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp this
  have hb₀ : IsTranscendenceBasis K (fun _ : Fin 1 => x₀) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨(algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hx₀, halg₀⟩
  have htr : Algebra.trdeg K F = Cardinal.mk (Fin 1) := hb₀.cardinalMk_eq_trdeg.symm
  have hbt : IsTranscendenceBasis K (fun _ : Fin 1 => t) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (0 : Fin 1)).mpr ht) htr.le
  have halg : Algebra.IsAlgebraic K⟮t⟯ F := by
    have h := hbt.isAlgebraic_field
    rwa [Set.range_const] at h
  set L := K⟮t⟯
  have hint : IsIntegral L x₀ := (halg.isAlgebraic x₀).isIntegral
  set N : IntermediateField L F := L⟮x₀⟯
  let _ : FiniteDimensional L N := IntermediateField.adjoin.finiteDimensional hint
  have hmem : ∀ s : K⟮x₀⟯, (s : F) ∈ N := by
    intro s
    have hle : K⟮x₀⟯ ≤ N.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self L x₀)
    refine hle s.2
  let _ : Algebra K⟮x₀⟯ N := RingHom.toAlgebra
    { toFun := fun s => ⟨(s : F), hmem s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : IsScalarTower K⟮x₀⟯ N F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Module.Finite N F := Module.Finite.of_restrictScalars_finite K⟮x₀⟯ N F
  apply Module.Finite.trans N F
/--
[AlgebraicCurve_finite_intermediateField_of_transcendental_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finite_intermediateField_of_transcendental_mem.lean)
-/
@[path]
private lemma main
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {E : IntermediateField K L} {t : L}
-- given
  (htE : t ∈ E) (ht : Transcendental K t)
  (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set L)) L) :
-- imply
  Module.Finite ↥E L := by
-- proof
  obtain ⟨x, hx, hfd⟩ := hfg
  have hfin : FiniteDimensional K⟮t⟯ L := finiteDimensional_adjoin_of_transcendental hx hfd ht
  have hle : K⟮t⟯ ≤ E := IntermediateField.adjoin_simple_le_iff.mpr htE
  let _ : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  let _ : IsScalarTower K⟮t⟯ E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Module.Finite.of_restrictScalars_finite K⟮t⟯ E L


-- created on 2026-10-20
