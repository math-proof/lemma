import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
  {X : (Scheme : Type (u + 1))} (c : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X]
  {Y : (Scheme : Type (u + 1))} [IsIntegral Y]
  (e₀ : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₀]
  (U : X.Opens) (hU : (U : Set X).Nonempty) :
  -- imply
  genericPoint Y ∈ ((TopologicalSpace.Opens.map (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base).obj U) := by
  -- proof
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let g : Y ⟶ X := e₀ ≫ pullback.fst c ι
  change genericPoint Y ∈ ((TopologicalSpace.Opens.map g.base).obj U)
  have hηU : genericPoint X ∈ (U : Set X) := ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let z₀ : ↥(pullback c ι) := e₀ (genericPoint Y)
  have hz : ∀ z : ↥(pullback c ι), c (pullback.fst c ι z) = ι (pullback.snd c ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hbot : ∀ w : ↥(Spec (CommRingCat.of K)), (show PrimeSpectrum R from ι w).asIdeal = ⊥ := fun w => by
    change (PrimeSpectrum.comap (algebraMap R K) w).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal]
    have hw : (show PrimeSpectrum K from w).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap (algebraMap R K) (show PrimeSpectrum K from w).asIdeal = ⊥
    rw [hw, Ideal.comap_bot_of_injective _ hinj]
  have hle : (show PrimeSpectrum R from c (genericPoint X)).asIdeal ≤ ⊥ := by
    rw [← hbot (pullback.snd c ι z₀), PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.le_iff_specializes]
    change c (genericPoint X) ⤳ ι (pullback.snd c ι z₀)
    rw [← hz z₀]
    apply (genericPoint_specializes (pullback.fst c ι z₀)).map c.continuous
  have hcη : c (genericPoint X) = ι (pullback.snd c ι z₀) := PrimeSpectrum.ext ((le_bot_iff.1 hle).trans (hbot _).symm)
  have hrange : genericPoint X ∈ Set.range (pullback.fst c ι) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨pullback.snd c ι z₀, hcη.symm⟩
  obtain ⟨z, hz'⟩ := hrange
  have hgy : g (inv e₀ z) = genericPoint X := by
    change (inv e₀ ≫ e₀ ≫ pullback.fst c ι) z = genericPoint X
    rw [IsIso.inv_hom_id_assoc]
    apply hz'
  have hsp : g (genericPoint Y) ⤳ genericPoint X := hgy ▸ (genericPoint_specializes (inv e₀ z)).map g.continuous
  refine hsp.mem_open U.isOpen hηU


-- created on 2026-10-20
