import Mathlib
import sympy.Basic
import Theorem.RingTheory.DiscreteValuationRing.Monogenic
open IsLocalRing
open IsDiscreteValuationRing


namespace IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
/--
[map_maximalIdeal_ne_bot'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
residue field `ResidueField A`, hence itself a field. -/
private lemma map_maximalIdeal_ne_bot' :
  (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
  intro hbot
  have hvan : ∀ a ∈ maximalIdeal A, algebraMap A B a = 0 := by
    intro a ha
    have hmem : algebraMap A B a ∈ (maximalIdeal A).map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ ha
    rw [hbot] at hmem
    exact (Submodule.mem_bot B).mp hmem
  let φ : ResidueField A →+* B := Ideal.Quotient.lift _ (algebraMap A B) hvan
  have hφ : ∀ a : A, φ (residue A a) = algebraMap A B a := fun a =>
    Ideal.Quotient.lift_mk _ _ _
  let _ : Algebra (ResidueField A) B := φ.toAlgebra
  have hcomp : (algebraMap (ResidueField A) B).comp (residue A) = algebraMap A B := by
    ext a
    exact hφ a
  let _ : Algebra.IsIntegral (ResidueField A) B :=
    Algebra.isIntegral_def.mpr fun x => by
      obtain ⟨p, hmonic, hpx⟩ := Algebra.IsIntegral.isIntegral (R := A) (A := B) x
      rw [← Polynomial.aeval_def] at hpx
      refine ⟨p.map (residue A), hmonic.map _, ?_⟩
      rwa [← Polynomial.aeval_def, ← Polynomial.aeval_eq_aeval_map hcomp]
  have hfield : IsField B :=
    isField_of_isIntegral_of_isField' (Field.toIsField (ResidueField A))
  exact not_isField B hfield
set_option linter.unusedSectionVars false in

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
/--
[algebraMap_injective_of_map_ne_bot'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
of `A` to map to zero, killing the extended maximal ideal. -/
private lemma algebraMap_injective_of_map_ne_bot'
  (hJ : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
  Function.Injective (algebraMap A B) := by
  obtain ⟨ϖA, hϖA⟩ := exists_irreducible A
  have hϖA_ne : algebraMap A B ϖA ≠ 0 := by
    intro h0
    apply hJ
    rw [hϖA.maximalIdeal_eq, Ideal.map_span]
    simp [h0]
  suffices h0 : ∀ a : A, algebraMap A B a = 0 → a = 0 by
    intro a b hab
    have hsub : algebraMap A B (a - b) = 0 := by simp [hab]
    exact sub_eq_zero.mp (h0 _ hsub)
  intro a ha0
  by_contra hane
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hane hϖA
  have hmap : algebraMap A B (↑u * ϖA ^ n) = 0 := ha0
  rw [map_mul, map_pow] at hmap
  have huB : IsUnit (algebraMap A B (↑u : A)) := (Units.isUnit u).map _
  rw [huB.mul_right_eq_zero] at hmap
  obtain _ | n := n
  · simp only [pow_zero] at hmap
    exact one_ne_zero hmap
  · exact hϖA_ne ((pow_eq_zero_iff (Nat.succ_ne_zero n)).mp hmap)
set_option linter.unusedSectionVars false in

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
/--
[faithfulSMul_of_map_ne_bot'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
private lemma faithfulSMul_of_map_ne_bot'
  (hJ : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) : FaithfulSMul A B := by
  rw [faithfulSMul_iff_injective_smul_one]
  have hinj := algebraMap_injective_of_map_ne_bot' hJ
  have heq : (fun r : A => r • (1 : B)) = algebraMap A B := by
    funext r
    exact (Algebra.algebraMap_eq_smul_one r).symm
  rwa [heq]

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[exists_generator_with_residue_minpoly_uniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
lemma exists_generator_with_residue_minpoly_uniformizer
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
-- imply
  ∃ (α : B) (F : Polynomial A),
    Algebra.adjoin A ({α} : Set B) = ⊤ ∧
    Algebra.adjoin (ResidueField A)
    ({residue B α} : Set (ResidueField B)) = ⊤ ∧
    F.Monic ∧
    F.map (residue A) =
    minpoly (ResidueField A) (residue B α) ∧
    IsUnit (Polynomial.aeval α F.derivative) ∧
    maximalIdeal B = Ideal.span {Polynomial.aeval α F} := by
-- proof
  obtain ⟨ϖB, hϖB⟩ := exists_irreducible B
  have hJbot : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := map_maximalIdeal_ne_bot'
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hJbot hϖB
  have hmBpow : maximalIdeal B ^ n = (maximalIdeal A).map (algebraMap A B) := by
    rw [hϖB.maximalIdeal_eq, Ideal.span_singleton_pow, hn]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  have hadj : Algebra.adjoin (ResidueField A) ({α} : Set _) = ⊤ := by
    have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite _ _ : IsAlgebraic (ResidueField A) α)
    rwa [hα, IntermediateField.top_toSubalgebra] at h
  obtain ⟨x, hx⟩ := residue_surjective (R := B) α
  have hmem : minpoly (ResidueField A) α ∈ Polynomial.lifts (residue A) :=
    Polynomial.mem_lifts_of_surjective residue_surjective _
  have hmonic_res : (minpoly (ResidueField A) α).Monic :=
    minpoly.monic ((IsAlgebraic.of_finite _ _ : IsAlgebraic (ResidueField A) α).isIntegral)
  obtain ⟨F, hF, -, hFmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hmem hmonic_res
  have hFx0 : residue B (Polynomial.aeval x F) = 0 := by
    rw [Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl F x,
      hF, hx]
    exact minpoly.aeval _ _
  have hFx_mem : Polynomial.aeval x F ∈ maximalIdeal B :=
    (residue_eq_zero_iff _).mp hFx0
  have hFx_span : Polynomial.aeval x F ∈ Ideal.span {ϖB} := by
    rwa [← hϖB.maximalIdeal_eq]
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hFx_span
  have hderiv : IsUnit (Polynomial.aeval x F.derivative) := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl
      F.derivative x, ← Polynomial.derivative_map, hF, hx]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  have hϖBmem : ϖB ∈ maximalIdeal B := by
    rw [hϖB.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self _
  have hϖ0 : residue B ϖB = 0 := (residue_eq_zero_iff _).mpr hϖBmem
  obtain ⟨c, -, hne⟩ : ∃ c : A, (c = 0 ∨ c = 1) ∧
    residue B w + algebraMap (ResidueField A) (ResidueField B) (residue A c) *
      residue B (Polynomial.aeval x F.derivative) ≠ 0 := by
    by_cases hw0 : residue B w = 0
    · refine ⟨1, Or.inr rfl, ?_⟩
      simp only [hw0, map_one, one_mul, zero_add]
      exact (residue_ne_zero_iff_isUnit _).mpr hderiv
    · refine ⟨0, Or.inl rfl, ?_⟩
      simp only [map_zero, zero_mul, add_zero]
      exact hw0
  set y : B := x + algebraMap A B c * ϖB with hy
  set S : Subalgebra A B := Algebra.adjoin A {y} with hS
  obtain ⟨C, hC⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
    (F.map (algebraMap A B)) x (algebraMap A B c * ϖB)
  have hGx : (F.map (algebraMap A B)).eval x = Polynomial.aeval x F := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hGd : (F.map (algebraMap A B)).derivative.eval x =
    Polynomial.aeval x F.derivative := by
    rw [Polynomial.derivative_map, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hGy : (F.map (algebraMap A B)).eval (x + algebraMap A B c * ϖB) =
    Polynomial.aeval y F := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← hy]
  set v : B := w + algebraMap A B c * Polynomial.aeval x F.derivative +
    C * (algebraMap A B c) ^ 2 * ϖB with hvdef
  have hgy : Polynomial.aeval y F = ϖB * v := by
    have hQ2 : C * (algebraMap A B c * ϖB) ^ 2 +
      Polynomial.aeval x F.derivative * (algebraMap A B c * ϖB) +
      Polynomial.aeval x F = Polynomial.aeval y F := by
      rwa [← hGy, ← hGx, ← hGd]
    rw [hw] at hQ2
    rw [hvdef, ← hQ2]
    ring
  have hresv : residue B v ≠ 0 := by
    have hcalc : residue B v = residue B w +
      residue B (algebraMap A B c) * residue B (Polynomial.aeval x F.derivative) := by
      rw [hvdef, map_add, map_add, map_mul, map_mul, map_mul, map_pow, hϖ0]
      ring
    have hcc : residue B (algebraMap A B c) =
      algebraMap (ResidueField A) (ResidueField B) (residue A c) :=
      (ResidueField.algebraMap_residue c).symm
    rwa [hcalc, hcc]
  obtain ⟨e, he⟩ := (residue_ne_zero_iff_isUnit _).mp hresv
  have hmBspan : maximalIdeal B = Ideal.span {Polynomial.aeval y F} := by
    rw [hϖB.maximalIdeal_eq, hgy, ← he]
    exact (Ideal.span_singleton_eq_span_singleton).mpr ⟨e, rfl⟩
  have hgBmem : Polynomial.aeval y F ∈ maximalIdeal B := by
    rw [hmBspan]
    exact Ideal.mem_span_singleton_self _
  have hgS : Polynomial.aeval y F ∈ S := by
    rw [hS, Algebra.adjoin_singleton_eq_range_aeval A y]
    exact ⟨F, rfl⟩
  have hresy : residue B y = α := by
    have : residue B y = residue B x + residue B (algebraMap A B c) * residue B ϖB := by
      rw [hy, map_add, map_mul]
    rw [this, hϖ0, mul_zero, add_zero, hx]
  have hrange : (Polynomial.aeval (R := ResidueField A) α).range =
    (⊤ : Subalgebra (ResidueField A) (ResidueField B)) :=
    (Algebra.adjoin_singleton_eq_range_aeval (ResidueField A) α).symm.trans hadj
  have step1 : ∀ t : B, ∃ s ∈ S, ∃ t', t = s + Polynomial.aeval y F * t' := by
    intro t
    have hmem : residue B t ∈ (Polynomial.aeval (R := ResidueField A) α).range := by
      rwa [hrange]
    obtain ⟨q, hq⟩ := (AlgHom.mem_range _).mp hmem
    obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) residue_surjective q
    have hs0 : residue B (Polynomial.aeval y P) = residue B t := by
      rw [Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl P y,
        hP, hresy]
      exact hq
    have hmemB : t - Polynomial.aeval y P ∈ maximalIdeal B := by
      rw [← residue_eq_zero_iff, map_sub, hs0, sub_self]
    rw [hmBspan] at hmemB
    obtain ⟨t', ht'⟩ := (Ideal.mem_span_singleton').mp hmemB
    refine ⟨Polynomial.aeval y P, ?_, t', ?_⟩
    · rw [hS, Algebra.adjoin_singleton_eq_range_aeval A y]
      exact ⟨P, rfl⟩
    · have h2 : Polynomial.aeval y F * t' = t - Polynomial.aeval y P := by
      rw [← ht']; ring
      exact ((sub_eq_iff_eq_add).mp h2.symm).trans (add_comm _ _)
  have stepIter : ∀ (i : ℕ) (b : B), ∃ s ∈ S, ∃ t,
    b = s + (Polynomial.aeval y F) ^ i * t := by
    intro i
    induction i with
    | zero => exact fun b => ⟨0, S.zero_mem, b, by simp⟩
    | succ i ih =>
      intro b
      obtain ⟨s, hs, t', hb⟩ := ih b
      obtain ⟨s2, hs2, t2, ht2⟩ := step1 t'
      refine ⟨s + (Polynomial.aeval y F) ^ i * s2,
        S.add_mem hs (S.mul_mem (S.pow_mem hgS i) hs2), t2, ?_⟩
      rw [hb, ht2, pow_succ]; ring
  have hfinal : (⊤ : Submodule A B) ≤ S.toSubmodule ⊔ maximalIdeal A • ⊤ := by
    rw [Ideal.smul_top_eq_map]
    intro b _
    obtain ⟨s, hs, t, ht⟩ := stepIter n b
    have hgn : (Polynomial.aeval y F) ^ n ∈ (maximalIdeal A).map (algebraMap A B) :=
      hmBpow ▸ Ideal.pow_mem_pow hgBmem n
    have hgt : (Polynomial.aeval y F) ^ n * t ∈
      ((maximalIdeal A).map (algebraMap A B)).restrictScalars A :=
      ((maximalIdeal A).map (algebraMap A B)).mul_mem_right t hgn
    exact (Submodule.mem_sup).mpr
      ⟨s, hs, _, hgt, ht.symm⟩
  have hfin : (⊤ : Submodule A B).FG := Module.finite_def.mp inferInstance
  have hle : (⊤ : Submodule A B) ≤ S.toSubmodule :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfin
      (maximalIdeal_le_jacobson (⊥ : Ideal A)) hfinal
  have hSeq : S = ⊤ := by
    rw [eq_top_iff]
    intro b _
    exact hle Submodule.mem_top
  have hderivY : IsUnit (Polynomial.aeval y F.derivative) := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl
      F.derivative y, ← Polynomial.derivative_map, hF, hresy]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  have hresgen : Algebra.adjoin (ResidueField A)
    ({residue B y} : Set (ResidueField B)) = ⊤ := by
    rwa [hresy]
  have hFmap : F.map (residue A) = minpoly (ResidueField A) (residue B y) := by
    rwa [hresy]
  have hSeq' : Algebra.adjoin A ({y} : Set B) = ⊤ := by
    rwa [← hS]
  exact ⟨y, F, hSeq', hresgen, hFmonic, hFmap, hderivY, hmBspan⟩

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[exists_adjoin_eq_top_of_separable_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
lemma exists_adjoin_eq_top_of_separable_residueField
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
-- imply
  ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ := by
-- proof
  obtain ⟨α, -, hgen, _, _, _, _, _⟩ :=
    exists_generator_with_residue_minpoly_uniformizer (A := A) (B := B)
  exact ⟨α, hgen⟩

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[adjoin_eq_top_of_lift_of_map_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
lemma adjoin_eq_top_of_lift_of_map_maximalIdeal
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {β : B}
-- given
  (hunram : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hβ : Algebra.adjoin (ResidueField A) ({residue B β} : Set _) = ⊤) :
-- imply
  Algebra.adjoin A ({β} : Set B) = ⊤ := by
-- proof
  have hJ : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [hunram]
    exact not_a_field (R := B)
  have hFS : FaithfulSMul A B := faithfulSMul_of_map_ne_bot' hJ
  have hFU : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hunram
  exact (@adjoin_residue_eq_top_iff_adjoin_eq_top A B _ _ _ _ _ _ hFS hFU β).mp hβ
set_option linter.unusedSectionVars false in

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[etale_of_isSeparable_residueField_of_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/Monogenic.lean)
-/
@[path]
lemma etale_of_isSeparable_residueField_of_finrank_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
-- given
  (hfin : Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) :
-- imply
  Algebra.Etale A B := by
-- proof
  have hJbot : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := map_maximalIdeal_ne_bot'
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_map_ne_bot' hJbot
  have hTF : Module.IsTorsionFree A B :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  let _ : Module.IsTorsionFree A B := hTF
  let _ : Module.Free A B := Module.free_of_finite_type_torsion_free'
  let _ : Module.Flat A B := Module.Flat.of_free
  let _ : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  obtain ⟨beta, hbeta⟩ := exists_adjoin_eq_top_of_separable_residueField (A := A) (B := B)
  have hbeta0 : Algebra.adjoin (ResidueField A) ({residue B beta} : Set _) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hbeta ⊢
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) y
    obtain ⟨p, hp⟩ := hbeta b
    refine ⟨p.map (residue A), ?_⟩
    rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl]
    simp [hp]
  set p := minpoly A beta with hpdef
  have hmap : p.map (residue A) = minpoly (ResidueField A) (residue B beta) := by
    have hmonic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := A) beta)
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral (residue B beta)))
      (hmonic.map _) (minpoly.dvd _ _ ?_) ?_
    · rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl]
      simp [p]
    · rw [hmonic.natDegree_map _,
      ← (IsAdjoinRootMonic.mkOfAdjoinEqTop' hbeta).finrank,
      hfin, (IsAdjoinRootMonic.mkOfAdjoinEqTop' hbeta0).finrank]
  have hsep : (p.map (residue A)).Separable := by
    rw [hmap]
    exact Algebra.IsSeparable.isSeparable _ _
  exact (Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly (R := A)
    (S := B)).mpr ⟨beta, hbeta, hsep⟩

end IsDiscreteValuationRing


-- created on 2026-10-20
-- updated on 2026-10-23
