import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
open UniformSpace Filter Topology Finset in IsDedekindDomain
open scoped Topology
open IsDedekindDomain


/--
[completion_universal_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean)
-/
@[path]
lemma completion_universal_property
  {K : Type*}
  [Field K]
  {v : AbsoluteValue K ℝ}
  {L : Type*}
  [Field L]
  [UniformSpace L]
  [CompleteSpace L]
  [T0Space L]
  [IsTopologicalRing L]
  [IsUniformAddGroup L]
  {f : WithAbs v →+* L}
-- given
  (hf : Continuous f)
  (hf_inj : Function.Injective f) :
-- imply
  ∃ g : Completion (WithAbs v) →+* L, Continuous g ∧ (∀ x : WithAbs v, g x = f x) ∧ (∀ g' : Completion (WithAbs v) →+* L, Continuous g' → (∀ x : WithAbs v, g' x = f x) → (g' : Completion (WithAbs v) → L) = (g : Completion (WithAbs v) → L)) := by
-- proof
  clear hf_inj
  refine ⟨Completion.extensionHom f hf,
    Completion.continuous_extension,
    fun x => Completion.extensionHom_coe f hf x,
    fun g' hg'_cont hg'_coe => ?_⟩
  have hf_uc : UniformContinuous f :=
    uniformContinuous_addMonoidHom_of_continuous (show Continuous (f : WithAbs v →+ L) from hf)
  have h1 : Completion.extension (⇑f) = (⇑g') :=
    Completion.extension_unique hf_uc
      (uniformContinuous_addMonoidHom_of_continuous
        (show Continuous (g' : Completion (WithAbs v) →+ L) from hg'_cont))
      fun a => (hg'_coe a).symm
  have h2 : Completion.extension (⇑f) = ⇑(Completion.extensionHom f hf) :=
    Completion.extension_unique hf_uc
      (uniformContinuous_addMonoidHom_of_continuous
        (show Continuous (Completion.extensionHom f hf : Completion (WithAbs v) →+ L)
          from Completion.continuous_extension))
      fun a => (Completion.extensionHom_coe f hf a).symm
  rw [← h2, h1]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

/--
[absoluteValue_same_topology_iff_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean)
-/
@[path]
lemma absoluteValue_same_topology_iff_equiv
  [Field K]
  {v w : AbsoluteValue K ℝ} :
-- imply
  v.inducedTopology = w.inducedTopology ↔ v.IsEquiv w := by
-- proof
  have hcomp : (WithAbs.toAbs w : K → WithAbs w) =
    (WithAbs.congr v w (.refl K)) ∘ (WithAbs.toAbs v) := rfl
  simp only [AbsoluteValue.inducedTopology]
  rw [hcomp, ← induced_compose]
  have he_symm : ⇑(WithAbs.equiv v).toEquiv.symm = WithAbs.toAbs v := rfl
  rw [← he_symm]
  set e := (WithAbs.equiv v).toEquiv
  have cancel : ∀ t : TopologicalSpace (WithAbs v),
    TopologicalSpace.coinduced (⇑e.symm) (TopologicalSpace.induced (⇑e.symm) t) = t := by
    intro t
    rw [Equiv.induced_symm, coinduced_compose]
    have : (⇑e.symm) ∘ (⇑e) = id := funext (fun x => e.symm_apply_apply x)
    rw [this, coinduced_id]
  constructor
  ·
    intro h
    have heq : (inferInstance : TopologicalSpace (WithAbs v)) =
      TopologicalSpace.induced (⇑(WithAbs.congr v w (.refl K))) inferInstance := by
      have h1 := cancel (inferInstance : TopologicalSpace (WithAbs v))
      have h2 := cancel (TopologicalSpace.induced (⇑(WithAbs.congr v w (.refl K)))
        (inferInstance : TopologicalSpace (WithAbs w)))
      rw [h] at h1; rw [← h1, h2]
    rw [AbsoluteValue.isEquiv_iff_isHomeomorph, isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨⟨⟨heq⟩, (RingEquiv.bijective _).1⟩, (RingEquiv.bijective _).2⟩
  ·
    intro h
    rw [AbsoluteValue.isEquiv_iff_isHomeomorph] at h
    exact congrArg _ h.isInducing.eq_induced
open IsDedekindDomain

/--
[weak_approximation_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean)
-/
@[path]
private lemma weak_approximation_theorem_eq
  [Field K]
  [Fintype ι]
  [DecidableEq ι]
  {v : ι → AbsoluteValue K ℝ}
  {a : ι → K}
  {ε : ι → ℝ}
-- given
  (hv_nontrivial : ∀ i, (v i).IsNontrivial)
  (hv_ineq : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j))
  (hε : ∀ i, 0 < ε i) :
-- imply
  ∃ x : K, ∀ i, v i (x - a i) < ε i := by
-- proof
  apply weak_approximation_theorem v hv_nontrivial hv_ineq a ε hε

/--
[intValuation_algebraMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean)
-/
@[path]
private lemma intValuation_algebraMap_eq_eq
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [FaithfulSMul R S]
  {P : HeightOneSpectrum R}
  {Q : HeightOneSpectrum S}
  [Q.asIdeal.LiesOver P.asIdeal]
  {r : R} :
-- imply
  Q.intValuation (algebraMap R S r) = (P.intValuation r) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
-- proof
  apply intValuation_algebraMap_eq P Q r

/--
[valuation_extends_with_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean)
-/
@[path]
private lemma valuation_extends_with_ramificationIdx_eq
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [FaithfulSMul R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra R L]
  [IsScalarTower R S L]
  [Algebra K L]
  [IsScalarTower R K L]
  {P : HeightOneSpectrum R}
  {Q : HeightOneSpectrum S}
  [Q.asIdeal.LiesOver P.asIdeal]
  {x : K} :
-- imply
  Q.valuation L (algebraMap K L x) = (P.valuation K x) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
-- proof
  apply valuation_extends_with_ramificationIdx K L P Q x


-- created on 2026-10-23
