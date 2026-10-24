import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FinitePlacesOver
open IsDedekindDomain
open scoped NumberField NumberField.LiesOver Valued


namespace IsDedekindDomain.HeightOneSpectrum

/--
[separableExtension_isCompletion_finitePlace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/SeparableExtension.lean)
-/
@[path]
lemma separableExtension_isCompletion_finitePlace
  {K : Type u} [Field K] [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {M : Type v} [Field M] [Algebra (v.adicCompletion K) M] [FiniteDimensional (v.adicCompletion K) M] [Algebra.IsSeparable (v.adicCompletion K) M] :
-- imply
  ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
    (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal),
    let _ : w.asIdeal.LiesOver v.asIdeal := by
-- proof
  obtain ⟨f, hf, hirr, hsep, ⟨eMf⟩⟩ :=
    (Algebra.isSeparable_iff_exists_monic_irreducible_separable
      (v.adicCompletion K) M).mp inferInstance
  obtain ⟨δ, hδ, hstable⟩ :=
    Polynomial.exists_pos_adjoinRoot_algEquiv_of_l1Norm_sub_lt
      (v.adicCompletion K) f hf hirr hsep
  obtain ⟨g, hg, hdeg, hclose, hmapirr, _⟩ :=
    Polynomial.exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable
      (v.denseRange_algebraMap K) f hf hirr hsep hδ
  obtain ⟨efg⟩ :=
    hstable (g.map (algebraMap K (v.adicCompletion K)))
      (hg.map _) hclose
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (algebraMap K (v.adicCompletion K)) g hg hmapirr
  let _ : Fact (Irreducible g) := ⟨hgirr⟩
  let L := AdjoinRoot g
  let _ : Module.Finite K L :=
    (AdjoinRoot.powerBasis hgirr.ne_zero).finite
  let _ : NumberField L :=
    NumberField.of_module_finite K L
  let _ : Algebra.IsSeparable K L := inferInstance
  let _ : FiniteDimensional K L := inferInstance
  let vw : v.placesOver L := Classical.choice inferInstance
  let w := vw.val
  let _ : w.asIdeal.LiesOver v.asIdeal := vw.property
  have hfinrankL : Module.finrank K L = g.natDegree := by
    dsimp [L]
    exact finrank_quotient_span_eq_natDegree
  have hfinrankM :
    Module.finrank (v.adicCompletion K) M = f.natDegree := by
    calc
      Module.finrank (v.adicCompletion K) M =
        Module.finrank (v.adicCompletion K) (AdjoinRoot f) :=
        eMf.toLinearEquiv.finrank_eq
      _ = f.natDegree := finrank_quotient_span_eq_natDegree
  have hfinrank :
    Module.finrank K L =
      Module.finrank (v.adicCompletion K) M := by
    rw [hfinrankL, hfinrankM, hdeg]
  let eL : L ≃ₐ[K] AdjoinRoot g := by
    dsimp [L]
    exact AlgEquiv.refl
  have hM :
    Nonempty
      (M ≃ₐ[v.adicCompletion K]
        AdjoinRoot
          (g.map (algebraMap K (v.adicCompletion K)))) :=
    ⟨eMf.trans efg⟩
  have hcompletion :
    Nonempty (M ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
    completion_algEquiv_of_adjoinRoot_globalEquiv
      v w g hmapirr eL hM
  exact
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, w, inferInstance, hfinrank, hcompletion⟩

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
