import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductSurjective
open scoped NumberField Valued
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open scoped NumberField.LiesOver
open TensorProduct
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[adicAbv_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
omit [NumberField K] in
private lemma adicAbv_nontrivial (w : v.placesOver L) :
  (NumberField.HeightOneSpectrum.adicAbv L w.val).IsNontrivial := by
  obtain ⟨a, ha_mem, ha_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot w.val.ne_bot
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 L) L).not.2 ha_ne
  refine ⟨algebraMap (𝓞 L) L a, ha0, ?_⟩
  have hlt :
    NumberField.HeightOneSpectrum.adicAbv L w.val
      (algebraMap (𝓞 L) L a) < 1 :=
    (w.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w.val) a).mpr
      ha_mem
  exact ne_of_lt hlt

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[adicAbv_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
omit [NumberField K] in
private lemma adicAbv_pairwise :
  Pairwise fun a b : v.placesOver L =>
    ¬(NumberField.HeightOneSpectrum.adicAbv L a.val).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv L b.val) := by
  intro a b hne hEquiv
  apply hne
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  have hlt :
    ∀ x : L,
      NumberField.HeightOneSpectrum.adicAbv L a.val x < 1 ↔
        NumberField.HeightOneSpectrum.adicAbv L b.val x < 1 :=
    fun x => hEquiv.lt_one_iff
  have ha :
    NumberField.HeightOneSpectrum.adicAbv L a.val
      (algebraMap (𝓞 L) L r) < 1 ↔
    r ∈ a.val.asIdeal :=
    a.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal a.val) r
  have hb :
    NumberField.HeightOneSpectrum.adicAbv L b.val
      (algebraMap (𝓞 L) L r) < 1 ↔
    r ∈ b.val.asIdeal :=
    b.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal b.val) r
  rw [← ha, ← hb]
  exact hlt _

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[coord_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
omit [NumberField K] in
private lemma coord_isometry (w : v.placesOver L) :
  Isometry (coord v w) := by
  refine AddMonoidHomClass.isometry_of_norm _ (fun x => ?_)
  have h1 :
    ‖coord v w x‖ =
      NumberField.HeightOneSpectrum.adicAbv L w.val
        ((WithAbs.equiv _) x) := by
    simp only [coord, RingHom.comp_apply]
    exact NumberField.FinitePlace.norm_embedding w.val _
  have h2 :
    ‖x‖ =
      NumberField.HeightOneSpectrum.adicAbv L w.val
        ((WithAbs.equiv _) x) :=
    WithAbs.norm_eq_apply_ofAbs _ x
  rw [h1, h2]

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[coord_comp_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
omit [NumberField K] in
private lemma coord_comp_algebraMap (w : v.placesOver L) :
  (⇑(coord v w) ∘
    algebraMap L
      (WithAbs
        (NumberField.HeightOneSpectrum.adicAbv L w.val))) =
    algebraMap L (w.val.adicCompletion L) := by
  funext y
  simp only [coord, RingHom.comp_apply, Function.comp_apply]
  rw [NumberField.FinitePlace.embedding_apply]
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[coord_denseRange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
omit [NumberField K] in
private lemma coord_denseRange (w : v.placesOver L) :
  DenseRange (coord v w) := by
  apply DenseRange.of_comp
    (g := algebraMap L
      (WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val)))
  rw [coord_comp_algebraMap]
  exact w.val.denseRange_algebraMap L

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
/--
[weakApprox](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
private lemma weakApprox :
  DenseRange
    (algebraMap L
      ((w : v.placesOver L) →
        WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))) :=
  AbsoluteValue.denseRange_algebraMap_pi (fun w => adicAbv_nontrivial v w)
    (adicAbv_pairwise v)

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[denseRange_algebraMap_placesOver](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
lemma denseRange_algebraMap_placesOver
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  DenseRange (fun y : L => fun w : v.placesOver L =>
    algebraMap L (w.val.adicCompletion L) y) := by
-- proof
  have hWA := weakApprox (K := K) (L := L) v
  have hPi :=
    DenseRange.piMap (fun w : v.placesOver L => coord_denseRange v w)
  have hcont :=
    Continuous.piMap
      (fun w : v.placesOver L => (coord_isometry v w).continuous)
  have hcomp := hPi.comp hWA hcont
  have heq : (Pi.map (fun w : v.placesOver L => coord v w)) ∘
    algebraMap L
      ((w : v.placesOver L) →
        WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val)) =
    (fun y : L => fun w : v.placesOver L =>
      algebraMap L (w.val.adicCompletion L) y) := by
    funext y w
    simp only [Function.comp_apply, Pi.map_apply]
    have h2 := coord_comp_algebraMap v w
    have h3 : (algebraMap L
      ((w : v.placesOver L) →
        WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))
      y) w =
      algebraMap L
        (WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))
        y := rfl
    rw [h3]
    exact congrFun h2 y
  rwa [heq] at hcomp

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[denseRange_completionTensorProductMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
lemma denseRange_completionTensorProductMap
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  DenseRange (completionTensorProductMap (K := by
-- proof
  apply DenseRange.of_comp
    (g := fun y : L => (1 : v.adicCompletion K) ⊗ₜ[K] y)
  have heq : (completionTensorProductMap (K := K) (L := L) v) ∘
    (fun y : L => (1 : v.adicCompletion K) ⊗ₜ[K] y) =
    (fun y : L => fun w : v.placesOver L =>
      algebraMap L (w.val.adicCompletion L) y) := by
    funext y w
    simp only [Function.comp_apply]
    rw [completionTensorProductMap_tmul, map_one, one_mul]
    change algebraMap L (w.val.adicCompletion L) y = _
    rfl
  rw [heq]
  exact denseRange_algebraMap_placesOver v

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
[completionTensorProductMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean)
-/
@[path]
lemma completionTensorProductMap_surjective
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Function.Surjective
    (completionTensorProductMap (K := by
-- proof
  let f :=
    (completionTensorProductMap (K := K) (L := L) v).toLinearMap
  let s : Submodule (v.adicCompletion K)
    ((w : v.placesOver L) → w.val.adicCompletion L) :=
    (⊤ : Submodule (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).map f
  have hsRange :
    (s : Set ((w : v.placesOver L) → w.val.adicCompletion L)) = Set.range f := by
    ext y
    simp [s]
  let _ : FiniteDimensional (v.adicCompletion K) s := inferInstance
  have hsClosed : IsClosed (s : Set ((w : v.placesOver L) →
    w.val.adicCompletion L)) := by
    exact Submodule.closed_of_finiteDimensional
      (𝕜 := v.adicCompletion K)
      (E := ((w : v.placesOver L) → w.val.adicCompletion L)) s
  have hDense : DenseRange f :=
    denseRange_completionTensorProductMap (K := K) (L := L) v
  have hRange : Set.range f = Set.univ := by
    rwa [← hsRange, ← hsClosed.closure_eq, hsRange]
  exact Set.range_eq_univ.mp hRange

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
