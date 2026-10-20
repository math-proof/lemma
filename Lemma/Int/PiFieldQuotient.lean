import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PiFieldQuotient
open PiFieldQuotient


/--
[restrict_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma restrict_apply_eq
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι}
  {s : S}
-- given
  (x : ∀ i, F i) :
-- imply
  restrict (K := by
-- proof
  apply PiFieldQuotient.restrict_apply S x s

/--
[restrict_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma restrict_surjective_eq
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι} :
-- imply
  Function.Surjective (restrict (F := by
-- proof
  apply PiFieldQuotient.restrict_surjective S

/--
[mem_ker_restrict_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma mem_ker_restrict_iff_eq
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι}
-- given
  (x : ∀ i, F i) :
-- imply
  restrict (K := by
-- proof
  apply PiFieldQuotient.mem_ker_restrict_iff S x

/--
[mem_selected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma mem_selected_eq
  [Finite ι]
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {φ : (∀ i, F i) →ₐ[K] B}
  {i : ι} :
-- imply
  i ∈ selected φ ↔
    Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥ := by
-- proof
  apply PiFieldQuotient.mem_selected φ i

/--
[mem_ker_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma mem_ker_iff_eq
  [Finite ι]
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {φ : (∀ i, F i) →ₐ[K] B}
-- given
  (x : ∀ i, F i) :
-- imply
  φ x = 0 ↔ ∀ i, x i ∈ Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) := by
-- proof
  apply PiFieldQuotient.mem_ker_iff φ x

/--
[exists_algEquiv_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma exists_algEquiv_restrict_eq
  [Finite ι]
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {φ : (∀ i, F i) →ₐ[K] B}
-- given
  (hφ : Function.Surjective φ) :
-- imply
  ∃ S : Finset ι, ∃ e : B ≃ₐ[K] (∀ i : S, F i),
    e.toAlgHom.comp φ = AlgHom.pi (fun i : S => Pi.evalAlgHom K F i) := by
-- proof
  apply PiFieldQuotient.exists_algEquiv_restrict φ hφ

/--
[exists_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma exists_algEquiv_eq
  [Finite ι]
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {φ : (∀ i, F i) →ₐ[K] B}
-- given
  (hφ : Function.Surjective φ) :
-- imply
  ∃ S : Finset ι, Nonempty (B ≃ₐ[K] (∀ i : S, F i)) := by
-- proof
  apply PiFieldQuotient.exists_algEquiv φ hφ


-- created on 2026-10-20
