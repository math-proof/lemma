import Mathlib
import sympy.Basic
import Def.RingTheory.PiFieldQuotient
open PiFieldQuotient


namespace PiFieldQuotient

/--
[restrict_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma restrict_apply
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι}
  {s : S}
-- given
  (x : ∀ i, F i) :
-- imply
  restrict (K :=
-- proof
  rfl

end PiFieldQuotient

namespace PiFieldQuotient

/--
[restrict_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma restrict_surjective
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι} :
-- imply
  Function.Surjective (restrict (F := by
-- proof
  classical
  intro y
  refine ⟨fun i => if h : i ∈ S then y ⟨i, h⟩ else 0, ?_⟩
  ext s
  simp only [restrict, AlgHom.pi_apply, Pi.evalAlgHom_apply, dite_eq_left s.property]

end PiFieldQuotient

namespace PiFieldQuotient

/--
[mem_ker_restrict_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma mem_ker_restrict_iff
  {K : Type u} [Field K]
  {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  {B : Type w} [CommRing B] [Algebra K B]
  {S : Finset ι}
-- given
  (x : ∀ i, F i) :
-- imply
  restrict (K := by
-- proof
  constructor
  · intro h i hi
    have h2 : restrict (K := K) (F := F) S x ⟨i, hi⟩ = 0 := by
      rw [h]
      rfl
    rwa [restrict_apply] at h2
  · intro h
    ext s
    simpa using h s.val s.property

end PiFieldQuotient

namespace PiFieldQuotient

/--
[mem_selected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma mem_selected
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
  unfold selected
  simp

end PiFieldQuotient

namespace PiFieldQuotient

/--
[mem_ker_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma mem_ker_iff
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
  have hJ : (fun i => Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ)) =
    ⇑Ideal.piOrderIso (RingHom.ker φ) :=
    funext fun i => rfl
  have hker_pi :
    Ideal.pi (fun i => Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ)) =
      RingHom.ker φ := by
    rw [hJ]
    exact Ideal.piOrderIso.symm_apply_apply (RingHom.ker φ)
  conv_lhs => rw [← RingHom.mem_ker, ← hker_pi]
  exact Ideal.mem_pi _ x

end PiFieldQuotient

namespace PiFieldQuotient

/--
[exists_algEquiv_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma exists_algEquiv_restrict
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
  classical
  have hker : RingHom.ker φ =
    RingHom.ker (restrict (K := K) (F := F) (selected φ)) := by
    ext x
    simp only [RingHom.mem_ker]
    rw [mem_ker_iff φ x, mem_ker_restrict_iff]
    constructor
    · intro h i hi
      have hJi : Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥ :=
        (mem_selected φ i).mp hi
      have hi2 := h i
      rw [hJi] at hi2
      exact (Submodule.mem_bot _).mp hi2
    · intro h i
      by_cases hi : i ∈ selected φ
      · have hJi : Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥ :=
        (mem_selected φ i).mp hi
        rw [hJi]
        exact (Submodule.mem_bot _).mpr (h i hi)
      · have hne : Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) ≠ ⊥ :=
        fun hbot => hi ((mem_selected φ i).mpr hbot)
        rcases Ideal.eq_bot_or_top
          (Ideal.map (Pi.evalRingHom F i) (RingHom.ker φ)) with hbot | htop
        · exact (hne hbot).elim
        · rw [htop]
          exact Submodule.mem_top
  refine ⟨selected φ,
    (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.trans
      ((Ideal.quotientEquivAlgOfEq K hker).trans
        (Ideal.quotientKerAlgEquivOfSurjective
          (restrict_surjective (selected φ)))),
    ?_⟩
  have hcomm : ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm.trans
    ((Ideal.quotientEquivAlgOfEq K hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (restrict_surjective (selected φ))))).toAlgHom.comp φ =
    restrict (K := K) (F := F) (selected φ) := by
    ext x s
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply,
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply, AlgEquiv.trans_apply,
      Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  exact hcomm

end PiFieldQuotient

namespace PiFieldQuotient

/--
[exists_algEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean)
-/
@[path]
lemma exists_algEquiv
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
  obtain ⟨S, e, -⟩ := exists_algEquiv_restrict φ hφ
  exact ⟨S, ⟨e⟩⟩

end PiFieldQuotient


-- created on 2026-10-20
-- updated on 2026-10-23
