/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean -/

-- MathlibExt/RingTheory/PiFieldQuotient.lean

import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Surjective algebra quotients of finite products of fields

Let `K` be a field, `ι` a finite type, `F : ι → Type*` a family of fields with
`K`-algebra structures, and `B` a commutative `K`-algebra. We show that any
surjective `K`-algebra homomorphism `(∀ i, F i) →ₐ[K] B` exhibits `B` as the
coordinate restriction to a subfamily: there is `S : Finset ι` and a
`K`-algebra equivalence `B ≃ₐ[K] (∀ i : S, F i)` commuting with restriction.

The proof analyzes the kernel: ideals of a product of fields are products of
ideals (`Ideal.piOrderIso`), each component ideal is `⊥` or `⊤`
(`Ideal.eq_bot_or_top`), and the first isomorphism theorem
(`Ideal.quotientKerAlgEquivOfSurjective`) identifies both `B` and the
restricted product with the quotient by that kernel. No finite-dimensionality,
separability, or nontriviality hypotheses are needed; the empty subfamily and
trivial targets work uniformly.
-/

universe u v w

namespace PiFieldQuotient

variable {K : Type u} [Field K]
variable {ι : Type*}
variable {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
variable {B : Type w} [CommRing B] [Algebra K B]

/-- Coordinate restriction to a selected subfamily, as a `K`-algebra map. -/
def restrict (S : Finset ι) : (∀ i, F i) →ₐ[K] (∀ i : S, F i) :=
  AlgHom.pi (A := fun i : S => F (i : ι))
    (fun i : S => Pi.evalAlgHom K F (i : ι))

/-- Applying restriction is evaluation at the underlying index. -/
@[simp]
theorem restrict_apply (S : Finset ι) (x : ∀ i, F i) (s : S) :
    restrict (K := K) (F := F) S x s = x s :=
  rfl

/-- Coordinate restriction is surjective (extend by zero off `S`). -/
theorem restrict_surjective (S : Finset ι) :
    Function.Surjective (restrict (F := F) (K := K) S) := by
  classical
  intro y
  refine ⟨fun i => if h : i ∈ S then y ⟨i, h⟩ else 0, ?_⟩
  ext s
  simp only [restrict, AlgHom.pi_apply, Pi.evalAlgHom_apply, dite_eq_left s.property]

/-- Vanishing on `restrict S` is vanishing on all selected coordinates. -/
theorem mem_ker_restrict_iff (S : Finset ι) (x : ∀ i, F i) :
    restrict (K := K) (F := F) S x = 0 ↔ ∀ i ∈ S, x i = 0 := by
  constructor
  · intro h i hi
    have h2 : restrict (K := K) (F := F) S x ⟨i, hi⟩ = 0 := by
      rw [h]
      rfl
    rwa [restrict_apply] at h2
  · intro h
    ext s
    simpa using h s.val s.property

variable [Finite ι]

/-- The indices where the kernel of `φ` vanishes componentwise. -/
noncomputable def selected (φ : (∀ i, F i) →ₐ[K] B) : Finset ι := by
  classical
  haveI := Fintype.ofFinite ι
  exact Finset.univ.filter
    fun i => Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥

/-- Membership in `selected φ` is vanishing of the corresponding component ideal. -/
theorem mem_selected (φ : (∀ i, F i) →ₐ[K] B) (i : ι) :
    i ∈ selected φ ↔
      Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥ := by
  unfold selected
  simp

/-- Membership in the kernel of `φ` is componentwise membership in the pushed-forward
ideals, via `Ideal.piOrderIso`. -/
theorem mem_ker_iff (φ : (∀ i, F i) →ₐ[K] B) (x : ∀ i, F i) :
    φ x = 0 ↔ ∀ i, x i ∈ Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) := by
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

/-- A surjective algebra map out of a finite product of fields exhibits its target as
coordinate restriction to a subfamily, up to `K`-algebra equivalence. -/
theorem exists_algEquiv_restrict
    (φ : (∀ i, F i) →ₐ[K] B) (hφ : Function.Surjective φ) :
    ∃ S : Finset ι, ∃ e : B ≃ₐ[K] (∀ i : S, F i),
      e.toAlgHom.comp φ = AlgHom.pi (fun i : S => Pi.evalAlgHom K F i) := by
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

/-- Weaker corollary: only the existence of the subfamily and the equivalence. -/
theorem exists_algEquiv
    (φ : (∀ i, F i) →ₐ[K] B) (hφ : Function.Surjective φ) :
    ∃ S : Finset ι, Nonempty (B ≃ₐ[K] (∀ i : S, F i)) := by
  obtain ⟨S, e, -⟩ := exists_algEquiv_restrict φ hφ
  exact ⟨S, ⟨e⟩⟩

end PiFieldQuotient
