import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
open FunctionFieldAdeleRing RiemannRochSpace WeilDifferential
open scoped RestrictedProduct
open CurveWithOrd CurveDivisor


namespace FunctionFieldAdeleRing

/--
[mem_valuationSubring_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma mem_valuationSubring_cofinitely
  [Field F]
  {O : P → ValuationSubring F}
  {α : FunctionFieldAdeleRing F P O} :
-- imply
  ∀ᶠ p in Filter.cofinite, α p ∈ O p :=
-- proof
  α.2

end FunctionFieldAdeleRing

/--
[RiemannRochData.algebraMap_of_all_ord_zero_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma RiemannRochData.algebraMap_of_all_ord_zero_ax
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {f : Fˣ} :
-- imply
  (∀ P : C, CurveWithOrd.ord P f = 0) → ∃ c : kˣ, (f : F) = algebraMap k F (c : k) := by
-- proof
  intro hf
  obtain ⟨a, ha⟩ := CurveWithConstants.ker_div_eq_constants f hf
  exact ⟨a, by rw [← ha]; simp [Units.coe_map]⟩

/--
[dvr_uniformizer_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma dvr_uniformizer_exists
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [CurveWithOrd C F]
  {P : C} :
-- imply
  ∃ (π : Fˣ), CurveWithOrd.ord P π = 1 :=
-- proof
  CurveWithOrd.uniformizer_exists P

/--
[dvr_residue_eval_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma dvr_residue_eval_exists
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [CurveWithConstants C k F]
  {P : C} :
-- imply
  ∃ (evalP : F →ₗ[k] k), ∀ (f : Fˣ), CurveWithOrd.ord P f ≥ 0 → evalP (f : F) = 0 → CurveWithOrd.ord P f ≥ 1 :=
-- proof
  CurveWithConstants.residue_eval P

/--
[CurveWithOrd.ord_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma CurveWithOrd.ord_zpow
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [CurveWithOrd C F]
  {P : C}
  {f : Fˣ}
  {n : ℤ} :
-- imply
  CurveWithOrd.ord P (f ^ n) = n * CurveWithOrd.ord P f := by
-- proof
  have h := MonoidHom.map_zpow (CurveWithOrd.ordMonoidHom P) f n
  dsimp [CurveWithOrd.ordMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  have h2 : (Multiplicative.ofAdd (CurveWithOrd.ord P f)) ^ n =
    Multiplicative.ofAdd (n * CurveWithOrd.ord P f) :=
    (Equiv.symm_apply_eq Multiplicative.ofAdd).mp rfl
  rw [h2] at h
  exact Multiplicative.ofAdd.injective h

/--
[dvr_residue_functional_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma dvr_residue_functional_exists
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
  {P : C} :
-- imply
  ∃ (φ : F →ₗ[k] k), ∀ (f : Fˣ), (CurveWithOrd.principalDivisor f + (D + Finsupp.single P 1)).IsEffective → φ (f : F) = 0 → (CurveWithOrd.principalDivisor f + D).IsEffective := by
-- proof
  obtain ⟨π, hπ⟩ := dvr_uniformizer_exists (F := F) P
  obtain ⟨evalP, hevalP⟩ := dvr_residue_eval_exists (F := F) (k := k) P
  set n : ℤ := D P + 1 with hn_def
  let mulπn : F →ₗ[k] F :=
    { toFun := fun f => (↑(π ^ n) : F) * f
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        exact mul_smul_comm r (↑(π ^ n)) x }
  refine ⟨evalP.comp mulπn, fun f heff hφf => ?_⟩
  intro Q
  have heffQ := heff Q
  simp only [Finsupp.coe_add, Pi.add_apply,
    CurveWithOrd.principalDivisor_apply] at heffQ ⊢
  by_cases hQP : Q = P
  ·
    subst hQP
    simp only [Finsupp.single_eq_same] at heffQ
    have hord_prod : CurveWithOrd.ord Q (π ^ n * f) = n + CurveWithOrd.ord Q f := by
      rw [CurveWithOrd.ord_mul, CurveWithOrd.ord_zpow, hπ, mul_one]
    have hord_nonneg : CurveWithOrd.ord Q (π ^ n * f) ≥ 0 := by
      rw [hord_prod]; linarith
    have hcoerce : (↑(π ^ n * f) : F) = (↑(π ^ n) : F) * (↑f : F) := by
      simp [Units.val_mul]
    have heval_zero : evalP (↑(π ^ n * f) : F) = 0 := by
      rwa [hcoerce]
    have hord_pos : CurveWithOrd.ord Q (π ^ n * f) ≥ 1 :=
      hevalP (π ^ n * f) hord_nonneg heval_zero
    linarith [hord_prod]
  ·
    have hsingle : (Finsupp.single P 1 : CurveDivisor C) Q = 0 :=
      Finsupp.single_eq_of_ne hQP
    linarith [hsingle]

/--
[RiemannRochData.dvr_eval_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma RiemannRochData.dvr_eval_ax
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
  {P : C} :
-- imply
  ∃ (φ : F →ₗ[k] k), ∀ (f : F), (f = 0 ∨ ∃ (hf : f ≠ 0), (CurveWithOrd.principalDivisor (Units.mk0 f hf) + (D + Finsupp.single P 1)).IsEffective) → φ f = 0 → (f = 0 ∨ ∃ (hf : f ≠ 0), (CurveWithOrd.principalDivisor (Units.mk0 f hf) + D).IsEffective) := by
-- proof
  obtain ⟨φ, hφ⟩ := dvr_residue_functional_exists (F := F) (k := k) D P
  exact ⟨φ, fun f hfLD hφf => by
    obtain rfl | ⟨hf, heff⟩ := hfLD
    · left; rfl
    · right
      exact ⟨hf, hφ (Units.mk0 f hf) heff hφf⟩⟩

/--
[RiemannRochData.degree_principalDivisor_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma RiemannRochData.degree_principalDivisor_eq_zero
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {f : Fˣ} :
-- imply
  CurveDivisor.degree C (CurveWithOrd.principalDivisor f) = 0 :=
-- proof
  CurveWithOrd.degree_principalDivisor_eq_zero (k := k) f

/--
[RiemannRochData.algebraMap_of_all_ord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma RiemannRochData.algebraMap_of_all_ord_zero
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {f : Fˣ}
-- given
  (hf : ∀ P : C, CurveWithOrd.ord P f = 0) :
-- imply
  ∃ c : kˣ, (f : F) = algebraMap k F (c : k) :=
-- proof
  RiemannRochData.algebraMap_of_all_ord_zero_ax f hf

/--
[RiemannRochData.dvr_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma RiemannRochData.dvr_eval
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
  {P : C} :
-- imply
  ∃ (φ : F →ₗ[k] k), ∀ (f : F), (f = 0 ∨ ∃ (hf : f ≠ 0), (CurveWithOrd.principalDivisor (Units.mk0 f hf) + (D + Finsupp.single P 1)).IsEffective) → φ f = 0 → (f = 0 ∨ ∃ (hf : f ≠ 0), (CurveWithOrd.principalDivisor (Units.mk0 f hf) + D).IsEffective) :=
-- proof
  RiemannRochData.dvr_eval_ax D P
namespace RiemannRochSpace
variable {C : Type*} {F : Type*} {k : Type*}
  [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
open CurveWithOrd CurveDivisor

namespace RiemannRochSpace

/--
[mem_riemannRochSpace_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma mem_riemannRochSpace_of_ne_zero
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
  {f : F}
-- given
  (hf : f ≠ 0) :
-- imply
  f ∈ riemannRochSpace (k := k) D ↔ (principalDivisor (Units.mk0 f hf) + D).IsEffective := by
-- proof
  constructor
  · intro hmem
    exact (hmem.resolve_left hf).choose_spec
  · intro heff
    exact Or.inr ⟨hf, heff⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_equiv_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_equiv_of_linearlyEquivalent
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
-- given
  (h : PicardGroup.LinearlyEquivalent (CurveDivisor C) (principalDivisors (F := F)) A B) :
-- imply
  Nonempty ((riemannRochSpace (F := F) (k := k) A) ≃ₗ[k] (riemannRochSpace (F := F) (k := k) B)) := by
-- proof
  obtain ⟨f, hf⟩ : ∃ f : Fˣ, principalDivisor f = A - B := h
  exact ⟨riemannRochSpace_linearEquiv_of_linearlyEquivalent A B f hf⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_mono
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
-- given
  (hAB : A ≤ B) :
-- imply
  riemannRochSpace (F := F) (k := k) A ≤ riemannRochSpace (F := F) (k := k) B := by
-- proof
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
  · exact Or.inl rfl
  · right; exact ⟨hf_ne, fun P => by
    have h1 := hf_eff P
    have h2 := hAB P
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at *
    linarith⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[le_positivePart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma le_positivePart
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C} :
-- imply
  D ≤ D.positivePart := by
-- proof
  intro P
  simp [CurveDivisor.positivePart_apply]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[effective_degree_zero_eq_zero_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma effective_degree_zero_eq_zero_aux
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (heff : D.IsEffective)
  (hdeg : degree C D = 0) :
-- imply
  D = 0 := by
-- proof
  ext P
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hP
  have hP_pos : 0 < D P := lt_of_le_of_ne (heff P) (Ne.symm hP)
  rw [degree_eq_sum] at hdeg
  have hP_mem : P ∈ D.support := Finsupp.mem_support_iff.mpr hP
  have hpos := Finsupp.sum_pos' (g := fun _ n => n) (fun p _ => heff p) ⟨P, hP_mem, hP_pos⟩
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[mem_riemannRochSpace_zero_iff_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma mem_riemannRochSpace_zero_iff_algebraMap
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {f : F} :
-- imply
  f ∈ riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C) ↔ ∃ c : k, f = algebraMap k F c := by
-- proof
  constructor
  · intro hf
    rw [mem_riemannRochSpace_iff] at hf
    obtain rfl | ⟨hf_ne, heff⟩ := hf
    · exact ⟨0, (algebraMap k F).map_zero.symm⟩
    ·
      have hord_nonneg : ∀ P : C, 0 ≤ ord P (Units.mk0 f hf_ne) := by
        intro P
        have := heff P
        simp only [add_zero, principalDivisor_apply] at this
        exact this
      have heff' : (principalDivisor (C := C) (Units.mk0 f hf_ne)).IsEffective := by
        intro Q
        simp only [principalDivisor_apply]
        exact hord_nonneg Q
      have hdeg : degree C (principalDivisor (C := C) (Units.mk0 f hf_ne)) = 0 :=
        RiemannRochData.degree_principalDivisor_eq_zero (Units.mk0 f hf_ne)
      have hzero := effective_degree_zero_eq_zero_aux
        (principalDivisor (C := C) (Units.mk0 f hf_ne)) heff' hdeg
      have hord_zero : ∀ P : C, ord P (Units.mk0 f hf_ne) = 0 := by
        intro P
        have : (principalDivisor (C := C) (Units.mk0 f hf_ne)) P = 0 := by
          rw [hzero]; simp
        rwa [principalDivisor_apply] at this
      obtain ⟨c, hc⟩ := RiemannRochData.algebraMap_of_all_ord_zero (Units.mk0 f hf_ne) hord_zero
      exact ⟨c, hc⟩
  · intro ⟨c, hc⟩
    subst hc
    by_cases hc0 : c = 0
    · subst hc0; simp only [map_zero]; exact (riemannRochSpace (k := k) 0).zero_mem
    · rw [mem_riemannRochSpace_iff]
      right
      have hne : algebraMap k F c ≠ 0 := by
        intro h
        exact hc0 ((algebraMap k F).injective (h.trans (map_zero _).symm))
      refine ⟨hne, fun P => ?_⟩
      simp only [add_zero, principalDivisor_apply]
      have key : Units.mk0 (algebraMap k F c) hne =
        Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc0) := by
        apply Units.ext; simp
      rw [key, RiemannRochData.ord_algebraMap]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_zero_eq_span_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_zero_eq_span_one
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k] :
-- imply
  riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C) = Submodule.span k {(1 : F)} := by
-- proof
  apply le_antisymm
  · intro f hf
    rw [mem_riemannRochSpace_zero_iff_algebraMap] at hf
    obtain ⟨c, rfl⟩ := hf
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by simp [Algebra.smul_def]⟩
  · rw [Submodule.span_le]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    show (1 : F) ∈ riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C)
    rw [mem_riemannRochSpace_zero_iff_algebraMap]
    exact ⟨1, (algebraMap k F).map_one.symm⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_zero_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_zero_finiteDimensional
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k] :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C)) := by
-- proof
  rw [riemannRochSpace_zero_eq_span_one]
  infer_instance

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_zero_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_zero_finrank
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k] :
-- imply
  Module.finrank k (riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C)) = 1 := by
-- proof
  haveI := riemannRochSpace_zero_finiteDimensional (C := C) (F := F) (k := k)
  rw [riemannRochSpace_zero_eq_span_one]
  exact finrank_span_singleton (one_ne_zero)

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_dvr_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_dvr_eval
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
  {P : C} :
-- imply
  ∃ (φ : ↑(riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) →ₗ[k] k), ∀ f : ↑(riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)), φ f = 0 → (f : F) ∈ riemannRochSpace (F := F) (k := k) D := by
-- proof
  obtain ⟨φ₀, hφ₀⟩ := RiemannRochData.dvr_eval (F := F) (k := k) D P
  refine ⟨φ₀.comp (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)).subtype,
    fun ⟨f, hf⟩ hker => ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hker
  exact hφ₀ f hf hker

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_finrank_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_finrank_step
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
  {P : C}
  [FiniteDimensional k (riemannRochSpace (F := F) (k := k) D)] :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ∧ (Module.finrank k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) : ℤ) ≤ (Module.finrank k (riemannRochSpace (F := F) (k := k) D) : ℤ) + 1 := by
-- proof
  obtain ⟨φ, hφ⟩ := riemannRochSpace_dvr_eval (F := F) (k := k) D P
  have hker_in_LD : ∀ x : φ.ker, (x.1 : F) ∈ riemannRochSpace (F := F) (k := k) D := by
    intro ⟨⟨f, hf⟩, hmem⟩
    exact hφ ⟨f, hf⟩ (LinearMap.mem_ker.mp hmem)
  let ι : φ.ker →ₗ[k] (riemannRochSpace (F := F) (k := k) D) :=
    { toFun := fun x => ⟨(x.1 : F), hker_in_LD x⟩
      map_add' := by intros x y; ext; simp [Submodule.coe_add]
      map_smul' := by intros c x; ext; simp [SetLike.val_smul] }
  have hι_inj : Function.Injective ι := by
    intro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ h
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  haveI hfd_ker : FiniteDimensional k φ.ker :=
    FiniteDimensional.of_injective ι hι_inj
  haveI : FiniteDimensional k
    ((riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ⧸ φ.ker) := by
    have : FiniteDimensional k (LinearMap.range φ) :=
      Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
    exact Module.Finite.equiv φ.quotKerEquivRange.symm
  haveI hfd_LDP : FiniteDimensional k
    (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) :=
    Module.Finite.of_submodule_quotient φ.ker
  constructor
  · exact hfd_LDP
  ·
    have hRN := LinearMap.finrank_range_add_finrank_ker φ
    have hrange_le : Module.finrank k (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank k (LinearMap.range φ)
        ≤ Module.finrank k k := Submodule.finrank_le _
        _ = 1 := Module.finrank_self k
    have hker_le : Module.finrank k φ.ker ≤
      Module.finrank k (riemannRochSpace (F := F) (k := k) D) :=
      LinearMap.finrank_le_finrank_of_injective hι_inj
    have : Module.finrank k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ≤
      Module.finrank k (riemannRochSpace (F := F) (k := k) D) + 1 := by omega
    exact_mod_cast this
set_option maxHeartbeats 400000 in

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_finrank_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_finrank_le_of_le
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {A B : CurveDivisor C}
  [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)]
-- given
  (hAB : A ≤ B) :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) B) ∧ (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) ≤ (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) + (degree C B - degree C A) := by
-- proof
  classical
  have heff : ∀ Q, 0 ≤ (B - A) Q := fun Q => by
    have := hAB Q; simp only [Finsupp.sub_apply]; omega
  have hdeg_nonneg : 0 ≤ degree C (B - A) := by
    rw [degree_eq_sum]
    exact Finsupp.sum_nonneg (fun P _ => heff P)
  suffices h : ∀ (n : ℕ) (A' B' : CurveDivisor C),
    A' ≤ B' → (degree C (B' - A')).toNat = n →
    FiniteDimensional k (riemannRochSpace (F := F) (k := k) A') →
    FiniteDimensional k (riemannRochSpace (F := F) (k := k) B') ∧
    (Module.finrank k (riemannRochSpace (F := F) (k := k) B') : ℤ) ≤
    (Module.finrank k (riemannRochSpace (F := F) (k := k) A') : ℤ) +
      (degree C B' - degree C A') by
    exact h _ A B hAB rfl ‹_›
  intro n
  induction n using Nat.strongRec with
  | _ n ih => ?_
  intro A' B' hAB' hdeg_eq hfdA'
  have heff' : ∀ Q, 0 ≤ (B' - A') Q := fun Q => by
    have := hAB' Q; simp only [Finsupp.sub_apply]; omega
  have hdeg_nonneg' : 0 ≤ degree C (B' - A') := by
    rw [degree_eq_sum]; exact Finsupp.sum_nonneg (fun P _ => heff' P)
  by_cases hBA : B' - A' = 0
  ·
    have hBA_eq : B' = A' := by
      ext Q; have := Finsupp.ext_iff.mp hBA Q; simp [Finsupp.sub_apply] at this; linarith
    subst hBA_eq
    exact ⟨hfdA', by simp⟩
  ·
    have hsupp : (B' - A').support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hBA
    obtain ⟨P, hP⟩ := hsupp
    have hP_pos : 0 < (B' - A') P :=
      lt_of_le_of_ne (heff' P) (Ne.symm (Finsupp.mem_support_iff.mp hP))
    set B'' := B' - Finsupp.single P 1 with hB''_def
    have hAB'' : A' ≤ B'' := by
      intro Q
      simp only [hB''_def, Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; have := hAB' P; simp only [Finsupp.sub_apply] at hP_pos; omega
      · simp only [sub_zero]; exact hAB' Q
    have hB'eq : B' = B'' + Finsupp.single P 1 := by
      rw [hB''_def]; ext Q; simp
    have hdeg_step : degree C (B'' - A') = degree C (B' - A') - 1 := by
      have : B'' - A' = (B' - A') - Finsupp.single P 1 := by
        rw [hB''_def]; ext Q; simp [Finsupp.sub_apply, Finsupp.single_apply]; omega
      rw [this, degree_sub, degree_single]
    have heff'' : ∀ Q, 0 ≤ (B'' - A') Q := fun Q => by
      have := hAB'' Q; simp only [Finsupp.sub_apply]; omega
    have hdeg_nonneg'' : 0 ≤ degree C (B'' - A') := by
      rw [degree_eq_sum]; exact Finsupp.sum_nonneg (fun P' _ => heff'' P')
    have hdeg_lt : (degree C (B'' - A')).toNat < n := by
      rw [hdeg_step]
      have h1 : 0 < degree C (B' - A') := by
        rw [degree_eq_sum]
        exact Finsupp.sum_pos (fun i hi => by
          have := heff' i
          exact lt_of_le_of_ne this (Ne.symm (Finsupp.mem_support_iff.mp hi))) hBA
      omega
    have ⟨hfdB'', hbound''⟩ := ih _ hdeg_lt A' B'' hAB'' rfl hfdA'
    rw [hB'eq]
    have ⟨hfdB', hbound_step⟩ := @riemannRochSpace_finrank_step C F k _ _ _ _ B'' P hfdB''
    refine ⟨hfdB', ?_⟩
    have hdeg_B' : degree C (B'' + Finsupp.single P 1) = degree C B'' + 1 := by
      rw [degree_add, degree_single]
    rw [hdeg_B']
    linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_quotient_dim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_quotient_dim_bound
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
  [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)]
-- given
  (hAB : A ≤ B) :
-- imply
  (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) - (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) ≤ degree C B - degree C A := by
-- proof
  have ⟨_, hbound⟩ := riemannRochSpace_finrank_le_of_le (F := F) (k := k) hAB
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_effective_dim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_effective_dim_bound
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {D : CurveDivisor C}
-- given
  (hD : D.IsEffective) :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) D) ∧ (Module.finrank k (riemannRochSpace (F := F) (k := k) D) : ℤ) ≤ degree C D + 1 := by
-- proof
  have h0D : (0 : CurveDivisor C) ≤ D := (CurveDivisor.isEffective_iff_nonneg D).mp hD
  haveI hfd0 := riemannRochSpace_zero_finiteDimensional (C := C) (F := F) (k := k)
  have hfr0 := riemannRochSpace_zero_finrank (C := C) (F := F) (k := k)
  have ⟨hfdD, hbound⟩ := riemannRochSpace_finrank_le_of_le (F := F) (k := k) h0D
  constructor
  · exact hfdD
  ·
    rw [hfr0, CurveDivisor.degree_zero, sub_zero] at hbound
    push_cast at hbound
    linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_effective_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_effective_finiteDimensional
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (hD : D.IsEffective) :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) D) :=
-- proof
  (riemannRochSpace_effective_dim_bound (F := F) (k := k) D hD).1

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_finiteDimensional
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C} :
-- imply
  FiniteDimensional k (riemannRochSpace (F := F) (k := k) D) := by
-- proof
  have hle : riemannRochSpace (F := F) (k := k) D ≤
    riemannRochSpace (F := F) (k := k) D.positivePart :=
    riemannRochSpace_mono (le_positivePart D)
  have heff : D.positivePart.IsEffective := CurveDivisor.positivePart_isEffective D
  haveI := riemannRochSpace_effective_finiteDimensional (F := F) (k := k) D.positivePart heff
  exact Submodule.finiteDimensional_of_le hle

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_dim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_dim_bound
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C} :
-- imply
  (Module.finrank k (riemannRochSpace (F := F) (k := k) D) : ℤ) ≤ degree C D.positivePart + 1 := by
-- proof
  have hle : riemannRochSpace (F := F) (k := k) D ≤
    riemannRochSpace (F := F) (k := k) D.positivePart :=
    riemannRochSpace_mono (le_positivePart D)
  have heff : D.positivePart.IsEffective := CurveDivisor.positivePart_isEffective D
  have ⟨hfd, hbound⟩ := riemannRochSpace_effective_dim_bound (F := F) (k := k)
    D.positivePart heff
  haveI := hfd
  have h1 : Module.finrank k (riemannRochSpace (F := F) (k := k) D) ≤
    Module.finrank k (riemannRochSpace (F := F) (k := k) D.positivePart) :=
    Submodule.finrank_mono hle
  exact le_trans (Int.ofNat_le.mpr h1) hbound

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_eq_finrank
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C} :
-- imply
  divisorDim (F := F) (k := k) D = Module.finrank k (riemannRochSpace (F := F) (k := k) D) :=
-- proof
  rfl

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_zero
  [Field F]
  {O : P → ValuationSubring F} :
-- imply
  divisorDim (F := F) (k := k) (0 : CurveDivisor C) = 1 := by
-- proof
  rwa [divisorDim_eq_finrank]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_eq_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_eq_of_linearlyEquivalent
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
-- given
  (h : PicardGroup.LinearlyEquivalent (CurveDivisor C) (principalDivisors (F := F)) A B) :
-- imply
  divisorDim (F := F) (k := k) A = divisorDim (F := F) (k := k) B := by
-- proof
  rw [divisorDim_eq_finrank, divisorDim_eq_finrank]
  obtain ⟨f, hf⟩ : ∃ f : Fˣ, principalDivisor f = A - B := h
  exact (riemannRochSpace_linearEquiv_of_linearlyEquivalent A B f hf).finrank_eq

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_sub_le_degree_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_sub_le_degree_sub
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
-- given
  (hAB : A ≤ B) :
-- imply
  (divisorDim (F := F) (k := k) B : ℤ) - (divisorDim (F := F) (k := k) A : ℤ) ≤ degree C B - degree C A := by
-- proof
  rw [divisorDim_eq_finrank, divisorDim_eq_finrank]
  haveI := riemannRochSpace_finiteDimensional (F := F) (k := k) A
  exact riemannRochSpace_quotient_dim_bound (F := F) (k := k) hAB

end RiemannRochSpace

namespace RiemannRochSpace

/--
[degree_principalDivisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma degree_principalDivisor
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {f : Fˣ} :
-- imply
  degree C (principalDivisor (C := C) f) = 0 :=
-- proof
  RiemannRochData.degree_principalDivisor_eq_zero f

end RiemannRochSpace

namespace RiemannRochSpace

/--
[effective_degree_zero_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma effective_degree_zero_eq_zero
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (heff : D.IsEffective)
  (hdeg : degree C D = 0) :
-- imply
  D = 0 := by
-- proof
  ext P
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hP
  have hP_ne : D P ≠ 0 := hP
  have hP_pos : 0 < D P := lt_of_le_of_ne (heff P) (Ne.symm hP_ne)
  rw [degree_eq_sum] at hdeg
  have hP_mem : P ∈ D.support := Finsupp.mem_support_iff.mpr hP_ne
  have hpos := Finsupp.sum_pos' (g := fun _ n => n) (fun p _ => heff p) ⟨P, hP_mem, hP_pos⟩
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_eq_one_of_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_eq_one_of_principal
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (hprinc : IsPrincipal (F := F) D) :
-- imply
  divisorDim (F := F) (k := k) D = 1 := by
-- proof
  rw [isPrincipal_iff] at hprinc
  obtain ⟨f, hf⟩ := hprinc
  have hf_eq : principalDivisor f = D - 0 := by rw [sub_zero]; exact hf
  let e := riemannRochSpace_linearEquiv_of_linearlyEquivalent D 0 f hf_eq
  have hfr : Module.finrank k (riemannRochSpace (F := F) (k := k) D) =
    Module.finrank k (riemannRochSpace (F := F) (k := k) (0 : CurveDivisor C)) :=
    e.finrank_eq
  rwa [divisorDim_eq_finrank, hfr]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_eq_zero_of_not_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_eq_zero_of_not_principal
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (hdeg : degree C D = 0)
  (hnprinc : ¬ IsPrincipal (F := F) D) :
-- imply
  divisorDim (F := F) (k := k) D = 0 := by
-- proof
  by_contra h
  rw [divisorDim_eq_finrank] at h
  haveI := riemannRochSpace_finiteDimensional (F := F) (k := k) D
  have hpos : 0 < Module.finrank k (riemannRochSpace (F := F) (k := k) D) := by
    omega
  rw [Module.finrank_pos_iff] at hpos
  obtain ⟨⟨f, hf_mem⟩, ⟨g, hg_mem⟩, hne⟩ := hpos
  simp only [Ne, Subtype.mk.injEq] at hne
  have ⟨v, hv_mem, hv_ne⟩ : ∃ v : F, v ∈ riemannRochSpace (k := k) D ∧ v ≠ 0 := by
    by_cases hf0 : f = 0
    · exact ⟨g, hg_mem, fun h => hne (hf0 ▸ h ▸ rfl)⟩
    · exact ⟨f, hf_mem, hf0⟩
  have hv_eff := (mem_riemannRochSpace_of_ne_zero D v hv_ne).mp hv_mem
  have hdeg_sum : degree C (principalDivisor (Units.mk0 v hv_ne) + D) = 0 := by
    rw [degree_add, degree_principalDivisor (k := k), hdeg, zero_add]
  have hzero : principalDivisor (Units.mk0 v hv_ne) + D = 0 :=
    effective_degree_zero_eq_zero _ hv_eff hdeg_sum
  have hD_eq : D = principalDivisor ((Units.mk0 v hv_ne)⁻¹ : Fˣ) := by
    rw [principalDivisor_inv]
    exact eq_neg_of_add_eq_zero_right hzero
  exfalso
  apply hnprinc
  rw [isPrincipal_iff]
  exact ⟨(Units.mk0 v hv_ne)⁻¹, hD_eq.symm⟩

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_degree_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_degree_zero_iff
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (hdeg : degree C D = 0) :
-- imply
  divisorDim (F := F) (k := k) D = 1 ↔ IsPrincipal (F := F) D := by
-- proof
  constructor
  ·
    intro h
    by_contra hnp
    have := divisorDim_eq_zero_of_not_principal (F := F) (k := k) D hdeg hnp
    omega
  ·
    exact divisorDim_eq_one_of_principal (F := F) (k := k) D

end RiemannRochSpace

namespace RiemannRochSpace

/--
[riemannRochSpace_nontrivial_iff_linearlyEquivalent_effective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma riemannRochSpace_nontrivial_iff_linearlyEquivalent_effective
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C} :
-- imply
  (riemannRochSpace (F := F) (k := k) D ≠ ⊥) ↔ ∃ D' : CurveDivisor C, D'.IsEffective ∧ PicardGroup.LinearlyEquivalent (CurveDivisor C) (principalDivisors (F := F)) D D' := by
-- proof
  constructor
  ·
    intro h
    rw [Submodule.ne_bot_iff] at h
    obtain ⟨f, hf_mem, hf_ne⟩ := h
    have hf_eff := (mem_riemannRochSpace_of_ne_zero D f hf_ne).mp hf_mem
    refine ⟨principalDivisor (Units.mk0 f hf_ne) + D, hf_eff, ?_⟩
    show D - (principalDivisor (Units.mk0 f hf_ne) + D) ∈ principalDivisors
    have hsub : D - (principalDivisor (Units.mk0 f hf_ne) + D) =
      principalDivisor ((Units.mk0 f hf_ne)⁻¹ : Fˣ) := by
      rw [principalDivisor_inv]; abel
    rw [hsub]
    exact ⟨(Units.mk0 f hf_ne)⁻¹, rfl⟩
  ·
    rintro ⟨D', hD'_eff, hD_equiv⟩
    rw [Submodule.ne_bot_iff]
    obtain ⟨g, hg⟩ : ∃ g : Fˣ, principalDivisor g = D - D' := hD_equiv
    refine ⟨(↑g⁻¹ : F), ?_, g⁻¹.ne_zero⟩
    rw [mem_riemannRochSpace_of_ne_zero D (↑g⁻¹ : F) g⁻¹.ne_zero]
    have hkey : Units.mk0 (↑g⁻¹ : F) g⁻¹.ne_zero = g⁻¹ := by
      apply Units.ext; simp
    rw [hkey, principalDivisor_inv, hg]
    show (-(D - D') + D).IsEffective
    have : -(D - D') + D = D' := by abel
    rwa [this]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[rDivisor_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma rDivisor_mono
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
  [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)]
-- given
  (hAB : A ≤ B) :
-- imply
  rDivisor (F := F) (k := k) A ≤ rDivisor (F := F) (k := k) B := by
-- proof
  simp only [rDivisor]
  have h := riemannRochSpace_quotient_dim_bound (F := F) (k := k) hAB
  simp only [divisorDim_eq_finrank]
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[rDivisor_eq_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma rDivisor_eq_of_linearlyEquivalent
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
-- given
  (hlin : PicardGroup.LinearlyEquivalent (CurveDivisor C) (principalDivisors (F := F)) A B) :
-- imply
  rDivisor (F := F) (k := k) A = rDivisor (F := F) (k := k) B := by
-- proof
  simp only [rDivisor]
  have hℓ_eq := divisorDim_eq_of_linearlyEquivalent A B hlin
  obtain ⟨f, hf⟩ : ∃ f : Fˣ, principalDivisor f = A - B := hlin
  have hdeg_eq : degree C A = degree C B := by
    have : degree C A - degree C B = 0 := by
      rw [← CurveDivisor.degree_sub]
      rw [← hf]
      exact degree_principalDivisor (k := k) f
    linarith
  rw [hdeg_eq, hℓ_eq]
/-- (Theorem 22.3, inequality.) For every divisor $D$, $r(D) \leq g - 1$. -/

end RiemannRochSpace

/--
[dim_counting_property_of_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma dim_counting_property_of_axioms
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  {ω₁ ω₂ : Ω}
-- given
  (hdata_all : WeilDifferentialSubspaceData F k Ω)
  (hω₁ : ω₁ ≠ 0)
  (hω₂ : ω₂ ≠ 0) :
-- imply
  ∃ (U₁ U₂ : Submodule k Ω), FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧ (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧ (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧ Module.finrank k ↥U₁ + Module.finrank k ↥U₂ > Module.finrank k ↥(U₁ ⊔ U₂) := by
-- proof
  obtain ⟨δ₁, δ₂, g, n₀, hdata⟩ := hdata_all ω₁ ω₂ hω₁ hω₂
  let n := max n₀ (3 * (g : ℤ) - δ₁ - δ₂ - 2)
  have hn₀ : n ≥ n₀ := le_max_left _ _
  have hn_large : n + δ₁ + δ₂ - 3 * (g : ℤ) + 3 > 0 := by
    simp only [n]; linarith [le_max_right n₀ (3 * (g : ℤ) - δ₁ - δ₂ - 2)]
  obtain ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, hdim₁, hdim₂, hamb⟩ :=
    hdata n hn₀
  refine ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, ?_⟩
  omega
namespace WeilDifferential
section Theorem22_14
variable {F : Type*} [Field F]
variable {k : Type*} [Field k] [Algebra k F]
variable {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]

namespace WeilDifferential

/--
[omega_one_dim_of_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma omega_one_dim_of_proportional
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
-- given
  (h : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂) :
-- imply
  ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f : F, f ≠ 0 ∧ ω₂ = f • ω₁ := by
-- proof
  intro ω₁ ω₂ hω₁ hω₂
  obtain ⟨f₁, f₂, hf₁, hf₂, heq⟩ := h ω₁ ω₂ hω₁ hω₂
  refine ⟨f₂⁻¹ * f₁, mul_ne_zero (inv_ne_zero hf₂) hf₁, ?_⟩
  have := congr_arg (f₂⁻¹ • ·) heq
  simp only [smul_smul, inv_mul_cancel₀ hf₂, one_smul] at this
  exact this.symm

end WeilDifferential

namespace WeilDifferential

/--
[finrank_eq_one_of_nonzero_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma finrank_eq_one_of_nonzero_proportional
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
-- given
  (omega_nonzero : ∃ ω : Ω, ω ≠ 0)
  (proportional : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂) :
-- imply
  Module.finrank F Ω = 1 := by
-- proof
  have omega_one_dim := omega_one_dim_of_proportional proportional
  obtain ⟨ω₀, hω₀⟩ := omega_nonzero
  suffices hbij : Function.Bijective (LinearMap.toSpanSingleton F Ω ω₀) by
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]
  constructor
  ·
    intro f g hfg
    simp only [LinearMap.toSpanSingleton_apply] at hfg
    by_contra hne
    have hfg_ne : f - g ≠ 0 := sub_ne_zero.mpr hne
    have h : (f - g) • ω₀ = 0 := by rw [sub_smul, sub_eq_zero.mpr hfg]
    have := congr_arg ((f - g)⁻¹ • ·) h
    simp [smul_smul, inv_mul_cancel₀ hfg_ne] at this
    exact hω₀ this
  ·
    intro ω
    by_cases hω : ω = 0
    · exact ⟨0, by simp [hω]⟩
    · obtain ⟨f, _, hf_eq⟩ := omega_one_dim ω₀ ω hω₀ hω
      exact ⟨f, by simp [hf_eq]⟩

end WeilDifferential

namespace WeilDifferential

/--
[weil_differentials_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma weil_differentials_nonzero
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [Nontrivial Ω] :
-- imply
  ∃ ω : Ω, ω ≠ 0 :=
-- proof
  exists_ne 0

end WeilDifferential

namespace WeilDifferential

/--
[dim_counting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma dim_counting
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  {ω₁ ω₂ : Ω}
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω)
  (hω₁ : ω₁ ≠ 0)
  (hω₂ : ω₂ ≠ 0) :
-- imply
  ∃ (U₁ U₂ : Submodule k Ω), FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧ (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧ (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧ Module.finrank k ↥U₁ + Module.finrank k ↥U₂ > Module.finrank k ↥(U₁ ⊔ U₂) :=
-- proof
  dim_counting_property_of_axioms hsd ω₁ ω₂ hω₁ hω₂

end WeilDifferential

namespace WeilDifferential

/--
[weil_differentials_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma weil_differentials_proportional
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω) :
-- imply
  ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 → ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂ := by
-- proof
  intro ω₁ ω₂ hω₁ hω₂
  obtain ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, h_dim_bound⟩ :=
    dim_counting (F := F) (k := k) hsd ω₁ ω₂ hω₁ hω₂
  haveI := hU₁_fd
  haveI := hU₂_fd
  have h_grassmann := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
  have h_pos : 0 < Module.finrank k ↥(U₁ ⊓ U₂) := by omega
  rw [Module.finrank_pos_iff] at h_pos
  obtain ⟨⟨w, hw_mem⟩, ⟨w', hw'_mem⟩, hne⟩ := h_pos
  simp only [Ne, Subtype.mk.injEq] at hne
  by_cases hw0 : w = 0
  ·
    subst hw0
    have hw'_ne : w' ≠ 0 := fun h => hne (h ▸ rfl)
    obtain ⟨f₁, hf₁⟩ := hU₁_smul w' (Submodule.mem_inf.mp hw'_mem).1
    obtain ⟨f₂, hf₂⟩ := hU₂_smul w' (Submodule.mem_inf.mp hw'_mem).2
    exact ⟨f₁, f₂,
      fun h => hw'_ne (by rw [hf₁, h, zero_smul]),
      fun h => hw'_ne (by rw [hf₂, h, zero_smul]),
      by rw [← hf₁, ← hf₂]⟩
  ·
    obtain ⟨f₁, hf₁⟩ := hU₁_smul w (Submodule.mem_inf.mp hw_mem).1
    obtain ⟨f₂, hf₂⟩ := hU₂_smul w (Submodule.mem_inf.mp hw_mem).2
    exact ⟨f₁, f₂,
      fun h => hw0 (by rw [hf₁, h, zero_smul]),
      fun h => hw0 (by rw [hf₂, h, zero_smul]),
      by rw [← hf₁, ← hf₂]⟩

end WeilDifferential

namespace WeilDifferential

/--
[weil_differentials_finrank_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma weil_differentials_finrank_eq_one
  [Field F]
  {O : P → ValuationSubring F}
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [Nontrivial Ω]
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω) :
-- imply
  Module.finrank F Ω = 1 :=
-- proof
  finrank_eq_one_of_nonzero_proportional
    weil_differentials_nonzero
    (weil_differentials_proportional hsd)
end Theorem22_14
end WeilDifferential
namespace RiemannRochSpace
variable {C : Type*} {F : Type*} {k : Type*}
  [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
open CurveWithOrd CurveDivisor


namespace RiemannRochSpace

/--
[exists_weil_differential_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma exists_weil_differential_data
  [Field F]
  {O : P → ValuationSubring F}
  {C : Type u_C}
  {F : Type u_F}
  {k : Type u_k}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {W : CurveDivisor C}
-- given
  (hW : IsCanonicalDivisor W) :
-- imply
  ∃ (Ω : Type u_F) (_ : AddCommGroup Ω) (_ : Module F Ω) (_ : Module k Ω) (_ : IsScalarTower k F Ω) (divΩ : Ω → CurveDivisor C) (ω₀ : Ω), ω₀ ≠ 0 ∧ W = divΩ ω₀ ∧ (∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 → ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P) ∧ (∀ (c : k) (ω : Ω), c • ω ≠ 0 → ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P) ∧ (∀ (f : F) (hf : f ≠ 0), divΩ (f • ω₀) = principalDivisor (Units.mk0 f hf) + divΩ ω₀) ∧ (∀ ω' : Ω, ω' ≠ 0 → ∃ (f : F), f ≠ 0 ∧ ω' = f • ω₀) ∧ (∀ (f : F), f • ω₀ = 0 → f = 0) := by
-- proof
  classical
  let divΩ : F → CurveDivisor C := fun x =>
    if hx : x = 0 then 0 else principalDivisor (Units.mk0 x hx) + W
  have divΩ_ne : ∀ (x : F) (hx : x ≠ 0),
    divΩ x = principalDivisor (Units.mk0 x hx) + W := fun x hx => dif_neg hx
  have divΩ_zero : ∀ (x : F), x = 0 → divΩ x = 0 :=
    fun x hx => dif_pos hx
  have divΩ_one : divΩ 1 = W := by
    rw [divΩ_ne 1 one_ne_zero]
    simp [Units.mk0_one, principalDivisor_one]
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
    divΩ, 1, one_ne_zero, divΩ_one.symm, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ω₁ ω₂ hsum P
    by_cases h₁ : ω₁ = 0
    · subst h₁; simp only [zero_add, divΩ_zero 0 rfl, Finsupp.coe_zero, Pi.zero_apply]
      exact min_le_right _ _
    · by_cases h₂ : ω₂ = 0
      · subst h₂; simp only [add_zero, divΩ_zero 0 rfl, Finsupp.coe_zero, Pi.zero_apply]
        exact min_le_left _ _
      · rw [divΩ_ne ω₁ h₁, divΩ_ne ω₂ h₂, divΩ_ne (ω₁ + ω₂) hsum]
        simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
        have hord := CurveWithOrd.ord_add P (Units.mk0 ω₁ h₁)
          (Units.mk0 ω₂ h₂) hsum
        simp only [Units.val_mk0] at hord
        rw [min_add_add_right]; linarith
  ·
    intro c ω hne P
    have hω : ω ≠ 0 := by
      intro heq; rw [heq, smul_zero] at hne; exact hne rfl
    have hc : c ≠ 0 := by
      intro heq; rw [heq, zero_smul] at hne; exact hne rfl
    have hcsmul : c • ω ≠ 0 := hne
    rw [divΩ_ne ω hω, divΩ_ne (c • ω) hcsmul]
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
    have hcF : algebraMap k F c ≠ 0 :=
      (map_ne_zero_iff (algebraMap k F) (algebraMap k F).injective).mpr hc
    have hsmul_eq : c • ω = algebraMap k F c * ω := Algebra.smul_def c ω
    have hcU : Units.mk0 (c • ω) hcsmul =
      Units.mk0 (algebraMap k F c) hcF * Units.mk0 ω hω := by
      ext; simp [hsmul_eq]
    rw [hcU, CurveWithOrd.ord_mul]
    have hord_c := CurveWithConstants.ord_constant (F := F) P (Units.mk0 c hc)
    have : Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc) =
      Units.mk0 (algebraMap k F c) hcF := by ext; simp
    rw [this] at hord_c; linarith
  ·
    intro f hf
    have hfsmul : f • (1 : F) = f := mul_one f
    rw [hfsmul, divΩ_ne f hf, divΩ_one]
  ·
    intro ω' hω'
    exact ⟨ω', hω', (mul_one ω').symm⟩
  ·
    intro f hf
    simpa [mul_one] using hf

end RiemannRochSpace

namespace RiemannRochSpace

/--
[divisorDim_eq_zero_of_neg_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma divisorDim_eq_zero_of_neg_degree
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
-- given
  (hdeg : degree C D < 0) :
-- imply
  divisorDim (F := F) (k := k) D = 0 := by
-- proof
  by_contra h
  rw [divisorDim_eq_finrank] at h
  haveI := riemannRochSpace_finiteDimensional (F := F) (k := k) D
  have hpos : 0 < Module.finrank k (riemannRochSpace (F := F) (k := k) D) := by omega
  rw [Module.finrank_pos_iff] at hpos
  obtain ⟨⟨f, hf_mem⟩, ⟨g, hg_mem⟩, hne⟩ := hpos
  simp only [Ne, Subtype.mk.injEq] at hne
  have ⟨v, hv_mem, hv_ne⟩ : ∃ v : F, v ∈ riemannRochSpace (k := k) D ∧ v ≠ 0 := by
    by_cases hf0 : f = 0
    · exact ⟨g, hg_mem, fun h => hne (hf0 ▸ h ▸ rfl)⟩
    · exact ⟨f, hf_mem, hf0⟩
  have hv_eff := (mem_riemannRochSpace_of_ne_zero D v hv_ne).mp hv_mem
  have hdeg_sum : degree C (principalDivisor (Units.mk0 v hv_ne) + D) = degree C D := by
    rw [degree_add, degree_principalDivisor (k := k), zero_add]
  have hdeg_nonneg : 0 ≤ degree C (principalDivisor (Units.mk0 v hv_ne) + D) := by
    rw [degree_eq_sum]
    exact Finsupp.sum_nonneg (fun i _ => hv_eff i)
  linarith

end RiemannRochSpace

namespace RiemannRochSpace

/--
[isCanonicalDivisor_of_linearlyEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
lemma isCanonicalDivisor_of_linearlyEquivalent
  [Field F]
  {O : P → ValuationSubring F}
  {W D : CurveDivisor C}
-- given
  (hW : IsCanonicalDivisor W)
  (hprinc : IsPrincipal (F := F) (W - D)) :
-- imply
  IsCanonicalDivisor D := by
-- proof
  obtain ⟨Ω, instΩ, divΩ, ω, hω_ne, hW_eq⟩ := hW
  obtain ⟨f, hf_eq⟩ := (isPrincipal_iff (W - D)).mp hprinc
  refine ⟨Ω, instΩ, fun x => divΩ x - principalDivisor (C := C) f, ω, hω_ne, ?_⟩
  show D = divΩ ω - principalDivisor (C := C) f
  rw [hf_eq, hW_eq]
  abel
/-- (Corollary 22.24, (a) implies (b).) If $D$ is canonical then $\ell(D) = g$ and
$\deg D = 2g - 2$. -/

end RiemannRochSpace

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ext_eq
  [Field F]
  {O : P → ValuationSubring F}
  {α β : FunctionFieldAdeleRing F P O}
-- given
  (h : ∀ p, α p = β p) :
-- imply
  α = β := by
-- proof
  apply FunctionFieldAdeleRing.ext h

/--
[smul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma smul_apply_eq
  [Field F]
  {O : P → ValuationSubring F}
  {k : Type*}
  [Field k]
  [Algebra k F]
  [ConstantField k (O := O)]
  {c : k}
  {α : FunctionFieldAdeleRing F P O}
  {p : P} :
-- imply
  (c • α) p = algebraMap k F c * α p := by
-- proof
  apply FunctionFieldAdeleRing.smul_apply k c α p

/--
[RiemannRochData.ord_algebraMap_eq_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_algebraMap_eq_ax_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {c : kˣ} :
-- imply
  CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 := by
-- proof
  apply RiemannRochData.ord_algebraMap_eq_ax P c

/--
[RiemannRochData.ord_add_ge_min_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_add_ge_min_field_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {f g : Fˣ}
-- given
  (hfg : (f : F) + (g : F) ≠ 0) :
-- imply
  CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) := by
-- proof
  apply RiemannRochData.ord_add_ge_min_field P f g hfg

/--
[RiemannRochData.ord_algebraMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_algebraMap_eq_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {c : kˣ} :
-- imply
  CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 := by
-- proof
  apply RiemannRochData.ord_algebraMap_eq P c

/--
[RiemannRochData.ord_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_algebraMap_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {c : kˣ} :
-- imply
  CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 := by
-- proof
  apply RiemannRochData.ord_algebraMap P c

/--
[RiemannRochData.ord_add_ge_min_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_add_ge_min_ax_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {f g : Fˣ}
-- given
  (hfg : (f : F) + (g : F) ≠ 0) :
-- imply
  CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) := by
-- proof
  apply RiemannRochData.ord_add_ge_min_ax P f g hfg

/--
[RiemannRochData.ord_add_ge_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma ord_add_ge_min_eq
  [Field F]
  {O : P → ValuationSubring F}
  [Field k]
  [Field F]
  [Algebra k F]
  [RiemannRochData C F k]
  {P : C}
  {f g : Fˣ}
-- given
  (hfg : (f : F) + (g : F) ≠ 0) :
-- imply
  CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) := by
-- proof
  apply RiemannRochData.ord_add_ge_min P f g hfg

/--
[mem_riemannRochSpace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma mem_riemannRochSpace_iff_eq
  [Field F]
  {O : P → ValuationSubring F}
  {D : CurveDivisor C}
  {f : F} :
-- imply
  f ∈ riemannRochSpace (k := k) D ↔ f = 0 ∨ ∃ (hf : f ≠ 0), (principalDivisor (Units.mk0 f hf) + D).IsEffective := by
-- proof
  apply RiemannRochSpace.mem_riemannRochSpace_iff D f

/--
[mul_unit_mem_riemannRochSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean)
-/
@[path]
private lemma mul_unit_mem_riemannRochSpace_eq
  [Field F]
  {O : P → ValuationSubring F}
  {A B : CurveDivisor C}
  {f : Fˣ}
  {g : F}
-- given
  (hf : principalDivisor f = A - B)
  (hg : g ∈ riemannRochSpace (k := k) A) :
-- imply
  (f : F) * g ∈ riemannRochSpace (k := k) B := by
-- proof
  apply RiemannRochSpace.mul_unit_mem_riemannRochSpace A B f hf g hg


-- created on 2026-10-23
