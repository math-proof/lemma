-- Carved from Lemma/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Lemma.AlgebraicCurve.CurveModel
import Instance.JacJ1_ChartAlgebra
import Instance.AlgebraicCurve_CurveModelSmooth
import Lemma.AlgebraicCurve.CurveModelConstruction

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

variable [Fact (t ≠ 0)]

instance isOpenImmersion_f₀ : IsOpenImmersion (f₀ K t) := by
  letI := (incl₀ K t).toRingHom.toAlgebra
  haveI := isLocalization_away_incl₀ K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tChart K t)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf K t) := by
  letI := (inclInf K t).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tInvChart K t)

end Charts

section Glue

variable [Fact (t ≠ 0)]

instance isOpenImmersion_ι₀ : IsOpenImmersion (ι₀ K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.right

end Glue

section Qualities

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

instance isIntegral_glued : IsIntegral (glued K t) := by
  let 𝒰 := Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))
  haveI : ∀ i, IsReduced (𝒰.X i) := by
    rintro (_ | _ | _)
    · change IsReduced (XOverlap K t); infer_instance
    · change IsReduced (X₀ K t); infer_instance
    · change IsReduced (XInf K t); infer_instance
  haveI : IsReduced (glued K t) := IsReduced.of_openCover _ 𝒰
  have hA : IsIrreducible (Set.range (ι₀ K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (X₀ K t)).image _
      (ι₀ K t).base.hom.continuous.continuousOn
  have hB : IsIrreducible (Set.range (ιInf K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (XInf K t)).image _
      (ιInf K t).base.hom.continuous.continuousOn
  have hBA : Set.range (ιInf K t).base ⊆ closure (Set.range (ι₀ K t).base) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hB.isPreirreducible
      (ι₀ K t).isOpenEmbedding.isOpen_range (range_ιInf_inter_range_ι₀_nonempty K t)).trans
      (closure_mono Set.inter_subset_right)
  have huniv : closure (Set.range (ι₀ K t).base) = Set.univ :=
    Set.eq_univ_of_univ_subset fun x _ =>
      (mem_range_ι₀_or_mem_range_ιInf K t x).elim (fun h => subset_closure h) fun h => hBA h
  haveI : IrreducibleSpace (glued K t) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
    exact hA.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance isFractionRing_overlap : IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) L :=
  IsFractionRing.of_field (chartRing K ({t, t⁻¹} : Set L)) L fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({t} : Set L)) z
    exact ⟨⟨a, chartRing_mono K (singleton_subset_pair t) a.2⟩,
      ⟨b, chartRing_mono K (singleton_subset_pair t) b.2⟩, rfl⟩

instance algebra_overlap_functionField :
    Algebra (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

instance isFractionRing_overlap_functionField :
    IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

instance isOpenImmersion_ιU : IsOpenImmersion (ιU K t) :=
  inferInstanceAs (IsOpenImmersion (f₀ K t ≫ ι₀ K t))

end Qualities

instance isIntegral_adjoin_chartRing (S : Set L) :
    Algebra.IsIntegral (Algebra.adjoin K S) (chartRing K S) :=
  IsIntegralClosure.isIntegral_algebra (Algebra.adjoin K S) (A := chartRing K S) L

section FiniteType

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance locallyOfFiniteType_gluedToBase : LocallyOfFiniteType (gluedToBase K t) := by
  have h₀' : LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t) := by
    rw [ι₀_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t) := by
    rw [ιInf_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      show colimit.ι (span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t)
    exact hInf'

instance jacobsonSpace_glued : JacobsonSpace (glued K t) :=
  LocallyOfFiniteType.jacobsonSpace (gluedToBase K t)

end FiniteType


section StalkRange

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

variable (A : Subalgebra K L) (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L))

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

scoped instance stalkAlgebra_spec (p : Spec (CommRingCat.of A)) :
    Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra (↥A) p

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

scoped instance isLocalization_stalk_spec (p : Spec (CommRingCat.of A)) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (↥A) p

end StalkRange


open IsLocalRing

section Compact

variable [Fact (t ≠ 0)]

instance compactSpace_glued : CompactSpace (glued K t) := by
  refine ⟨?_⟩
  have h : Set.range (ι₀ K t).base ∪ Set.range (ιInf K t).base = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_range_ι₀_or_mem_range_ιInf K t x
  rw [← h]
  exact (isCompact_range (ι₀ K t).base.hom.continuous).union
    (isCompact_range (ιInf K t).base.hom.continuous)

instance quasiCompact_gluedToBase : QuasiCompact (gluedToBase K t) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

end Compact

section Noetherian

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance isLocallyNoetherian_glued : IsLocallyNoetherian (glued K t) := by
  refine (isLocallyNoetherian_iff_openCover (X := glued K t)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XOverlap K t)
    haveI : IsNoetherianRing (chartRing K ({t, t⁻¹} : Set L)) := by
      letI := (incl₀ K t).toRingHom.toAlgebra
      haveI := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
      exact IsLocalization.isNoetherianRing (Submonoid.powers (tChart K t)) _ inferInstance
    infer_instance
  · change IsLocallyNoetherian (X₀ K t)
    infer_instance
  · change IsLocallyNoetherian (XInf K t)
    infer_instance

instance quasiSeparated_gluedToBase : QuasiSeparated (gluedToBase K t) :=
  QuasiSeparated.of_quasiSeparatedSpace _

end Noetherian


section Proper

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance isProper_gluedToBase : IsProper (gluedToBase K t) :=
  IsProper.of_valuativeCriterion (gluedToBase K t)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence K t, valuativeCriterion_uniqueness K t⟩)

end Proper

open TopologicalSpace


end CurveModel

end AlgebraicCurve

end
