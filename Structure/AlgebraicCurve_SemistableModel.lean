import Mathlib
import Structure.AlgebraicCurve_SemistableCharts
import Abbrev.AlgebraicCurve_SemistableModel
import Instance.AlgebraicCurve_SemistableModel
import Def.AlgebraicCurve_SemistableModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve


variable {L : Type u} [Field L] (A : ValuationSubring L)
variable (F : Type v) [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} (Fbar : ιV → Type w) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : ιE → Annulus A F) (src tgt : ιE → ιV)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))

structure SemistableModel where

  X : Scheme.{u}

  toBase : X ⟶ Spec (CommRingCat.of A)
  [isIntegral : IsIntegral X]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [locallyOfFinitePresentation : LocallyOfFinitePresentation toBase]

  ffEquiv : F ≃+* X.functionField

  ffEquiv_algebraMap : ∀ a : A,
    ffEquiv (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a

  pt : Place L F → X

  localRing_pt : ∀ P, SemistableModel.localRing X ffEquiv (pt P) = P.toValuationSubring.toSubring

  toBase_pt : ∀ P, (toBase.base (pt P)).asIdeal = ⊥

  gen : ιV → X

  localRing_gen : ∀ i, SemistableModel.localRing X ffEquiv (gen i) = (C i).integers.toSubring

  toBase_gen : ∀ i, toBase.base (gen i) = IsLocalRing.closedPoint A

  sm : ∀ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes} → X

  nd : ιE → X

  classify_bijective : Function.Bijective
    (Sum.elim (fun _ : Unit => genericPoint X)
      (Sum.elim pt (Sum.elim gen (Sum.elim
        (fun iQ : (Σ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) => sm iQ.1 iQ.2) nd))) :
      Unit ⊕ (Place L F ⊕ (ιV ⊕ ((Σ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) ⊕ ιE))) → X)

  pt_specializes_sm : ∀ i (P : Place L F) (hP : P ∈ (C i).dom),
    pt P ⤳ sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩

  pt_specializes_nd : ∀ e, ∀ P ∈ (An e).dom, pt P ⤳ nd e

  eq_of_pt_specializes : ∀ (P : Place L F) (x : X), pt P ⤳ x → x = pt P ∨
    (∃ i, ∃ hP : P ∈ (C i).dom, x = sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩) ∨
    (∃ e, P ∈ (An e).dom ∧ x = nd e)

  gen_specializes_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}), gen i ⤳ sm i Q
  gen_specializes_nd : ∀ e, gen (src e) ⤳ nd e ∧ gen (tgt e) ⤳ nd e
  eq_of_gen_specializes : ∀ (j : ιV) (x : X), gen j ⤳ x → x = gen j ∨ (∃ Q, x = sm j Q) ∨
    (∃ e, (src e = j ∨ tgt e = j) ∧ x = nd e)

  eq_of_sm_specializes : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (x : X), sm i Q ⤳ x → x = sm i Q
  eq_of_nd_specializes : ∀ e (x : X), nd e ⤳ x → x = nd e

  localRing_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F),
    f ∈ SemistableModel.localRing X ffEquiv (sm i Q) ↔
      (f ∈ (C i).integers ∧ ∀ P ∈ (C i).dom, (C i).placeMap P = Q.1 → f ∈ P.toValuationSubring)

  localRing_nd : ∀ e (f : F), f ∈ SemistableModel.localRing X ffEquiv (nd e) ↔
      (f ∈ (C (src e)).integers ∧ f ∈ (C (tgt e)).integers ∧ ∀ P ∈ (An e).dom, f ∈ P.toValuationSubring)

  residue_mem_of_mem_localRing_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F) (hf : f ∈ (C i).integers),
    f ∈ SemistableModel.localRing X ffEquiv (sm i Q) →
      (C i).residue ⟨f, hf⟩ ∈ Q.1.toValuationSubring

  exists_residue_eq_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (g : Fbar i), g ∈ Q.1.toValuationSubring →
    ∃ (f : F) (hf : f ∈ (C i).integers), f ∈ SemistableModel.localRing X ffEquiv (sm i Q) ∧ (C i).residue ⟨f, hf⟩ = g

  exists_eq_mul_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F) (hf : f ∈ (C i).integers), f ∈ SemistableModel.localRing X ffEquiv (sm i Q) →
    (C i).residue ⟨f, hf⟩ = 0 → ∃ a ∈ maximalIdeal A, ∃ g ∈ SemistableModel.localRing X ffEquiv (sm i Q),
      f = algebraMap L F (a : L) * g

  residue_nd : ∀ e (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
    f ∈ SemistableModel.localRing X ffEquiv (nd e) →
      ∃ (h1 : (C (src e)).residue ⟨f, hs⟩ ∈ (xs e).toValuationSubring)
        (h2 : (C (tgt e)).residue ⟨f, ht⟩ ∈ (xt e).toValuationSubring) (c : ResidueField A),
        IsLocalRing.residue (xs e).toValuationSubring ⟨_, h1⟩ = algebraMap (ResidueField A) (xs e).ResidueField c ∧
        IsLocalRing.residue (xt e).toValuationSubring ⟨_, h2⟩ = algebraMap (ResidueField A) (xt e).ResidueField c

  exists_residue_eq_nd : ∀ e (g : ∀ j, Fbar j) (h1 : g (src e) ∈ (xs e).toValuationSubring)
    (h2 : g (tgt e) ∈ (xt e).toValuationSubring) (c : ResidueField A),
    IsLocalRing.residue (xs e).toValuationSubring ⟨_, h1⟩ = algebraMap (ResidueField A) (xs e).ResidueField c →
    IsLocalRing.residue (xt e).toValuationSubring ⟨_, h2⟩ = algebraMap (ResidueField A) (xt e).ResidueField c →
      ∃ (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
        f ∈ SemistableModel.localRing X ffEquiv (nd e) ∧
        (C (src e)).residue ⟨f, hs⟩ = g (src e) ∧ (C (tgt e)).residue ⟨f, ht⟩ = g (tgt e)

  exists_eq_mul_nd : ∀ e (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
    f ∈ SemistableModel.localRing X ffEquiv (nd e) →
    (C (src e)).residue ⟨f, hs⟩ = 0 → (C (tgt e)).residue ⟨f, ht⟩ = 0 →
      ∃ a ∈ maximalIdeal A, ∃ g ∈ SemistableModel.localRing X ffEquiv (nd e), f = algebraMap L F (a : L) * g

  pt_mem_smoothLocus : ∀ P, pt P ∈ toBase.smoothLocus
  gen_mem_smoothLocus : ∀ i, gen i ∈ toBase.smoothLocus
  sm_mem_smoothLocus : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}), sm i Q ∈ toBase.smoothLocus
  nd_not_mem_smoothLocus : ∀ e, nd e ∉ toBase.smoothLocus

attribute [instance] SemistableModel.isIntegral SemistableModel.isProper SemistableModel.flat
  SemistableModel.locallyOfFinitePresentation


namespace SemistableModel

variable {A F Fbar C An src tgt xs xt}


structure Descent (M : SemistableModel A F Fbar C An src tgt xs xt) where

  A₀ : Type u
  [commRing : CommRing A₀]
  [isNoetherianRing : IsNoetherianRing A₀]
  [henselianLocalRing : HenselianLocalRing A₀]

  ι : A₀ →+* A
  [isLocalHom : IsLocalHom ι]
  ι_injective : Function.Injective ι

  K₀ : Subfield L
  range_ι : Set.range (fun a : A₀ => ((ι a : A) : L)) = (A : Set L) ∩ (K₀ : Set L)
  [isAlgebraic : Algebra.IsAlgebraic K₀ L]

  residue_comp_surjective : Function.Surjective ((IsLocalRing.residue A).comp ι)

  X₀ : Scheme.{u}
  toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)
  [isIntegral₀ : IsIntegral X₀]
  [isProper₀ : IsProper toBase₀]
  [flat₀ : Flat toBase₀]
  [locallyOfFinitePresentation₀ : LocallyOfFinitePresentation toBase₀]

  iso : M.X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))
  iso_snd : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = M.toBase

  base_genericPoint :
    (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint M.X) =
      genericPoint X₀

  F₀ : Subfield F
  [isAlgebraic_F₀ : Algebra.IsAlgebraic F₀ F]

  ffEquiv₀ : F₀ ≃+* X₀.functionField

  ffEquiv₀_ffEquiv : ∀ s : F₀, M.ffEquiv (s : F) =
    ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint M.X)).hom
      ((X₀.presheaf.stalkSpecializes (specializes_of_eq base_genericPoint)).hom (ffEquiv₀ s))

attribute [instance] Descent.commRing Descent.isNoetherianRing Descent.henselianLocalRing Descent.isLocalHom
  Descent.isAlgebraic Descent.isIntegral₀ Descent.isProper₀ Descent.flat₀ Descent.locallyOfFinitePresentation₀
  Descent.isAlgebraic_F₀


end SemistableModel

end AlgebraicCurve

end
