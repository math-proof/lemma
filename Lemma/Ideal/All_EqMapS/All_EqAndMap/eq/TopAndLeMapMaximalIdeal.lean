import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type (u + 1))}

private lemma map_germ_ideal_eq
  (I : X.IdealSheafData) {x : X} (V W : X.affineOpens)
  (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)) :
  Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
    Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W) := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hV, hW⟩
  have key : ∀ (T : X.affineOpens) (hT : x ∈ (T : X.Opens)) (hle : (X.affineBasicOpen f : X.Opens) ≤ (T : X.Opens)), Ideal.map (X.presheaf.germ (T : X.Opens) x hT).hom (I.ideal T) =
    Ideal.map (X.presheaf.germ (X.affineBasicOpen f : X.Opens) x hxf).hom
      (I.ideal (X.affineBasicOpen f)) := by
    intro T hT hle
    rw [← I.map_ideal (U := X.affineBasicOpen f) (V := T) hle, Ideal.map_map]
    congr 1
    rw [← TopCat.Presheaf.germ_res X.presheaf (homOfLE hle) x hxf, CommRingCat.hom_comp]
    rfl
  rw [key V hV (X.basicOpen_le f), key W hW]
  change X.basicOpen f ≤ (W : X.Opens)
  rw [hfg]
  apply X.basicOpen_le g
private lemma ideal_le_primeIdealOf_of_mem_support
  (U : X.affineOpens) (a : (U : X.Opens)) (K : X.IdealSheafData)
  (ha : (a : X) ∈ (K.support : Set X)) :
  K.ideal U ≤ (U.2.primeIdealOf a).asIdeal := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let _ := hU.isLocalization_stalk a
  intro f hf
  have hz : (a : X) ∈ X.zeroLocus (K.ideal U : Set (X.presheaf.obj (op U))) := by
    rw [← Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) a.2]
    apply ha
  have hnb : (a : X) ∉ X.basicOpen f := by
    rw [X.mem_zeroLocus_iff] at hz
    apply hz f hf
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (a : X)) (hU.primeIdealOf a).asIdeal f,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hnb
  rw [X.mem_basicOpen (U := U) f a a.2]
  apply hu
private lemma map_germ_ideal_eq_top_of_not_mem_support
  (U : X.affineOpens) (a : (U : X.Opens)) (K : X.IdealSheafData)
  (ha : (a : X) ∉ (K.support : Set X)) :
  Ideal.map (algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (a : X))) (K.ideal U) = ⊤ := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have ha' : ¬ ∀ f ∈ (K.ideal U : Set (X.presheaf.obj (op U))), (a : X) ∉ X.basicOpen f := by
    intro h
    apply ha
    change (a : X) ∈ K.support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) a.2]
    rw [X.mem_zeroLocus_iff]
    apply h
  push Not at ha'
  obtain ⟨f, hf, hfa⟩ := ha'
  have hu : IsUnit ((X.presheaf.germ (U : X.Opens) (a : X) a.2).hom f) := by
    rw [← X.mem_basicOpen (U := U) f a a.2]
    apply hfa
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) hu
private lemma ideal_le_of_forall_map_germ_le
  {V : X.Opens} (hV : IsAffineOpen V) {I' J' : Ideal (X.presheaf.obj (op V))}
  (h : ∀ (x : X) (hx : x ∈ V), I'.map (X.presheaf.germ V x hx).hom ≤
    J'.map (X.presheaf.germ V x hx).hom) :
  I' ≤ J' := by
  intro a ha
  let K : Ideal (X.presheaf.obj (op V)) :=
    { carrier := {c | c * a ∈ J'}
      add_mem' := fun {c d} hc hd => by
        simp only [Set.mem_ofPred_eq, add_mul]
        apply J'.add_mem hc hd
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, zero_mul]
        apply J'.zero_mem
      smul_mem' := fun c d hd => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_assoc]
        apply J'.mul_mem_left c hd }
  suffices hK : K = ⊤ by
    have h1 : (1 : (X.presheaf.obj (op V))) ∈ K := hK ▸ Submodule.mem_top
    have h1' : 1 * a ∈ J' := h1
    rwa [one_mul] at h1'
  rw [← Ideal.span_eq K, ← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : (X.presheaf.obj (op V)))) fun x hx => ?_
  let _ := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let _ := hV.isLocalization_stalk ⟨x, hx⟩
  have hmem : algebraMap (X.presheaf.obj (op V)) (X.presheaf.stalk x) a ∈
    J'.map (algebraMap (X.presheaf.obj (op V)) (X.presheaf.stalk x)) :=
    h x hx (Ideal.mem_map_of_mem _ ha)
  rw [IsLocalization.mem_map_algebraMap_iff (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _] at hmem
  obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, hjs⟩ := hmem
  simp only at hjs
  rw [← map_mul] at hjs
  rw [IsLocalization.eq_iff_exists (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _] at hjs
  obtain ⟨⟨c, hc⟩, hcas⟩ := hjs
  simp only at hcas
  have hf : c * s ∈ K := by
    show c * s * a ∈ J'
    rw [mul_assoc, mul_comm s a, hcas]
    apply J'.mul_mem_left c hj
  rw [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⟨c * s, hf⟩, ?_⟩
  rw [X.mem_basicOpen _ x hx]
  apply IsLocalization.map_units (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    (X.presheaf.stalk x) ⟨c * s, mul_mem hc hs⟩
private lemma map_germ_ideal_le_maximalIdeal_of_mem_support
  (U : X.affineOpens) (a : (U : X.Opens)) (K : X.IdealSheafData)
  (ha : (a : X) ∈ (K.support : Set X)) :
  Ideal.map (X.presheaf.germ (U : X.Opens) (a : X) a.2).hom (K.ideal U) ≤
    IsLocalRing.maximalIdeal (X.presheaf.stalk (a : X)) := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let _ := X.presheaf.algebra_section_stalk a
  let _ := hU.isLocalization_stalk a
  have hle := ideal_le_primeIdealOf_of_mem_support U a K ha
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  have hf' : f ∈ (hU.primeIdealOf a).asIdeal := hle hf
  rw [Ideal.mem_comap]
  change algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (a : X)) f ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk (a : X))
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (a : X)) (hU.primeIdealOf a).asIdeal f]
  apply hf'
private lemma ext_of_forall_exists_map_germ_ideal_eq
  {I J : X.IdealSheafData}
  (h : ∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ (U : X.Opens)), Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) =
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (J.ideal U)) :
  I = J := by
  have key : ∀ (V : X.affineOpens) (x : X) (hx : x ∈ (V : X.Opens)), Ideal.map (X.presheaf.germ (V : X.Opens) x hx).hom (I.ideal V) =
    Ideal.map (X.presheaf.germ (V : X.Opens) x hx).hom (J.ideal V) := by
    intro V x hx
    obtain ⟨U, hxU, hU⟩ := h x
    rw [map_germ_ideal_eq I V U hx hxU, map_germ_ideal_eq J V U hx hxU, hU]
  apply Scheme.IdealSheafData.ext
  funext V
  apply le_antisymm
  · apply ideal_le_of_forall_map_germ_le V.2 (fun x hx => (key V x hx).le)
  · apply ideal_le_of_forall_map_germ_le V.2 (fun x hx => (key V x hx).ge)
/--
[AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} :
  (∀ (I : X.IdealSheafData) (x : X) (V W : X.affineOpens) (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)), Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
    Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W)) ∧
    (∀ (I J : X.IdealSheafData), (∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ (U : X.Opens)), Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) =
      Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (J.ideal U)) → I = J) ∧
    (∀ (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)), (x ∉ (I.support : Set X) → Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) = ⊤) ∧
      (x ∈ (I.support : Set X) → Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x))) := by
  refine ⟨fun I x V W hV hW => map_germ_ideal_eq I V W hV hW, fun I J h => ext_of_forall_exists_map_germ_ideal_eq h, ?_⟩
  intro I U x hx
  refine ⟨fun hns => ?_, fun hs => ?_⟩
  · apply map_germ_ideal_eq_top_of_not_mem_support U ⟨x, hx⟩ I hns
  · apply map_germ_ideal_le_maximalIdeal_of_mem_support U ⟨x, hx⟩ I hs


-- created on 2026-10-20
