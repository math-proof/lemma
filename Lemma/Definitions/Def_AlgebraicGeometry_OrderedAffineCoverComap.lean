import Lemma.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover

theorem preimage_iInf_fin {Y Z : Scheme.{u}} (f : Y ⟶ Z) {n : ℕ} (W : Fin (n + 1) → Z.Opens) :
    f ⁻¹ᵁ (⨅ j, W j) = ⨅ j, f ⁻¹ᵁ (W j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, W j) = W 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, f ⁻¹ᵁ (W j)) = f ⁻¹ᵁ (W 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit W, Scheme.Hom.preimage_inf, ih (fun j => W j.succ), hsplit (fun j => f ⁻¹ᵁ (W j))]

section Comap

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (f : Y ⟶ X) [IsAffineHom f]

def comap : Y.OrderedAffineCover where
  ι := 𝒰.ι
  instFintype := 𝒰.instFintype
  instLinearOrder := 𝒰.instLinearOrder
  U i := f ⁻¹ᵁ 𝒰.U i
  isAffineOpen i := (𝒰.isAffineOpen i).preimage f
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_eq_top]; rfl

theorem comap_ι : (𝒰.comap f).ι = 𝒰.ι := rfl

theorem comap_U (i : 𝒰.ι) : (𝒰.comap f).U i = f ⁻¹ᵁ 𝒰.U i := rfl

theorem comap_Idx (i : ℕ) : (𝒰.comap f).Idx i = 𝒰.Idx i := rfl

theorem comap_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) : (𝒰.comap f).face s j = 𝒰.face s j := rfl

theorem comap_inter {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s = f ⁻¹ᵁ 𝒰.inter s :=
  (preimage_iInf_fin f (fun j => 𝒰.U (s.1 j))).symm

theorem comap_inter_le {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s ≤ f ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.comap_inter f s).le

theorem le_comap_inter {i : ℕ} (s : 𝒰.Idx i) : f ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.comap f).inter s :=
  (𝒰.comap_inter f s).ge

end Comap

section BaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

abbrev baseChange : (Limits.pullback π (specMap R A)).OrderedAffineCover :=
  haveI := isAffineHom_fst π A
  𝒰.comap (Limits.pullback.fst π (specMap R A))

theorem baseChange_ι : (𝒰.baseChange π A).ι = 𝒰.ι := rfl

theorem baseChange_U (i : 𝒰.ι) :
    (𝒰.baseChange π A).U i = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.U i := rfl

theorem baseChange_Idx (i : ℕ) : (𝒰.baseChange π A).Idx i = 𝒰.Idx i := rfl

theorem baseChange_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) :
    (𝒰.baseChange π A).face s j = 𝒰.face s j := rfl

theorem baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  haveI := isAffineHom_fst π A
  𝒰.comap_inter _ s

theorem baseChange_inter_le {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.baseChange_inter π A s).le

theorem le_baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.baseChange π A).inter s :=
  (𝒰.baseChange_inter π A s).ge

end BaseChange

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem toOrderedAffineCover_pullback :
    (𝒱.pullback π A).toOrderedAffineCover = 𝒱.toOrderedAffineCover.baseChange π A := by
  unfold Scheme.TwoAffineOpenCover.toOrderedAffineCover Scheme.OrderedAffineCover.baseChange
    Scheme.OrderedAffineCover.comap
  congr 1
  funext i; rcases i with ⟨i⟩; fin_cases i <;> rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
