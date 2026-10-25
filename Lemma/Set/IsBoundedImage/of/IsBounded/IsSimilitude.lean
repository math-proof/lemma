import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
open Classical ChamberComplex AffineCoxeter AffineCoxeterComplex AffineBuilding
open ChamberComplex
open AffineCoxeter


/--
[IsSimilitude.image_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma IsSimilitude.image_bounded
  [PseudoMetricSpace X]
  [PseudoMetricSpace Y]
  {f : X → Y}
  {c : ℝ}
  {S : Set X}
-- given
  (hf : IsSimilitude f c)
  (hS : Bornology.IsBounded S) :
-- imply
  Bornology.IsBounded (f '' S) := by
-- proof
  rw [Metric.isBounded_iff]
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hS
  exact ⟨c * D, fun x ⟨a, ha, hfa⟩ y ⟨b, hb, hfb⟩ => by
    rw [← hfa, ← hfb, hf.2 a b]; exact mul_le_mul_of_nonneg_left (hD ha hb) (le_of_lt hf.1)⟩

/--
[IsSimilitude.diam_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma IsSimilitude.diam_image
  [PseudoMetricSpace X]
  [PseudoMetricSpace Y]
  {f : X → Y}
  {c : ℝ}
  {S : Set X}
-- given
  (hf : IsSimilitude f c)
  (hS : Bornology.IsBounded S) :
-- imply
  Metric.diam (f '' S) = c * Metric.diam S := by
-- proof
  apply le_antisymm
  ·
    apply Metric.diam_le_of_forall_dist_le (mul_nonneg (le_of_lt hf.1) Metric.diam_nonneg)
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hf.2 a b]
    exact mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hS ha hb) (le_of_lt hf.1)
  ·
    have hfS_bdd := hf.image_bounded S hS
    rw [mul_comm, ← le_div_iff₀ hf.1]
    apply Metric.diam_le_of_forall_dist_le (div_nonneg Metric.diam_nonneg (le_of_lt hf.1))
    intro a ha b hb
    rw [le_div_iff₀ hf.1, mul_comm, ← hf.2 a b]
    exact Metric.dist_le_diam_of_mem hfS_bdd (Set.mem_image_of_mem f ha) (Set.mem_image_of_mem f hb)

/--
[IsSimilitude.const_eq_one_of_diam_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma IsSimilitude.const_eq_one_of_diam_preserved
  [PseudoMetricSpace X]
  [PseudoMetricSpace Y]
  {f : X → Y}
  {c : ℝ}
  {S : Set X}
-- given
  (hf : IsSimilitude f c)
  (hS_bdd : Bornology.IsBounded S)
  (hS_diam : Metric.diam S = 1)
  (hfS_diam : Metric.diam (f '' S) = 1) :
-- imply
  c = 1 := by
-- proof
  have h := hf.diam_image S hS_bdd
  rw [hfS_diam, hS_diam] at h
  linarith
namespace AffineCoxeterComplex
variable {B : Type*} [DecidableEq B]

namespace AffineCoxeterComplex

/--
[sc_iso_is_similitude](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma sc_iso_is_similitude
  [DecidableEq B]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex} :
-- imply
  ∃ (g : E →ᵃ[ℝ] E'), IsSimilitude (↑g) (A'.chamberDiameter / A.chamberDiameter) := by
-- proof
  obtain ⟨g, hg_sim, _hg_compat⟩ :=
    AffineCoxeter.coxeter_iso_induces_vertex_compatible_similitude A A' φ
  refine ⟨g, ?_, ?_⟩
  ·
    exact div_pos A'.chamberDiameter_pos A.chamberDiameter_pos
  ·
    intro x y
    simp only [dist_eq_norm]
    have h := hg_sim x y
    unfold AffineCoxeter.euclideanDist at h
    exact h

end AffineCoxeterComplex

namespace AffineCoxeterComplex

/--
[sc_iso_canonical_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma sc_iso_canonical_isometry
  [DecidableEq B]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']
  {A : AffineCoxeterComplex E}
  {A' : AffineCoxeterComplex E'}
  {φ : SimplicialComplexIso A.complex A'.complex}
-- given
  (hD_eq : A.chamberDiameter = A'.chamberDiameter) :
-- imply
  ∃ (g : E →ᵃ[ℝ] E'), ∀ x y : E, dist (g x) (g y) = dist x y := by
-- proof
  obtain ⟨g, hg_sim⟩ := sc_iso_is_similitude A A' φ
  have hμ_one : A'.chamberDiameter / A.chamberDiameter = 1 := by
    rw [← hD_eq]; exact div_self (ne_of_gt A.chamberDiameter_pos)
  exact ⟨g, fun x y => by rw [hg_sim.2 x y, hμ_one, one_mul]⟩

end AffineCoxeterComplex

namespace AffineCoxeterComplex

/--
[sc_iso_canonical_isometry'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma sc_iso_canonical_isometry'
  [DecidableEq B]
  [DecidableEq B]
  [DecidableEq B']
  {M : CoxeterMatrix B}
  {M' : CoxeterMatrix B'}
  [PseudoMetricSpace X]
  [PseudoMetricSpace X']
  {cm : CanonicalMetric M X}
  {cm' : CanonicalMetric M' X'}
  {φ : X → X'}
  {c : ℝ}
-- given
  (hφ : IsSimilitude φ c)
  (hφ_chambers : ∀ C ∈ cm.chambers, (φ '' C) ∈ cm'.chambers)
  (h_cover : ∀ x : X, ∃ C ∈ cm.chambers, x ∈ C)
  (hC_nonempty : cm.chambers.Nonempty) :
-- imply
  ∀ x y : X, dist (φ x) (φ y) = dist x y := by
-- proof
  obtain ⟨C, hC_mem⟩ := hC_nonempty
  have hC_diam : Metric.diam C = 1 := cm.chamber_diam_one C hC_mem
  have hφC_diam : Metric.diam (φ '' C) = 1 := cm'.chamber_diam_one (φ '' C) (hφ_chambers C hC_mem)
  have hC_bdd : Bornology.IsBounded C := cm.chamber_bounded C hC_mem
  have hc_one : c = 1 := hφ.const_eq_one_of_diam_preserved hC_bdd hC_diam hφC_diam
  intro x y
  rw [hφ.2 x y, hc_one, one_mul]

end AffineCoxeterComplex

namespace AffineCoxeterComplex

/--
[canonical_metric_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma canonical_metric_unique
  [DecidableEq B]
  [PseudoMetricSpace X]
  [PseudoMetricSpace Y]
  {chambersX : Set (Set X)}
  {chambersY : Set (Set Y)}
  {φ : X → Y}
  {c : ℝ}
-- given
  (hX_bdd : ∀ C ∈ chambersX, Bornology.IsBounded C)
  (hX_diam : ∀ C ∈ chambersX, Metric.diam C = 1)
  (hY_diam : ∀ C ∈ chambersY, Metric.diam C = 1)
  (hφ : IsSimilitude φ c)
  (hφ_chambers : ∀ C ∈ chambersX, (φ '' C) ∈ chambersY)
  (hne : chambersX.Nonempty) :
-- imply
  ∀ x y : X, dist (φ x) (φ y) = dist x y := by
-- proof
  obtain ⟨C, hC⟩ := hne
  have hc_one : c = 1 :=
    hφ.const_eq_one_of_diam_preserved (hX_bdd C hC) (hX_diam C hC) (hY_diam _ (hφ_chambers C hC))
  intro x y
  rw [hφ.2 x y, hc_one, one_mul]

end AffineCoxeterComplex

namespace AffineCoxeterComplex

/--
[canonical_metric_unique'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma canonical_metric_unique'
  [DecidableEq B]
  [DecidableEq B]
  [DecidableEq B']
  {M : CoxeterMatrix B}
  {M' : CoxeterMatrix B'}
  [PseudoMetricSpace X]
  [PseudoMetricSpace X']
  {cm : CanonicalMetric M X}
  {cm' : CanonicalMetric M' X'}
  {φ : X → X'}
  {c : ℝ}
-- given
  (hφ : IsSimilitude φ c)
  (hφ_chambers : ∀ C ∈ cm.chambers, (φ '' C) ∈ cm'.chambers)
  (hne : cm.chambers.Nonempty) :
-- imply
  ∀ x y : X, dist (φ x) (φ y) = dist x y :=
-- proof
  canonical_metric_unique cm.chambers cm'.chambers
    cm.chamber_bounded cm.chamber_diam_one cm'.chamber_diam_one
    φ hφ hφ_chambers hne
end AffineCoxeterComplex
variable {V : Type*} [DecidableEq V]
namespace AffineBuilding

end AffineCoxeterComplex

namespace AffineBuilding

/--
[iso_fix_from_shared_face_and_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma iso_fix_from_shared_face_and_chamber
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {C : Finset V}
  {x y : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hσ_A₁ : σ ∈ A₁.val.faces)
  (hσ_A₂ : σ ∈ A₂.val.faces)
  (hx_σ : x ∈ σ)
  (hy_σ : y ∈ σ)
  (hC_max : A₁.val.IsMaximal C)
  (hC_A₂ : C ∈ A₂.val.faces) :
-- imply
  ∃ φ : SimplicialMap A₁.val A₂.val, φ.toFun x = x ∧ φ.toFun y = y := by
-- proof
  obtain ⟨φ, hφ_σ, _hφ_C⟩ :=
    b.apartmentSystem.iso_exists A₁.val A₁.property A₂.val A₂.property
      σ hσ_A₁ hσ_A₂ C hC_max hC_A₂
  exact ⟨φ, hφ_σ x hx_σ, hφ_σ y hy_σ⟩

end AffineBuilding

namespace AffineBuilding

/--
[buildingDist_wellDefined_from_face_and_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma buildingDist_wellDefined_from_face_and_chamber
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ : Finset V}
  {C : Finset V}
  {x y : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hσ_A₁ : σ ∈ A₁.val.faces)
  (hσ_A₂ : σ ∈ A₂.val.faces)
  (hC_max : A₁.val.IsMaximal C)
  (hC_A₂ : C ∈ A₂.val.faces)
  (hx_σ : x ∈ σ)
  (hy_σ : y ∈ σ) :
-- imply
  md.dist_fn A₁ x y = md.dist_fn A₂ x y := by
-- proof
  obtain ⟨φ, hφx, hφy⟩ := iso_fix_from_shared_face_and_chamber b A₁ A₂
    σ C x y hσ_A₁ hσ_A₂ hx_σ hy_σ hC_max hC_A₂
  have h_iso := md.iso_isometry A₁ A₂ φ φ.map_face x y
  rw [h_iso, hφx, hφy]

end AffineBuilding

namespace AffineBuilding

/--
[buildingDist_wellDefined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma buildingDist_wellDefined
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {v w : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hcommon : ∃ σ ∈ A₁.val.faces, σ ∈ A₂.val.faces ∧ v ∈ σ ∧ w ∈ σ) :
-- imply
  md.dist_fn A₁ v w = md.dist_fn A₂ v w := by
-- proof
  obtain ⟨σ, hσ_A₁, hσ_A₂, hv_σ, hw_σ⟩ := hcommon
  obtain ⟨_, _, cc₁, hcc₁_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₁.val A₁.property
  obtain ⟨_, _, cc₂, hcc₂_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A₂.val A₂.property
  have hσ_cc₁ : σ ∈ cc₁.toSimplicialComplex.faces := hcc₁_eq ▸ hσ_A₁
  obtain ⟨C₁, hC₁_max_cc, hσ_sub_C₁⟩ := cc₁.exists_maximal σ hσ_cc₁
  have hC₁_max : A₁.val.IsMaximal C₁ := hcc₁_eq ▸ hC₁_max_cc
  have hσ_cc₂ : σ ∈ cc₂.toSimplicialComplex.faces := hcc₂_eq ▸ hσ_A₂
  obtain ⟨D₂, hD₂_max_cc, hσ_sub_D₂⟩ := cc₂.exists_maximal σ hσ_cc₂
  have hD₂_max : A₂.val.IsMaximal D₂ := hcc₂_eq ▸ hD₂_max_cc
  have hC₁_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₁.val A₁.property C₁ hC₁_max
  have hD₂_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A₂.val A₂.property D₂ hD₂_max
  obtain ⟨A₃_val, hA₃_mem, hC₁_A₃, hD₂_A₃⟩ :=
    b.apartmentSystem.contains_pair C₁ D₂ hC₁_bmax hD₂_bmax
  let A₃ : { A // A ∈ b.apartmentSystem.apartments } := ⟨A₃_val, hA₃_mem⟩
  have hσ_nonempty : σ.Nonempty := ⟨v, hv_σ⟩
  have hσ_A₃ : σ ∈ A₃.val.faces :=
    A₃_val.down_closed hC₁_A₃ hσ_sub_C₁ hσ_nonempty
  have h₁ := buildingDist_wellDefined_from_face_and_chamber b md A₁ A₃
    σ C₁ hσ_A₁ hσ_A₃ hC₁_max hC₁_A₃ v w hv_σ hw_σ
  have h₂ := buildingDist_wellDefined_from_face_and_chamber b md A₂ A₃
    σ D₂ hσ_A₂ hσ_A₃ hD₂_max hD₂_A₃ v w hv_σ hw_σ
  rw [h₁, ← h₂]

end AffineBuilding

namespace AffineBuilding

/--
[buildingDist_well_defined_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma buildingDist_well_defined_general
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {x y : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hx₁ : ∃ s ∈ A₁.val.faces, x ∈ s)
  (hy₁ : ∃ s ∈ A₁.val.faces, y ∈ s)
  (hx₂ : ∃ s ∈ A₂.val.faces, x ∈ s)
  (hy₂ : ∃ s ∈ A₂.val.faces, y ∈ s) :
-- imply
  md.dist_fn A₁ x y = md.dist_fn A₂ x y := by
-- proof
  obtain ⟨sx, hsx, hx_sx⟩ := hx₁
  have hx₁' : {x} ∈ A₁.val.faces :=
    A₁.val.down_closed hsx (Finset.singleton_subset_iff.mpr hx_sx) (Finset.singleton_nonempty x)
  obtain ⟨sy, hsy, hy_sy⟩ := hy₁
  have hy₁' : {y} ∈ A₁.val.faces :=
    A₁.val.down_closed hsy (Finset.singleton_subset_iff.mpr hy_sy) (Finset.singleton_nonempty y)
  obtain ⟨sx₂, hsx₂, hx_sx₂⟩ := hx₂
  have hx₂' : {x} ∈ A₂.val.faces :=
    A₂.val.down_closed hsx₂ (Finset.singleton_subset_iff.mpr hx_sx₂) (Finset.singleton_nonempty x)
  obtain ⟨sy₂, hsy₂, hy_sy₂⟩ := hy₂
  have hy₂' : {y} ∈ A₂.val.faces :=
    A₂.val.down_closed hsy₂ (Finset.singleton_subset_iff.mpr hy_sy₂) (Finset.singleton_nonempty y)
  exact buildingDist_well_defined_clean b md x y A₁ A₂ hx₁' hy₁' hx₂' hy₂'

end AffineBuilding

namespace AffineBuilding

/--
[telescoping_triangle_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
lemma telescoping_triangle_ineq
  [DecidableEq V]
  {d : α → α → ℝ}
-- given
  (htri : ∀ x y z, d x z ≤ d x y + d y z)
  (hzero : ∀ x, d x x ≤ 0) :
-- imply
  ∀ (l : List α) (hne : l ≠ []), d (l.head hne) (l.getLast hne) ≤ (List.zipWith d l l.tail).sum := by
-- proof
  intro l hne
  induction l with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp [List.head, List.getLast, List.tail]
      exact hzero a
    | cons c rest' =>
      have htail_ne : (c :: rest') ≠ [] := List.cons_ne_nil _ _
      have ih_tail := ih htail_ne
      have htail_simp : (c :: rest').tail = rest' := by simp [List.tail]
      rw [htail_simp] at ih_tail
      simp only [List.head, List.tail_cons, List.zipWith_cons_cons, List.sum_cons]
      have hhead_eq : (c :: rest').head htail_ne = c := by simp [List.head]
      have hlast_eq : (a :: c :: rest').getLast (List.cons_ne_nil a (c :: rest'))
        = (c :: rest').getLast htail_ne := by
        simp [List.getLast_cons]
      rw [hlast_eq]
      rw [hhead_eq] at ih_tail
      calc d a ((c :: rest').getLast htail_ne)
        ≤ d a c + d c ((c :: rest').getLast htail_ne) := htri a c _
        _ ≤ d a c + (List.zipWith d (c :: rest') rest').sum := by linarith

end AffineBuilding

/--
[buildingDist_wellDefined_from_face_and_chamber_cross](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
private lemma buildingDist_wellDefined_from_face_and_chamber_cross_eq
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ : Finset V}
  {C : Finset V}
  {x y : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hσ_A₁ : σ ∈ A₁.val.faces)
  (hσ_A₂ : σ ∈ A₂.val.faces)
  (hC_max : A₁.val.IsMaximal C)
  (hC_A₂ : C ∈ A₂.val.faces)
  (hx_σ : x ∈ σ)
  (hy_C : y ∈ C) :
-- imply
  md.dist_fn A₁ x y = md.dist_fn A₂ x y := by
-- proof
  apply AffineBuilding.buildingDist_wellDefined_from_face_and_chamber_cross b md A₁ A₂ σ C hσ_A₁ hσ_A₂ hC_max hC_A₂ x y hx_σ hy_C

/--
[buildingDist_well_defined_clean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean)
-/
@[path]
private lemma buildingDist_well_defined_clean_eq
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {v w : V}
-- given
  (A₁ A₂ : { A // A ∈ b.apartmentSystem.apartments })
  (hv₁ : {v} ∈ A₁.val.faces)
  (hw₁ : {w} ∈ A₁.val.faces)
  (hv₂ : {v} ∈ A₂.val.faces)
  (hw₂ : {w} ∈ A₂.val.faces) :
-- imply
  md.dist_fn A₁ v w = md.dist_fn A₂ v w := by
-- proof
  apply AffineBuilding.buildingDist_well_defined_clean b md v w A₁ A₂ hv₁ hw₁ hv₂ hw₂


-- created on 2026-10-23
