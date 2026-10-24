import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits TensorCategories


namespace TensorCategories

/--
[simple_of_endoIsIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma simple_of_endoIsIso
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Abelian C]
  {X : C}
-- given
  (hne : ¬ IsZero X)
  (hendo : ∀ (g : X ⟶ X), g ≠ 0 → IsIso g)
  (hlift : ∀ {Y : C} (f : Y ⟶ X) [Mono f], f ≠ 0 → ∃ (k : X ⟶ Y), k ≠ 0) :
-- imply
  Simple X where mono_isIso_iff_nonzero :=
-- proof
  fun {Y} f => by
    intro _hMono
    constructor
    ·
      intro hiso hf0
      subst hf0
      apply hne
      rw [IsZero.iff_id_eq_zero]
      have := IsIso.inv_hom_id (f := (0 : Y ⟶ X))
      simp at this
      exact this.symm
    ·
      intro hf
      obtain ⟨k, hk⟩ := hlift f hf
      have hkf_ne : k ≫ f ≠ 0 := by
        intro h; apply hk; rwa [← cancel_mono f, zero_comp]
      haveI : IsIso (k ≫ f) := hendo (k ≫ f) hkf_ne
      set s := inv (k ≫ f) ≫ k
      have hsec : s ≫ f = 𝟙 X := by simp [s, assoc]
      have : (f ≫ s) ≫ f = (𝟙 Y) ≫ f := by
        rw [assoc]; simp [hsec]
      exact ⟨⟨s, (cancel_mono f).mp this, hsec⟩⟩

end TensorCategories

namespace TensorCategories

/--
[pi_single_corner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma pi_single_corner
  {n : ℕ}
  {M : Fin n → Type*}
  [∀ i, Ring (M i)]
  {i : Fin n}
-- given
  (x : ∀ j, M j) :
-- imply
  Pi.single (M := M) i 1 * x * Pi.single (M := M) i 1 = Pi.single (M := M) i (x i) := by
-- proof
  ext j; by_cases hij : j = i
  · subst hij; simp [Pi.mul_apply, Pi.single_eq_same]
  · simp [Pi.mul_apply, Pi.single_eq_of_ne hij]

end TensorCategories

namespace TensorCategories

/--
[pi_single_mul_pi_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma pi_single_mul_pi_single
  {n : ℕ}
  {M : Fin n → Type*}
  [∀ i, Ring (M i)]
  {i : Fin n}
  {a b : M i} :
-- imply
  Pi.single (M := M) i a * Pi.single (M := M) i b = Pi.single (M := M) i (a * b) := by
-- proof
  ext j; by_cases hij : j = i
  · subst hij; simp [Pi.mul_apply, Pi.single_eq_same]
  · simp [Pi.mul_apply, Pi.single_eq_of_ne hij]
set_option maxHeartbeats 800000 in
set_option maxRecDepth 1000 in

end TensorCategories

namespace TensorCategories

/--
[commSemisimpleRing_primitiveIdempotents](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma commSemisimpleRing_primitiveIdempotents
  {R : Type*}
  [Ring R]
  [IsSemisimpleRing R]
-- given
  (hcomm : ∀ (a b : R), a * b = b * a) :
-- imply
  ∃ (n : ℕ) (e : Fin n → R), CompleteOrthogonalIdempotents e ∧ (∀ i, e i ≠ 0) ∧ (∀ i (h : R), h ≠ 0 → e i * h * e i = h → ∃ (sinv : R), h * sinv = e i ∧ sinv * h = e i) := by
-- proof
  obtain ⟨n, D, d, hDiv, hNe, ⟨φ⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)
  let e : Fin n → R := fun i => φ.symm (Pi.single (M := M) i 1)
  have hcoi : CompleteOrthogonalIdempotents e := by
    have : e = φ.symm.toRingHom ∘ (fun i => Pi.single (M := M) i 1) := by ext; simp [e]
    rw [this]; exact (CompleteOrthogonalIdempotents.single M).map φ.symm.toRingHom
  have hne : ∀ i, e i ≠ 0 := by
    intro i hi
    have h1 : (Pi.single (M := M) i 1 : ∀ j, M j) = 0 := by
      have := congr_arg φ hi; simp [e] at this
    have := congr_fun h1 i; simp at this
  have hfactor_comm : ∀ i (a b : M i), a * b = b * a := by
    intro i a b
    have h := hcomm (φ.symm (Pi.single i a)) (φ.symm (Pi.single i b))
    rw [← map_mul, ← map_mul] at h
    have h2 := φ.symm.injective h
    rw [pi_single_mul_pi_single, pi_single_mul_pi_single] at h2
    have h3 := congr_fun h2 i; simp at h3; exact h3
  have hField : ∀ i, IsField (M i) := by
    intro i; letI := hDiv i; letI := hNe i
    haveI : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    haveI : IsSimpleRing (M i) := IsSimpleRing.matrix (Fin (d i)) (D i)
    letI : CommRing (M i) := { (inferInstance : Ring (M i)) with mul_comm := hfactor_comm i }
    exact (isSimpleRing_iff_isField (M i)).mp ‹_›
  refine ⟨n, e, hcoi, hne, fun i h hh hcorner => ?_⟩
  have he_phi : φ (e i) = Pi.single (M := M) i 1 := φ.apply_symm_apply _
  have hcorner_phi : φ h = Pi.single (M := M) i (φ h i) := by
    have key : Pi.single (M := M) i 1 * φ h * Pi.single (M := M) i 1 = φ h := by
      calc Pi.single (M := M) i 1 * φ h * Pi.single (M := M) i 1
        = φ (e i) * φ h * φ (e i) := by rw [he_phi]
        _ = φ (e i * h * e i) := by rw [map_mul, map_mul]
        _ = φ h := by rw [hcorner]
    exact key.symm.trans (pi_single_corner i (φ h))
  have hhi_ne : φ h i ≠ 0 := by
    intro heq; apply hh; apply φ.injective
    simp only [map_zero, hcorner_phi, heq, Pi.single_zero]
  obtain ⟨b, hab⟩ := (hField i).mul_inv_cancel hhi_ne
  let sinv := φ.symm (Pi.single (M := M) i b)
  refine ⟨sinv, ?_, ?_⟩
  ·
    apply φ.injective; show φ (h * sinv) = φ (e i)
    rw [map_mul, he_phi]
    show φ h * φ sinv = Pi.single (M := M) i 1
    simp only [sinv, φ.apply_symm_apply]
    rw [hcorner_phi, pi_single_mul_pi_single, hab]
  ·
    apply φ.injective; show φ (sinv * h) = φ (e i)
    rw [map_mul, he_phi]
    show φ sinv * φ h = Pi.single (M := M) i 1
    simp only [sinv, φ.apply_symm_apply]
    rw [hcorner_phi, pi_single_mul_pi_single, hfactor_comm i b _, hab]

end TensorCategories

namespace TensorCategories

/--
[isIso_of_corner_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma isIso_of_corner_inv
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  {X fi : C}
  {ι : fi ⟶ X}
  {π : X ⟶ fi}
  {e : X ⟶ X}
  {g : fi ⟶ fi}
  {sinv : X ⟶ X}
-- given
  (hret : ι ≫ π = 𝟙 fi)
  (hsplit : π ≫ ι = e)
  (hinv_l : π ≫ g ≫ ι ≫ sinv = e)
  (hinv_r : sinv ≫ π ≫ g ≫ ι = e) :
-- imply
  IsIso g := by
-- proof
  have key : ι ≫ e ≫ π = 𝟙 fi := by rw [← hsplit]; simp [assoc, hret]
  refine ⟨⟨ι ≫ sinv ≫ π, ?_, ?_⟩⟩
  · calc g ≫ ι ≫ sinv ≫ π
    = (ι ≫ π) ≫ g ≫ ι ≫ sinv ≫ π := by simp [hret]
    _ = ι ≫ (π ≫ g ≫ ι ≫ sinv) ≫ π := by simp only [assoc]
    _ = ι ≫ e ≫ π := by rw [hinv_l]
    _ = 𝟙 fi := key
  · calc (ι ≫ sinv ≫ π) ≫ g
    = ι ≫ sinv ≫ π ≫ g := by simp only [assoc]
    _ = ι ≫ sinv ≫ π ≫ g ≫ (ι ≫ π) := by simp [hret]
    _ = ι ≫ (sinv ≫ π ≫ g ≫ ι) ≫ π := by simp only [assoc]
    _ = ι ≫ e ≫ π := by rw [hinv_r]
    _ = 𝟙 fi := key

end TensorCategories

namespace TensorCategories

/--
[primitive_idempotent_endoIsIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma primitive_idempotent_endoIsIso
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [Abelian C]
-- given
  (hss : IsSemisimpleRing (End (𝟙_ C))) :
-- imply
  ∃ (n : ℕ) (e : Fin n → End (𝟙_ C)), CompleteOrthogonalIdempotents e ∧ (∀ i, e i ≠ 0) ∧ ∀ (f : Fin n → C) (ι_hom : ∀ i, f i ⟶ 𝟙_ C) (π_hom : ∀ i, 𝟙_ C ⟶ f i), (∀ i, ι_hom i ≫ π_hom i = 𝟙 (f i)) → (∀ i, π_hom i ≫ ι_hom i = e i) → ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g := by
-- proof
  letI := hss
  obtain ⟨n, e, hcoi, hne, corner_inv⟩ :=
    commSemisimpleRing_primitiveIdempotents (End (𝟙_ C)) (mul_comm)
  refine ⟨n, e, hcoi, hne, fun f ι_hom π_hom hret hsplit i g hg => ?_⟩
  let h : End (𝟙_ C) := π_hom i ≫ g ≫ ι_hom i
  have hh_ne : h ≠ 0 := by
    intro hh0
    apply hg
    calc g = 𝟙 (f i) ≫ g ≫ 𝟙 (f i) := by simp
      _ = (ι_hom i ≫ π_hom i) ≫ g ≫ (ι_hom i ≫ π_hom i) := by rw [hret i]
      _ = ι_hom i ≫ (π_hom i ≫ g ≫ ι_hom i) ≫ π_hom i := by simp only [assoc]
      _ = ι_hom i ≫ (h : 𝟙_ C ⟶ 𝟙_ C) ≫ π_hom i := rfl
      _ = 0 := by rw [show (h : 𝟙_ C ⟶ 𝟙_ C) = (0 : 𝟙_ C ⟶ 𝟙_ C) from hh0]; simp
  have hcorner : e i * h * e i = h := by
    show e i ≫ (π_hom i ≫ g ≫ ι_hom i) ≫ e i = π_hom i ≫ g ≫ ι_hom i
    rw [← hsplit i]
    simp only [assoc]
    slice_lhs 2 3 => rw [hret i]
    simp only [id_comp]
    slice_lhs 3 4 => rw [hret i]
    simp
  obtain ⟨sinv, hinv_l, hinv_r⟩ := corner_inv i h hh_ne hcorner
  have hinv_l' : π_hom i ≫ g ≫ ι_hom i ≫ sinv = e i := by
    have key : (h : 𝟙_ C ⟶ 𝟙_ C) ≫ sinv = (e i : 𝟙_ C ⟶ 𝟙_ C) := hinv_r
    dsimp only [h] at key
    simp only [assoc] at key; exact key
  have hinv_r' : sinv ≫ π_hom i ≫ g ≫ ι_hom i = e i := by
    have key : sinv ≫ (h : 𝟙_ C ⟶ 𝟙_ C) = (e i : 𝟙_ C ⟶ 𝟙_ C) := hinv_l
    dsimp only [h] at key
    exact key
  exact isIso_of_corner_inv (ι_hom i) (π_hom i) (e i) g
    (hret i) (hsplit i) sinv hinv_l' hinv_r'

end TensorCategories

namespace TensorCategories

/--
[idempotent_summands_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma idempotent_summands_simple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [Abelian C]
  {n : ℕ}
  {e : Fin n → End (𝟙_ C)}
  {f : Fin n → C}
-- given
  (_hss : IsSemisimpleRing (End (𝟙_ C)))
  (_hcoi : CompleteOrthogonalIdempotents e)
  (ι_hom : ∀ i, f i ⟶ 𝟙_ C)
  (π_hom : ∀ i, 𝟙_ C ⟶ f i)
  (_hretract : ∀ i, ι_hom i ≫ π_hom i = 𝟙 (f i))
  (hsplit : ∀ i, π_hom i ≫ ι_hom i = e i)
  (hne : ∀ i, e i ≠ 0)
  (hendo : ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g)
  (hlift : ∀ i, ∀ {Y : C} (m : Y ⟶ f i) [Mono m], m ≠ 0 → ∃ (k : f i ⟶ Y), k ≠ 0) :
-- imply
  ∀ i, Simple (f i) := by
-- proof
  intro i
  have hne_fi : ¬ IsZero (f i) := by
    intro hZ
    apply hne i
    have h_id : 𝟙 (f i) = 0 := (IsZero.iff_id_eq_zero _).mp hZ
    calc (e i : 𝟙_ C ⟶ 𝟙_ C) = π_hom i ≫ ι_hom i := (hsplit i).symm
      _ = π_hom i ≫ (𝟙 (f i) ≫ ι_hom i) := by rw [id_comp]
      _ = π_hom i ≫ (0 ≫ ι_hom i) := by rw [h_id]
      _ = 0 := by simp
  exact simple_of_endoIsIso hne_fi (hendo i) (hlift i)

end TensorCategories

namespace TensorCategories

/--
[hom_eq_zero_of_orthogonal_idempotent_summands](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma hom_eq_zero_of_orthogonal_idempotent_summands
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [Abelian C]
  {n : ℕ}
  {e : Fin n → End (𝟙_ C)}
  {f : Fin n → C}
  {i j : Fin n}
  {g : f i ⟶ f j}
-- given
  (hcoi : CompleteOrthogonalIdempotents e)
  (ι_hom : ∀ i, f i ⟶ 𝟙_ C)
  (π_hom : ∀ i, 𝟙_ C ⟶ f i)
  (hretract : ∀ i, ι_hom i ≫ π_hom i = 𝟙 (f i))
  (hsplit : ∀ i, π_hom i ≫ ι_hom i = e i)
  (hij : i ≠ j) :
-- imply
  g = 0 := by
-- proof
  have hg : g = ι_hom i ≫ (π_hom i ≫ g ≫ ι_hom j) ≫ π_hom j := by
    calc g = 𝟙 (f i) ≫ g ≫ 𝟙 (f j) := by simp
      _ = (ι_hom i ≫ π_hom i) ≫ g ≫ (ι_hom j ≫ π_hom j) := by rw [hretract i, hretract j]
      _ = ι_hom i ≫ (π_hom i ≫ g ≫ ι_hom j) ≫ π_hom j := by simp [assoc]
  set h : 𝟙_ C ⟶ 𝟙_ C := π_hom i ≫ g ≫ ι_hom j
  have hortho : (e i : 𝟙_ C ⟶ 𝟙_ C) ≫ (e j : 𝟙_ C ⟶ 𝟙_ C) = 0 :=
    hcoi.ortho (Ne.symm hij)
  have hcomm : (e i : 𝟙_ C ⟶ 𝟙_ C) ≫ h = h ≫ (e i : 𝟙_ C ⟶ 𝟙_ C) :=
    endUnit_comm (e i) h
  have hfactor : h = (e i : 𝟙_ C ⟶ 𝟙_ C) ≫ h ≫ (e j : 𝟙_ C ⟶ 𝟙_ C) := by
    symm
    calc (e i : 𝟙_ C ⟶ 𝟙_ C) ≫ h ≫ (e j : 𝟙_ C ⟶ 𝟙_ C)
      = (π_hom i ≫ ι_hom i) ≫ (π_hom i ≫ g ≫ ι_hom j) ≫ (π_hom j ≫ ι_hom j) := by
        rw [hsplit i, hsplit j]
      _ = π_hom i ≫ (ι_hom i ≫ π_hom i) ≫ g ≫ (ι_hom j ≫ π_hom j) ≫ ι_hom j := by
        simp [assoc]
      _ = π_hom i ≫ g ≫ ι_hom j := by rw [hretract i, hretract j]; simp
  have hzero : h = 0 := by
    rw [hfactor, ← assoc, hcomm, assoc, hortho, comp_zero]
  rw [hg, hzero, zero_comp, comp_zero]

end TensorCategories

namespace TensorCategories

/--
[idempotent_summands_simple_and_noniso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma idempotent_summands_simple_and_noniso
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [Abelian C]
  {n : ℕ}
  {e : Fin n → End (𝟙_ C)}
  {f : Fin n → C}
-- given
  (hss : IsSemisimpleRing (End (𝟙_ C)))
  (hcoi : CompleteOrthogonalIdempotents e)
  (ι_hom : ∀ i, f i ⟶ 𝟙_ C)
  (π_hom : ∀ i, 𝟙_ C ⟶ f i)
  (hretract : ∀ i, ι_hom i ≫ π_hom i = 𝟙 (f i))
  (hsplit : ∀ i, π_hom i ≫ ι_hom i = e i)
  (hne : ∀ i, e i ≠ 0)
  (hendo : ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g)
  (hlift : ∀ i, ∀ {Y : C} (m : Y ⟶ f i) [Mono m], m ≠ 0 → ∃ (k : f i ⟶ Y), k ≠ 0) :
-- imply
  (∀ i, Simple (f i)) ∧ (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) := by
-- proof
  have hsimp := idempotent_summands_simple hss e hcoi f ι_hom π_hom hretract hsplit hne hendo hlift
  refine ⟨hsimp, ?_⟩
  intro i j hij ⟨φ⟩
  have h1 : φ.hom = 0 :=
    hom_eq_zero_of_orthogonal_idempotent_summands e hcoi f ι_hom π_hom hretract hsplit hij φ.hom
  have h2 : 𝟙 (f i) = 0 := by rw [← φ.hom_inv_id, h1, zero_comp]
  haveI : Simple (f i) := hsimp i
  exact Simple.not_isZero (f i) ((IsZero.iff_id_eq_zero (f i)).mpr h2)

end TensorCategories

namespace TensorCategories

/--
[idempotent_lifting_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma idempotent_lifting_decomposition
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
-- given
  (hss : IsSemisimpleRing (End (𝟙_ C)))
  (hlift : ∀ {X : C}, (∀ (g : X ⟶ X), g ≠ 0 → IsIso g) → ∀ {Y : C} (m : Y ⟶ X) [Mono m], m ≠ 0 → ∃ (k : X ⟶ Y), k ≠ 0) :
-- imply
  ∃ (n : ℕ) (f : Fin n → C) (hbp : HasBiproduct f), (∀ i, Simple (f i)) ∧ (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) ∧ Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp) := by
-- proof
  obtain ⟨n, e, hcoi, hne, hendo_axiom⟩ := primitive_idempotent_endoIsIso hss
  obtain ⟨f, ι_hom, π_hom, hretract, hsplit, hbp, hiso⟩ :=
    biproduct_from_completeOrthogonalIdempotents e hcoi
  have hendo : ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g :=
    hendo_axiom f ι_hom π_hom hretract hsplit
  have hlift_i : ∀ i, ∀ {Y : C} (m : Y ⟶ f i) [Mono m], m ≠ 0 → ∃ (k : f i ⟶ Y), k ≠ 0 :=
    fun i => hlift (hendo i)
  have ⟨hsimp, hnoniso⟩ := idempotent_summands_simple_and_noniso hss e hcoi
    f ι_hom π_hom hretract hsplit hne hendo hlift_i
  exact ⟨n, f, hbp, hsimp, hnoniso, hiso⟩

end TensorCategories

namespace TensorCategories

/--
[indecomposable_of_endoIsIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma indecomposable_of_endoIsIso
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [HasBinaryBiproducts C]
  {X : C}
-- given
  (hne : ¬IsZero X)
  (hendo : ∀ (g : X ⟶ X), g ≠ 0 → IsIso g) :
-- imply
  Indecomposable X := by
-- proof
  refine ⟨hne, fun Y Z φ => ?_⟩
  let e : X ⟶ X := φ.hom ≫ biprod.fst ≫ biprod.inl ≫ φ.inv
  have he_idem : e ≫ e = e := by
    simp only [e, assoc]
    congr 1; congr 1
    simp [Iso.inv_hom_id_assoc]
  by_cases he0 : e = 0
  ·
    left; rw [IsZero.iff_id_eq_zero]
    have h1 : (biprod.fst : Y ⊞ Z ⟶ Y) ≫ (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
      simp only [e] at he0
      have step1 := congr_arg (φ.inv ≫ ·) he0
      simp only [comp_zero, Iso.inv_hom_id_assoc] at step1
      have step2 := congr_arg (· ≫ φ.hom) step1
      simp only [zero_comp, assoc, Iso.inv_hom_id, comp_id] at step2
      exact step2
    have h2 : (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
      have := congr_arg ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ ·) h1
      simp at this; exact this
    calc 𝟙 Y = (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.fst := by simp
      _ = 0 ≫ biprod.fst := by rw [h2]
      _ = 0 := zero_comp
  ·
    right; haveI : IsIso e := hendo e he0
    have he_id : e = 𝟙 X := by rw [← cancel_mono e, id_comp]; exact he_idem
    rw [IsZero.iff_id_eq_zero]
    have h1 : (biprod.fst : Y ⊞ Z ⟶ Y) ≫ (biprod.inl : Y ⟶ Y ⊞ Z) = 𝟙 (Y ⊞ Z) := by
      simp only [e] at he_id
      have step1 := congr_arg (φ.inv ≫ ·) he_id
      simp only [Iso.inv_hom_id_assoc] at step1
      have step2 := congr_arg (· ≫ φ.hom) step1
      simp only [assoc, Iso.inv_hom_id, comp_id] at step2
      exact step2
    have h2 : (biprod.snd : Y ⊞ Z ⟶ Z) = 0 := by
      have := congr_arg (· ≫ (biprod.snd : Y ⊞ Z ⟶ Z)) h1
      simp at this; exact this.symm
    calc 𝟙 Z = (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.snd := by simp
      _ = biprod.inr ≫ 0 := by rw [h2]
      _ = 0 := comp_zero

end TensorCategories

namespace TensorCategories

/--
[unit_indecomposable_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma unit_indecomposable_decomposition
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
-- given
  (hss : IsSemisimpleRing (End (𝟙_ C))) :
-- imply
  ∃ (n : ℕ) (f : Fin n → C) (hbp : HasBiproduct f), (∀ i, Indecomposable (f i)) ∧ (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) ∧ Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp) := by
-- proof
  obtain ⟨n, e, hcoi, hne, hendo_axiom⟩ := primitive_idempotent_endoIsIso hss
  obtain ⟨f, ι_hom, π_hom, hretract, hsplit, hbp, hiso⟩ :=
    biproduct_from_completeOrthogonalIdempotents e hcoi
  have hendo : ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g :=
    hendo_axiom f ι_hom π_hom hretract hsplit
  have hne_fi : ∀ i, ¬ IsZero (f i) := by
    intro i hZ
    apply hne i
    have h_id : 𝟙 (f i) = 0 := (IsZero.iff_id_eq_zero _).mp hZ
    calc (e i : 𝟙_ C ⟶ 𝟙_ C) = π_hom i ≫ ι_hom i := (hsplit i).symm
      _ = π_hom i ≫ (𝟙 (f i) ≫ ι_hom i) := by rw [id_comp]
      _ = π_hom i ≫ (0 ≫ ι_hom i) := by rw [h_id]
      _ = 0 := by simp
  haveI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have hindec : ∀ i, Indecomposable (f i) :=
    fun i => indecomposable_of_endoIsIso (hne_fi i) (hendo i)
  have hnoniso : ∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j) := by
    intro i j hij ⟨φ⟩
    have h1 : φ.hom = 0 :=
      hom_eq_zero_of_orthogonal_idempotent_summands e hcoi f ι_hom π_hom hretract hsplit hij φ.hom
    have h2 : 𝟙 (f i) = 0 := by rw [← φ.hom_inv_id, h1, zero_comp]
    exact (hne_fi i) ((IsZero.iff_id_eq_zero (f i)).mpr h2)
  exact ⟨n, f, hbp, hindec, hnoniso, hiso⟩

end TensorCategories

namespace TensorCategories

/--
[hlift_for_retract_of_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma hlift_for_retract_of_unit
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  [IsArtinianObject (𝟙_ C)]
  {X : C}
  {ι : X ⟶ 𝟙_ C}
  {π : 𝟙_ C ⟶ X}
  {Y : C}
  {m : Y ⟶ X}
  [Mono m]
-- given
  (hret : ι ≫ π = 𝟙 X)
  (_hendo : ∀ (g : X ⟶ X), g ≠ 0 → IsIso g)
  (hm : m ≠ 0) :
-- imply
  ∃ (k : X ⟶ Y), k ≠ 0 := by
-- proof
  haveI : Mono ι := by
    constructor; intro Z a b hab
    have : a ≫ ι ≫ π = b ≫ ι ≫ π := by rw [← assoc, ← assoc, hab]
    rwa [hret, comp_id, comp_id] at this
  haveI : Mono (m ≫ ι) := mono_comp m ι
  have hmi : m ≫ ι ≠ 0 := by
    intro h; apply hm; rwa [← cancel_mono ι, zero_comp]
  have hY : ¬ IsZero Y := fun hZ => hm (hZ.eq_of_src m 0)
  haveI : IsArtinianObject Y := isArtinianObject_of_mono (m ≫ ι)
  obtain ⟨S, hS, j, hMono_j, hne_j⟩ := exists_simple_subobject Y hY
  haveI := hMono_j; haveI := hS
  have hne_jmi : j ≫ m ≫ ι ≠ 0 := by
    intro h
    apply hne_j
    rwa [← cancel_mono (m ≫ ι), zero_comp]
  haveI : Mono (j ≫ m ≫ ι) := mono_comp j (m ≫ ι)
  obtain ⟨g, hg⟩ := simple_subobj_unit_retraction (j ≫ m ≫ ι) hne_jmi
  refine ⟨ι ≫ g ≫ j, ?_⟩
  intro hk
  apply hg
  set f : 𝟙_ C ⟶ 𝟙_ C := g ≫ j ≫ m ≫ ι with hf_def
  have hι_f : ι ≫ f = 0 := by
    calc ι ≫ f = ι ≫ g ≫ j ≫ m ≫ ι := by simp [hf_def]
      _ = (ι ≫ g ≫ j) ≫ (m ≫ ι) := by simp only [assoc]
      _ = 0 ≫ (m ≫ ι) := by rw [hk]
      _ = 0 := by simp
  set e : 𝟙_ C ⟶ 𝟙_ C := π ≫ ι with he_def
  have he_f : e ≫ f = 0 := by
    calc e ≫ f = (π ≫ ι) ≫ f := rfl
      _ = π ≫ (ι ≫ f) := by rw [assoc]
      _ = π ≫ 0 := by rw [hι_f]
      _ = 0 := by simp
  have hcomm : e ≫ f = f ≫ e := endUnit_comm e f
  have hf_e : f ≫ e = 0 := hcomm ▸ he_f
  have hf_e_eq_f : f ≫ e = f := by
    calc f ≫ e = (g ≫ j ≫ m ≫ ι) ≫ (π ≫ ι) := rfl
      _ = g ≫ j ≫ m ≫ (ι ≫ π) ≫ ι := by simp only [assoc]
      _ = g ≫ j ≫ m ≫ 𝟙 X ≫ ι := by rw [hret]
      _ = g ≫ j ≫ m ≫ ι := by simp
  have hf_zero : f = 0 := by rw [← hf_e_eq_f]; exact hf_e
  rw [hf_def] at hf_zero
  rwa [← cancel_mono (j ≫ m ≫ ι), zero_comp]

end TensorCategories

namespace TensorCategories

/--
[unitIsSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean)
-/
@[path]
lemma unitIsSemisimple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  [RightRigidCategory C]
  [LeftRigidCategory C]
  [MonoidalPreadditive C]
  [IsArtinianRing (End (𝟙_ C))]
  [IsArtinianObject (𝟙_ C)] :
-- imply
  UnitIsSemisimple C where semisimple := by
-- proof
  have hss := endUnit_isSemisimpleRing (C := C)
  obtain ⟨n, e, hcoi, hne, hendo_axiom⟩ := primitive_idempotent_endoIsIso hss
  obtain ⟨f, ι_hom, π_hom, hretract, hsplit, hbp, hiso⟩ :=
    biproduct_from_completeOrthogonalIdempotents e hcoi
  have hendo : ∀ i, ∀ (g : f i ⟶ f i), g ≠ 0 → IsIso g :=
    hendo_axiom f ι_hom π_hom hretract hsplit
  have hlift_i : ∀ i, ∀ {Y : C} (m : Y ⟶ f i) [Mono m], m ≠ 0 → ∃ (k : f i ⟶ Y), k ≠ 0 :=
    fun i => hlift_for_retract_of_unit (ι_hom i) (π_hom i) (hretract i) (hendo i)
  have ⟨hsimp, hnoniso⟩ := idempotent_summands_simple_and_noniso hss e hcoi
    f ι_hom π_hom hretract hsplit hne hendo hlift_i
  exact ⟨n, f, hbp, hsimp, hnoniso, hiso⟩
end DualUnit
end TensorCategories
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits
universe u' v'



-- created on 2026-10-23
