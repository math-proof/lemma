import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.LinkBuilding
open SimplicialComplex Building
open scoped Classical


/--
[coxeter_complex_unique_labelling'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
lemma coxeter_complex_unique_labelling'
  {V : Type}
  [DecidableEq V]
  {A : SimplicialComplex V}
  {B_idx : Type}
  {M : CoxeterMatrix B_idx}
  {cc : ChamberComplex V}
  {φ : Finset V → M.Group}
-- given
  (hcc_eq : cc.toSimplicialComplex = A)
  (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
  (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
  (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :
-- imply
  ∀ (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂], ∀ (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂), (∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t) → (∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t) → ∀ C₀, A.IsMaximal C₀ → (∃ (f : L₁ → L₂), Function.Bijective f ∧ lab₂ C₀ = (lab₁ C₀).image f) ∧ (∀ (f : L₁ → L₂), Function.Bijective f → lab₂ C₀ = (lab₁ C₀).image f → ∀ s, s ∈ A.faces → lab₂ s = (lab₁ s).image f) := by
-- proof
  exact coxeter_complex_unique_labelling_axiom A B_idx M cc hcc_eq φ hinj hsurj hadj
namespace Building

/--
[sdiff_union_eq_sdiff_of_disjoint'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma sdiff_union_eq_sdiff_of_disjoint'_eq
  {V : Type}
  [DecidableEq V]
  {σ F τ : Finset V}
-- given
  (_hF_disj : Disjoint σ F)
  (hτ_disj : Disjoint σ τ) :
-- imply
  (σ ∪ τ) \ (σ ∪ F) = τ \ F := by
-- proof
  apply SimplicialComplex.sdiff_union_eq_sdiff_of_disjoint' _hF_disj hτ_disj

/--
[union_maximal_of_linkComplex_maximal'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma union_maximal_of_linkComplex_maximal'_eq
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ_max : (K.linkComplex σ hσ).IsMaximal τ) :
-- imply
  K.IsMaximal (σ ∪ τ) := by
-- proof
  apply SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hτ_max

/--
[linkComplex_maximal_of_union_maximal'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma linkComplex_maximal_of_union_maximal'_eq
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ_link : τ ∈ (K.linkComplex σ hσ).faces)
  (hστ_max : K.IsMaximal (σ ∪ τ)) :
-- imply
  (K.linkComplex σ hσ).IsMaximal τ := by
-- proof
  apply SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hτ_link hστ_max

/--
[linkComplex_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma linkComplex_sub_eq
  {V : Type}
  [DecidableEq V]
  {K A : SimplicialComplex V}
  {σ : Finset V}
-- given
  (hA : IsSubcomplex A K)
  (hσK : σ ∈ K.faces)
  (hσA : σ ∈ A.faces) :
-- imply
  IsSubcomplex (A.linkComplex σ hσA) (K.linkComplex σ hσK) := by
-- proof
  apply SimplicialComplex.linkComplex_sub hA σ hσK hσA

/--
[link_exists_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_exists_maximal_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
-- imply
  ∀ s ∈ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).faces, ∃ C, (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C ∧ s ⊆ C := by
-- proof
  apply link_exists_maximal b σ hσ hσ_proper

/--
[iso_exists_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma iso_exists_injective_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {B : SimplicialComplex V}
  {x : Finset V}
  {C : Finset V}
  {φ : SimplicialMap A B}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hB : B ∈ b.apartmentSystem.apartments)
  (hxA : x ∈ A.faces)
  (hxB : x ∈ B.faces)
  (hC_max : A.IsMaximal C)
  (hCB : C ∈ B.faces)
  (hφ_fix_x : ∀ v ∈ x, φ.toFun v = v)
  (hφ_fix_C : ∀ v ∈ C, φ.toFun v = v) :
-- imply
  ∀ (v₁ v₂ : V), (∃ s ∈ A.faces, v₁ ∈ s) → (∃ s ∈ A.faces, v₂ ∈ s) → φ.toFun v₁ = φ.toFun v₂ → v₁ = v₂ := by
-- proof
  apply iso_exists_injective b A hA B hB x hxA hxB C hC_max hCB φ hφ_fix_x hφ_fix_C

/--
[link_iso_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_iso_exists_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A' ∈ link_apts, ∀ B' ∈ link_apts, ∀ x, x ∈ A'.faces → x ∈ B'.faces → ∀ C, A'.IsMaximal C → C ∈ B'.faces → ∃ φ : SimplicialMap A' B', (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v) := by
-- proof
  apply link_iso_exists b σ hσ hσ_proper link_apts h_link_apts

/--
[link_maximal_in_apt_is_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_maximal_in_apt_is_maximal_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∀ C, A.IsMaximal C → (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C := by
-- proof
  apply link_maximal_in_apt_is_maximal b σ hσ hσ_proper link_apts h_link_apts

/--
[link_gallery_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_gallery_dist_le_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_cc : ChamberComplex V}
  {C D : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_cc : link_cc.toSimplicialComplex = b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ)
  (hC_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C)
  (hD_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D) :
-- imply
  galleryDist link_cc.toSimplicialComplex C D ≤ galleryDist b.toChamberComplex.toSimplicialComplex (σ ∪ C) (σ ∪ D) := by
-- proof
  apply link_gallery_dist_le b σ hσ hσ_proper link_cc h_link_cc C D hC_max hD_max

/--
[link_gallery_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_gallery_convex_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_cc : ChamberComplex V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_cc : link_cc.toSimplicialComplex = b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∀ C D : Finset V, C ∈ A.faces → link_cc.toSimplicialComplex.IsMaximal C → D ∈ A.faces → link_cc.toSimplicialComplex.IsMaximal D → ∀ g : Gallery link_cc.toSimplicialComplex, g.Connects C D → g.length = galleryDist link_cc.toSimplicialComplex C D → ∀ E ∈ g.chambers, E ∈ A.faces := by
-- proof
  apply link_gallery_convex b σ hσ hσ_proper link_cc h_link_cc link_apts h_link_apts

/--
[link_building_maximal_in_apt_is_apt_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_building_maximal_in_apt_is_apt_maximal_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∀ C, C ∈ A.faces → (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C → A.IsMaximal C := by
-- proof
  apply link_building_maximal_in_apt_is_apt_maximal b σ hσ hσ_proper link_apts h_link_apts

/--
[link_apt_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_apt_nonempty_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∃ s, s ∈ A.faces := by
-- proof
  apply link_apt_nonempty b σ hσ hσ_proper link_apts h_link_apts

/--
[link_iso_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_iso_bijective_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∀ A' ∈ link_apts, ∀ C, C ∈ A.faces → C ∈ A'.faces → A.IsMaximal C → ∃ φ : V → V, Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces) := by
-- proof
  apply link_iso_bijective b σ hσ hσ_proper link_apts h_link_apts

/--
[link_of_coxeter_complex_is_coxeter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_of_coxeter_complex_is_coxeter_eq
  {V : Type}
  [DecidableEq V]
  {A : SimplicialComplex V}
  {B_idx : Type}
  {M : CoxeterMatrix B_idx}
  {cc : ChamberComplex V}
  {φ : Finset V → M.Group}
  {σ : Finset V}
-- given
  (hcc_eq : cc.toSimplicialComplex = A)
  (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
  (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
  (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
  (hσ : σ ∈ A.faces)
  (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
-- imply
  ∃ (B_idx' : Type) (M' : CoxeterMatrix B_idx') (cc' : ChamberComplex V), cc'.toSimplicialComplex = A.linkComplex σ hσ ∧ ∃ (φ' : Finset V → M'.Group), (∀ C, (A.linkComplex σ hσ).IsMaximal C → ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧ (∀ w : M'.Group, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧ (∀ C C', (A.linkComplex σ hσ).Adjacent C C' → CoxeterComplex.ChamberAdjacent M' (φ' C) (φ' C')) ∧ cc'.IsThin := by
-- proof
  apply link_of_coxeter_complex_is_coxeter A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper

/--
[link_apt_is_coxeter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_apt_is_coxeter_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA}) :
-- imply
  ∀ A ∈ link_apts, ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ ∃ (φ : Finset V → M.Group), (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧ (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧ (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧ cc.IsThin := by
-- proof
  apply link_apt_is_coxeter b σ hσ hσ_proper link_apts h_link_apts

/--
[link_contains_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_contains_pair_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {link_apts : Set (SimplicialComplex V)}
  {C' D' : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (h_link_apts : link_apts = {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces), L = A.linkComplex σ hσA})
  (hC'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C')
  (hD'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D') :
-- imply
  ∃ A ∈ link_apts, C' ∈ A.faces ∧ D' ∈ A.faces := by
-- proof
  apply Building.link_contains_pair b σ hσ link_apts h_link_apts C' D' hC'_max hD'_max

/--
[link_is_thick](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_is_thick_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces) :
-- imply
  ∀ F' C' : Finset V, (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' C' → (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C' → ∃ D₁ D₂ : Finset V, D₁ ≠ C' ∧ D₂ ≠ C' ∧ D₁ ≠ D₂ ∧ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₁ ∧ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₁ ∧ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₂ ∧ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₂ := by
-- proof
  apply Building.link_is_thick b σ hσ

/--
[link_gallery_connected](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean)
-/
@[path]
private lemma link_gallery_connected_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
-- imply
  ∀ C D, (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C → (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D → ∃ g : Gallery (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ), g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by
-- proof
  apply Building.link_gallery_connected b σ hσ hσ_proper


-- created on 2026-10-23
