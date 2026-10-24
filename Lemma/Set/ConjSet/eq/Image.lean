import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
open Set Topology Filter


/--
[conjSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma conjSet_eq
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {g : G}
  {S : Set G} :
-- imply
  conjSet g S = (fun x => g * x * g⁻¹) '' S :=
-- proof
  rfl

/--
[isCompact_conjSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma isCompact_conjSet
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {g : G}
  {S : Set G}
-- given
  (hS : IsCompact S) :
-- imply
  IsCompact (conjSet g S) :=
-- proof
  (conjHomeomorph g).isCompact_image.mpr hS

/--
[isOpen_conjSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma isOpen_conjSet
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {g : G}
  {S : Set G}
-- given
  (hS : IsOpen S) :
-- imply
  IsOpen (conjSet g S) :=
-- proof
  (conjHomeomorph g).isOpenMap _ hS

/--
[isClosed_conjSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma isClosed_conjSet
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {g : G}
  {S : Set G}
-- given
  (hS : IsClosed S) :
-- imply
  IsClosed (conjSet g S) :=
-- proof
  (conjHomeomorph g).isClosedMap _ hS
end OpenImpliesClosed
section BuildingFixer

/--
[one_mem_pointwiseFixer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma one_mem_pointwiseFixer
  [Group G]
  {act : G → X → X}
  {Y : Set X}
-- given
  (hact_one : ∀ x : X, act 1 x = x) :
-- imply
  (1 : G) ∈ pointwiseFixer act Y :=
-- proof
  fun y _ => hact_one y

/--
[inv_mem_pointwiseFixer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma inv_mem_pointwiseFixer
  [Group G]
  {act : G → X → X}
  {Y : Set X}
  {g : G}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hact_one : ∀ x : X, act 1 x = x)
  (hg : g ∈ pointwiseFixer act Y) :
-- imply
  g⁻¹ ∈ pointwiseFixer act Y := by
-- proof
  intro y hy
  calc act g⁻¹ y = act g⁻¹ (act g y) := by rw [hg y hy]
    _ = act (g⁻¹ * g) y := by rw [← hact_mul]
    _ = act 1 y := by rw [inv_mul_cancel]
    _ = y := hact_one y

/--
[pointwiseFixer_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma pointwiseFixer_iUnion
  {act : G → X → X}
  {C : ι → Set X} :
-- imply
  pointwiseFixer act (⋃ i, C i) = ⋂ i, pointwiseFixer act (C i) := by
-- proof
  ext g
  simp only [pointwiseFixer, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro h i y hy; exact h y ⟨i, hy⟩
  · intro h y ⟨i, hy⟩; exact h i y hy

/--
[pointwiseFixer_image_eq_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma pointwiseFixer_image_eq_conj
  [Group G]
  {act : G → X → X}
  {C₀ : Set X}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hact_one : ∀ x : X, act 1 x = x)
  (h : G) :
-- imply
  pointwiseFixer act (act h '' C₀) = (fun b => h * b * h⁻¹) '' (pointwiseFixer act C₀) := by
-- proof
  ext g
  simp only [pointwiseFixer, Set.mem_setOf_eq, Set.mem_image]
  constructor
  ·
    intro hg
    refine ⟨h⁻¹ * g * h, fun y hy => ?_, by group⟩
    have := hg (act h y) ⟨y, hy, rfl⟩
    rw [show h⁻¹ * g * h = h⁻¹ * (g * h) from by group, hact_mul, hact_mul, this]
    rw [← hact_mul, inv_mul_cancel, hact_one]
  ·
    intro ⟨b, hb, hg_eq⟩
    subst hg_eq
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst hxy
    rw [show h * b * h⁻¹ = h * (b * h⁻¹) from by group, hact_mul, hact_mul]
    rw [← hact_mul h⁻¹ h, inv_mul_cancel, hact_one, hb x hx]
end BuildingFixer
section PointwiseFixer

/--
[pointwise_fixer_compact_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma pointwise_fixer_compact_open
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {B : Subgroup G}
  {act : G → X → X}
  {C₀ : Set X}
  {Y : Set X}
  {n : ℕ}
  {chambers : Fin n → Set X}
-- given
  (hB_compact : IsCompact (B : Set G))
  (hB_open : IsOpen (B : Set G))
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hact_one : ∀ x : X, act 1 x = x)
  (hB_fixer : (B : Set G) = pointwiseFixer act C₀)
  (IsChamber : Set X → Prop)
  (hY_contains_chamber : ∃ C, IsChamber C ∧ C ⊆ Y)
  (hn : 0 < n)
  (chambers_cover_Y : Y ⊆ ⋃ i, chambers i)
  (fixer_covers_chambers : ∀ g ∈ pointwiseFixer act Y, ∀ (i : Fin n) (x : X), x ∈ chambers i → act g x = x)
  (chamber_transit : ∀ i, ∃ h : G, chambers i = act h '' C₀) :
-- imply
  IsOpen (pointwiseFixer act Y) ∧ IsCompact (pointwiseFixer act Y) := by
-- proof
  have hY_fixer_eq : pointwiseFixer act Y =
    pointwiseFixer act (⋃ i, chambers i) := by
    ext g; constructor
    · intro hg x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact fixer_covers_chambers g hg i x hi
    · intro hg y hy
      exact hg y (chambers_cover_Y hy)
  choose h_conj h_transit using chamber_transit
  have key : pointwiseFixer act Y =
    ⋂ (i : Fin n), conjSet (h_conj i) (B : Set G) := by
    rw [hY_fixer_eq, pointwiseFixer_iUnion]
    congr 1; ext i
    rw [h_transit i, pointwiseFixer_image_eq_conj act hact_mul hact_one,
      hB_fixer, conjSet_eq]
  rw [key]
  constructor
  ·
    exact isOpen_iInter_of_finite (fun i => isOpen_conjSet (h_conj i) _ hB_open)
  ·
    have hB_closed : IsClosed (B : Set G) := Subgroup.isClosed_of_isOpen B hB_open
    apply IsCompact.of_isClosed_subset
      (isCompact_conjSet (h_conj (⟨0, hn⟩ : Fin n)) _ hB_compact)
    · exact isClosed_iInter (fun i => isClosed_conjSet (h_conj i) _ hB_closed)
    · exact Set.iInter_subset _ (⟨0, hn⟩ : Fin n)
end PointwiseFixer
section ClusterPoint

/--
[compact_subgroup_cluster_point](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma compact_subgroup_cluster_point
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {B : Subgroup G}
  {u : ℕ → G}
-- given
  (hB_compact : IsCompact (B : Set G))
  (hu : ∀ i, u i ∈ B) :
-- imply
  ∃ β ∈ (B : Set G), MapClusterPt β atTop u := by
-- proof
  apply hB_compact.exists_mapClusterPt
  rw [le_principal_iff, mem_map]
  exact univ_mem' hu

/--
[mapClusterPt_frequently_in_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma mapClusterPt_frequently_in_nhds
  [TopologicalSpace G]
  {β : G}
  {u : ℕ → G}
  {V : Set G}
  {N : ℕ}
-- given
  (hβ : MapClusterPt β atTop u)
  (hV : V ∈ nhds β) :
-- imply
  ∃ i ≥ N, u i ∈ V := by
-- proof
  have h1 : ∃ᶠ y in map u atTop, y ∈ V := hβ.frequently hV
  rw [frequently_map] at h1
  exact h1.forall_exists_of_atTop N
end ClusterPoint
section FixerCoset

/--
[act_eq_of_mul_fixer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma act_eq_of_mul_fixer
  [Group G]
  {act : G → X → X}
  {bⱼ f : G}
  {Y : Set X}
  {x : X}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hf : f ∈ pointwiseFixer act Y)
  (hx : x ∈ Y) :
-- imply
  act (bⱼ * f) x = act bⱼ x := by
-- proof
  rw [hact_mul, hf x hx]

/--
[image_sub_from_fixer_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma image_sub_from_fixer_chain
  [Group G]
  {act : G → X → X}
  {Y : ℕ → Set X}
  {A₀ : Set X}
  {b : ℕ → G}
  {g : G}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hb_maps : ∀ i j, i ≤ j → ∀ x ∈ Y i, act (b j) x ∈ A₀)
  (hg_coset : ∀ i, ∃ j ≥ i, ∃ f ∈ pointwiseFixer act (Y i), g = b j * f) :
-- imply
  ∀ x ∈ ⋃ i, Y i, act g x ∈ A₀ := by
-- proof
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj, f, hf, hg_eq⟩ := hg_coset i
  rw [hg_eq, act_eq_of_mul_fixer act hact_mul (b j) f hf hi]
  exact hb_maps i j hj x hi
end FixerCoset
section StrongTransitivityTheorem

/--
[maximally_strong_transitivity_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma maximally_strong_transitivity_core
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {B : Subgroup G}
  {act : G → X → X}
  {A₀ : Set X}
  {C₀ : Set X}
  {A' : Set X}
  {Y : ℕ → Set X}
  {A_chain : ℕ → Set X}
  {b : ℕ → G}
-- given
  (hB_compact : IsCompact (B : Set G))
  (hB_open : IsOpen (B : Set G))
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hact_one : ∀ x : X, act 1 x = x)
  (hC₀_sub : C₀ ⊆ A₀)
  (hB_fixer : (B : Set G) = pointwiseFixer act C₀)
  (hC₀_in_A' : C₀ ⊆ A')
  (hY_mono : ∀ i, Y i ⊆ Y (i + 1))
  (hC₀_in_Y : C₀ ⊆ Y 0)
  (hY_union : A' = ⋃ i, Y i)
  (hY_in_A : ∀ i, Y i ⊆ A_chain i)
  (hb : ∀ i, b i ∈ B)
  (hb_maps_apt : ∀ i, ∀ x ∈ A_chain i, act (b i) x ∈ A₀)
  (hY_in_Aj : ∀ i j, i ≤ j → Y i ⊆ A_chain j)
  (hF_open : ∀ i, IsOpen (pointwiseFixer act (Y i)))
  (hapt_surj : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) → (fun x => act g x) '' A' = A₀) :
-- imply
  ∃ g : G, g ∈ (B : Set G) ∧ (fun x => act g x) '' A' = A₀ := by
-- proof
  have hF_one : ∀ i, (1 : G) ∈ pointwiseFixer act (Y i) :=
    fun i => one_mem_pointwiseFixer act hact_one (Y i)
  have hF_inv : ∀ i x, x ∈ pointwiseFixer act (Y i) → x⁻¹ ∈ pointwiseFixer act (Y i) :=
    fun i x hx => inv_mem_pointwiseFixer act hact_mul hact_one hx
  have hb_maps : ∀ i j, i ≤ j → ∀ x ∈ Y i, act (b j) x ∈ A₀ :=
    fun i j hij x hx => hb_maps_apt j x (hY_in_Aj i j hij hx)
  have hseq : ∀ i, (b 0)⁻¹ * b i ∈ B := fun i => B.mul_mem (B.inv_mem (hb 0)) (hb i)
  obtain ⟨β, hβ_mem, hβ_cluster⟩ := compact_subgroup_cluster_point B hB_compact
    (fun i => (b 0)⁻¹ * b i) hseq
  set g := b 0 * β with hg_def
  have hg_mem : g ∈ (B : Set G) := B.mul_mem (hb 0) hβ_mem
  have hg_coset : ∀ i, ∃ j ≥ i, ∃ f ∈ pointwiseFixer act (Y i), g = b j * f := by
    intro i
    have hU_open : IsOpen ((fun x => β * x) '' (pointwiseFixer act (Y i))) :=
      (Homeomorph.mulLeft β).isOpenMap _ (hF_open i)
    have hU_nhds : (fun x => β * x) '' (pointwiseFixer act (Y i)) ∈ nhds β :=
      hU_open.mem_nhds ⟨1, hF_one i, by simp⟩
    obtain ⟨j, hj, u, hu_mem, hu_eq⟩ :=
      mapClusterPt_frequently_in_nhds hβ_cluster hU_nhds i
    refine ⟨j, hj, u⁻¹, hF_inv i u hu_mem, ?_⟩
    show b 0 * β = b j * u⁻¹
    have h1 : β * u = (b 0)⁻¹ * b j := by exact_mod_cast hu_eq
    have h2 : b 0 * (β * u) = b j := by rw [h1]; group
    calc b 0 * β = b 0 * (β * u) * u⁻¹ := by group
      _ = b j * u⁻¹ := by rw [h2]
  have hg_maps : ∀ x ∈ A', act g x ∈ A₀ := by
    rw [hY_union]
    exact image_sub_from_fixer_chain act hact_mul hb_maps hg_coset
  exact ⟨g, hg_mem, hapt_surj g hg_maps⟩

/--
[maximally_strong_transitivity_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma maximally_strong_transitivity_theorem
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {Δ : ThickBuildingData G X} :
-- imply
  ∀ A' ∈ Δ.maxAptSystem, ∀ C', Δ.IsChamber C' → C' ⊆ A' → ∃ g : G, (fun x => Δ.act g x) '' C' = Δ.C₀ ∧ (fun x => Δ.act g x) '' A' = Δ.A₀ := by
-- proof
  intro A' hA' C' hC'_chamber hC'_sub
  obtain ⟨h, hh_eq⟩ := Δ.chamber_transitive C' hC'_chamber
  set A'' := (fun x => Δ.act h⁻¹ x) '' A' with hA''_def
  have hA''_max : A'' ∈ Δ.maxAptSystem :=
    Δ.maxAptSystem_invariant h⁻¹ A' hA'
  have hC₀_sub_A'' : Δ.C₀ ⊆ A'' := by
    intro c hc
    have hc_in_C' : Δ.act h c ∈ C' := by rw [← hh_eq]; exact ⟨c, hc, rfl⟩
    exact ⟨Δ.act h c, hC'_sub hc_in_C', by show Δ.act h⁻¹ (Δ.act h c) = c; rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]⟩
  obtain ⟨Y, hY_mono, hC₀_in_Y, hY_union, A_chain, hY_in_A, b, hb, hb_maps,
    hY_in_Aj, hF_open, hapt_surj, _⟩ :=
    Δ.exhaustion_data A'' hA''_max hC₀_sub_A''
  obtain ⟨g₀, hg₀_mem, hg₀_img⟩ := maximally_strong_transitivity_core
    Δ.B Δ.B_compact Δ.B_open Δ.act Δ.act_mul Δ.act_one Δ.A₀ Δ.C₀
    Δ.chamber_sub_apt Δ.B_eq_fixer A'' hC₀_sub_A''
    Y hY_mono hC₀_in_Y hY_union A_chain hY_in_A b hb hb_maps hY_in_Aj
    hF_open hapt_surj
  refine ⟨g₀ * h⁻¹, ?_, ?_⟩
  ·
    ext x; simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Δ.act_mul]
      have hy_in_C' := hy
      obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Δ.C₀, Δ.act h c = y := by
        rw [← hh_eq] at hy_in_C'; exact hy_in_C'
      have hinv : Δ.act h⁻¹ (Δ.act h c) = c := by
        rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]
      rw [hinv]
      have hg₀_fixes : g₀ ∈ pointwiseFixer Δ.act Δ.C₀ := by
        rw [← Δ.B_eq_fixer]; exact hg₀_mem
      rw [hg₀_fixes c hc]; exact hc
    · intro hx
      have hg₀_fixes : g₀ ∈ pointwiseFixer Δ.act Δ.C₀ := by
        rw [← Δ.B_eq_fixer]; exact hg₀_mem
      refine ⟨Δ.act h x, ?_, ?_⟩
      · rw [← hh_eq]; exact ⟨x, hx, rfl⟩
      · simp only [Δ.act_mul]
        have hinv : Δ.act h⁻¹ (Δ.act h x) = x := by
          rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]
        rw [hinv, hg₀_fixes x hx]
  ·
    rw [show (fun x => Δ.act (g₀ * h⁻¹) x) '' A' =
      (fun x => Δ.act g₀ x) '' ((fun x => Δ.act h⁻¹ x) '' A') from by
      ext x; simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Δ.act h⁻¹ y, ⟨y, hy, rfl⟩, by simp only [Δ.act_mul]⟩
      · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by simp only [Δ.act_mul]⟩]
    exact hg₀_img
end StrongTransitivityTheorem
section AscendingChain

/--
[ascending_chain_fixer_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma ascending_chain_fixer_property
  [Group G]
  {act : G → Apt → Apt}
  {A₀ : Apt}
  {A : ℕ → Apt}
  {b : ℕ → G}
  {i j : ℕ}
-- given
  (hact_mul : ∀ g₁ g₂ a, act (g₁ * g₂) a = act g₁ (act g₂ a))
  (hact_one : ∀ a, act 1 a = a)
  (hb_map : ∀ i, act (b i) (A i) = A₀)
  (hij : i ≤ j) :
-- imply
  act ((b i)⁻¹ * b j) (A j) = A i := by
-- proof
  rw [hact_mul, hb_map j]
  rw [show A₀ = act (b i) (A i) from (hb_map i).symm]
  rw [← hact_mul]
  simp [inv_mul_cancel, hact_one]
end AscendingChain
section MaximalCorollary

/--
[preimage_of_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean)
-/
@[path]
lemma preimage_of_image_eq
  [Group G]
  {act : G → X → X}
  {g : G}
  {A A₀ : Set X}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
  (hact_one : ∀ x : X, act 1 x = x)
  (hg : (fun x => act g x) '' A = A₀) :
-- imply
  A = (fun x => act g⁻¹ x) '' A₀ := by
-- proof
  rw [← hg]; ext x; simp only [Set.mem_image]
  constructor
  · intro hx
    exact ⟨act g x, ⟨x, hx, rfl⟩, by
      show act g⁻¹ (act g x) = x
      rw [← hact_mul, inv_mul_cancel, hact_one]⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
    have : x = z := by
      have h : act g⁻¹ (act g z) = x := hyx
      rw [← hact_mul, inv_mul_cancel, hact_one] at h; exact h.symm
    rwa [this]
/-- Strong transitivity on apartments: every apartment of the maximal system
is $G$-translated to the base apartment $A_0$. -/
end MaximalCorollary


-- created on 2026-10-23
