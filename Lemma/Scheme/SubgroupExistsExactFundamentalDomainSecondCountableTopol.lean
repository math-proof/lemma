import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_isOpen_one_mem_mul_inv_subset {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Set G} (hVopen : IsOpen V) (hV1 : (1 : G) ∈ V) : ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V := by
  have hcont : Continuous fun p : G × G => p.1 * p.2⁻¹ := continuous_fst.mul continuous_snd.inv
  have hopen : IsOpen ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V) := hVopen.preimage hcont
  have hmem : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V := by
    simpa using hV1
  obtain ⟨u, v, huopen, hvopen, hu1, hv1, huv⟩ := isOpen_prod_iff.mp hopen 1 1 hmem
  refine ⟨u ∩ v, huopen.inter hvopen, ⟨hu1, hv1⟩, ?_⟩
  intro x hx y hy
  have hxy : (x, y) ∈ u ×ˢ v := ⟨hx.1, hy.2⟩
  refine huv hxy

private def rightTranslate {G : Type u} [Group G] (W : Set G) (h : G) : Set G :=
  (fun g : G => g * h⁻¹) ⁻¹' W

private lemma mem_rightTranslate_iff {G : Type u} [Group G] {W : Set G} {h x : G} : x ∈ rightTranslate W h ↔ x * h⁻¹ ∈ W := Iff.rfl

private lemma isOpen_rightTranslate {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W : Set G} (hW : IsOpen W) (h : G) : IsOpen (rightTranslate W h) :=
  hW.preimage (continuous_mul_const h⁻¹)

private lemma self_mem_rightTranslate {G : Type u} [Group G] {W : Set G} (hW1 : (1 : G) ∈ W) (h : G) : h ∈ rightTranslate W h := by
  show h * h⁻¹ ∈ W
  rwa [mul_inv_cancel]

private lemma iUnion_rightTranslate {G : Type u} [Group G] {W : Set G} (hW1 : (1 : G) ∈ W) : ⋃ h : G, rightTranslate W h = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, self_mem_rightTranslate hW1 x⟩

private lemma eq_of_mul_mem_rightTranslate {G : Type u} [Group G] {Γ : Subgroup G} {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1}) (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {h z : G} {γ δ : ↥Γ} (hγ : (γ : G) * z ∈ rightTranslate W h) (hδ : (δ : G) * z ∈ rightTranslate W h) : γ = δ := by
  have hγW : ((γ : G) * z) * h⁻¹ ∈ W := hγ
  have hδW : ((δ : G) * z) * h⁻¹ ∈ W := hδ
  have hkey : (((γ : G) * z) * h⁻¹) * (((δ : G) * z) * h⁻¹)⁻¹ ∈ V := hWV _ hγW _ hδW
  have hsimp : (((γ : G) * z) * h⁻¹) * (((δ : G) * z) * h⁻¹)⁻¹ = (γ : G) * (δ : G)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [hsimp] at hkey
  have hmemΓ : (γ : G) * (δ : G)⁻¹ ∈ Γ := mul_mem γ.2 (inv_mem δ.2)
  have hone : (γ : G) * (δ : G)⁻¹ ∈ V ∩ (Γ : Set G) := ⟨hkey, hmemΓ⟩
  rw [hVΓ, Set.mem_singleton_iff, mul_inv_eq_one] at hone
  refine Subtype.ext hone

private def orbitMeets {G : Type u} [Group G] (Γ : Subgroup G) (S : Set G) : Set G :=
  {x : G | ∃ γ : ↥Γ, (γ : G) * x ∈ S}

private lemma mem_orbitMeets_iff {G : Type u} [Group G] {Γ : Subgroup G} {S : Set G} {x : G} : x ∈ orbitMeets Γ S ↔ ∃ γ : ↥Γ, (γ : G) * x ∈ S := Iff.rfl

private lemma subset_orbitMeets {G : Type u} [Group G] (Γ : Subgroup G) (S : Set G) : S ⊆ orbitMeets Γ S :=
  fun x hx => ⟨1, by simpa using hx⟩

private lemma isOpen_orbitMeets {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {S : Set G} (hS : IsOpen S) : IsOpen (orbitMeets Γ S) := by
  have hrw : orbitMeets Γ S = ⋃ γ : ↥Γ, (fun x : G => (γ : G) * x) ⁻¹' S := by
    ext x
    simp only [orbitMeets, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [hrw]
  refine isOpen_iUnion fun γ => hS.preimage (continuous_const_mul _)

private lemma coe_mul_mem_orbitMeets_iff {G : Type u} [Group G] {Γ : Subgroup G} {S : Set G} (δ : ↥Γ) {x : G} : (δ : G) * x ∈ orbitMeets Γ S ↔ x ∈ orbitMeets Γ S := by
  constructor
  ·
    intro h
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ * δ, by simpa [mul_assoc] using hγ⟩
  ·
    intro h
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ * δ⁻¹, by simpa [mul_assoc] using hγ⟩

private def fdPiece {G : Type u} [Group G] (Γ : Subgroup G) (W : Set G) (e : ℕ → G) (n : ℕ) : Set G :=
  rightTranslate W (e n) \ ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m))

private def fdUnion {G : Type u} [Group G] (Γ : Subgroup G) (W : Set G) (e : ℕ → G) : Set G :=
  ⋃ n, fdPiece Γ W e n

private lemma mem_fdPiece_iff {G : Type u} [Group G] {Γ : Subgroup G} {W : Set G} {e : ℕ → G} {n : ℕ} {x : G} : x ∈ fdPiece Γ W e n ↔ x ∈ rightTranslate W (e n) ∧ x ∉ ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m)) := Iff.rfl

private lemma mem_fdUnion_iff {G : Type u} [Group G] {Γ : Subgroup G} {W : Set G} {e : ℕ → G} {x : G} : x ∈ fdUnion Γ W e ↔ ∃ n, x ∈ fdPiece Γ W e n := Set.mem_iUnion

private lemma not_mem_orbitMeets_of_mem_fdPiece {G : Type u} [Group G] {Γ : Subgroup G} {W : Set G} {e : ℕ → G} {m n : ℕ} (hmn : m < n) {x : G} (hx : x ∈ fdPiece Γ W e n) : x ∉ orbitMeets Γ (rightTranslate W (e m)) :=
  fun hcon => (mem_fdPiece_iff.mp hx).2 (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmn, hcon⟩⟩)

private lemma exists_coe_mul_mem_fdUnion {G : Type u} [Group G] {Γ : Subgroup G} {W : Set G} {e : ℕ → G} (hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n)) (x : G) : ∃ γ : ↥Γ, (γ : G) * x ∈ fdUnion Γ W e := by
  set N : Set ℕ := {n : ℕ | x ∈ orbitMeets Γ (rightTranslate W (e n))} with hN
  have hNne : N.Nonempty := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, subset_orbitMeets Γ _ hn⟩
  have hmin : x ∈ orbitMeets Γ (rightTranslate W (e (sInf N))) := Nat.sInf_mem hNne
  obtain ⟨γ₀, hγ₀⟩ := hmin
  refine ⟨γ₀, mem_fdUnion_iff.mpr ⟨sInf N, mem_fdPiece_iff.mpr ⟨hγ₀, ?_⟩⟩⟩
  intro hcon
  rw [Set.mem_iUnion] at hcon
  obtain ⟨m, hm⟩ := hcon
  rw [Set.mem_iUnion] at hm
  obtain ⟨hmlt, hmem⟩ := hm
  have hxm : x ∈ orbitMeets Γ (rightTranslate W (e m)) := (coe_mul_mem_orbitMeets_iff γ₀).mp hmem
  have hle : sInf N ≤ m := Nat.sInf_le hxm
  omega

private lemma eq_of_coe_mul_mem_fdUnion {G : Type u} [Group G] {Γ : Subgroup G} {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1}) (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {e : ℕ → G} {x : G} {γ δ : ↥Γ} (hγ : (γ : G) * x ∈ fdUnion Γ W e) (hδ : (δ : G) * x ∈ fdUnion Γ W e) : γ = δ := by
  obtain ⟨n, hγn⟩ := mem_fdUnion_iff.mp hγ
  obtain ⟨m, hδm⟩ := mem_fdUnion_iff.mp hδ
  have hstrict : ∀ (σ τ : ↥Γ) (i j : ℕ), i < j → (σ : G) * x ∈ fdPiece Γ W e i → (τ : G) * x ∈ fdPiece Γ W e j → False := by
    intro σ τ i j hij hσ hτ
    refine not_mem_orbitMeets_of_mem_fdPiece hij hτ ?_
    refine (coe_mul_mem_orbitMeets_iff τ).mpr ?_
    exact ⟨σ, (mem_fdPiece_iff.mp hσ).1⟩
  obtain hlt | hrest := lt_trichotomy n m
  · refine (hstrict γ δ n m hlt hγn hδm).elim
  ·
    obtain heq | hgt := hrest
    ·
      subst heq
      refine eq_of_mul_mem_rightTranslate hVΓ hWV (mem_fdPiece_iff.mp hγn).1 (mem_fdPiece_iff.mp hδm).1
    · refine (hstrict δ γ m n hgt hδm hγn).elim

private lemma existsUnique_coe_mul_mem_fdUnion {G : Type u} [Group G] {Γ : Subgroup G} {V W : Set G} (hVΓ : V ∩ (Γ : Set G) = {1}) (hWV : ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ V) {e : ℕ → G} (hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n)) (x : G) : ∃! γ : ↥Γ, (γ : G) * x ∈ fdUnion Γ W e := by
  obtain ⟨γ₀, hγ₀⟩ := exists_coe_mul_mem_fdUnion hcover x
  exact ⟨γ₀, hγ₀, fun δ hδ => eq_of_coe_mul_mem_fdUnion hVΓ hWV hδ hγ₀⟩

private lemma exists_exact_fundamental_domain {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) (hsc : SecondCountableTopology G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) : ∃ F : Set G, (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧ ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by
  obtain ⟨V, hVopen, hVΓ⟩ := hdisc
  have hV1 : (1 : G) ∈ V := by
    have h1 : (1 : G) ∈ V ∩ (Γ : Set G) := by
      rw [hVΓ]
      rfl
    refine h1.1
  obtain ⟨W, hWopen, hW1, hWV⟩ := exists_isOpen_one_mem_mul_inv_subset hVopen hV1
  let _ := hsc
  obtain ⟨T, hTc, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable (fun h : G => rightTranslate W h) (fun h => isOpen_rightTranslate hWopen h)
  have hmemT : ∀ y : G, y ∈ ⋃ h ∈ T, rightTranslate W h := by
    intro y
    have hy : y ∈ ⋃ h : G, rightTranslate W h := Set.mem_iUnion.mpr ⟨y, self_mem_rightTranslate hW1 y⟩
    refine (Set.ext_iff.mp hTcover y).mpr hy
  have hTne : T.Nonempty := by
    obtain hTe | hTne := Set.eq_empty_or_nonempty T
    ·
      exfalso
      have h1 := hmemT 1
      rw [hTe] at h1
      simp at h1
    · refine hTne
  obtain ⟨e, hTeq⟩ := hTc.exists_eq_range hTne
  have hcover : ∀ y : G, ∃ n : ℕ, y ∈ rightTranslate W (e n) := by
    intro y
    have hy := hmemT y
    rw [hTeq, Set.biUnion_range] at hy
    exact Set.mem_iUnion.mp hy
  refine ⟨fdUnion Γ W e, ⟨fun n => rightTranslate W (e n), fun n => ⋃ m, ⋃ (_ : m < n), orbitMeets Γ (rightTranslate W (e m)), fun n => isOpen_rightTranslate hWopen (e n), fun n => isOpen_iUnion fun m => isOpen_iUnion fun _ => isOpen_orbitMeets (isOpen_rightTranslate hWopen (e m)), rfl⟩, fun x => existsUnique_coe_mul_mem_fdUnion hVΓ hWV hcover x⟩

/--
[Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology.lean)
-/
@[path]
private lemma main
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  (Γ : Subgroup G)
  -- given
  (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
  -- imply
  ∃ F : Set G,
    (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F :=
    exists_exact_fundamental_domain Γ inferInstance hdisc


-- created on 2026-10-20
