import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type (u + 1))} {ι : Type u}

private noncomputable abbrev res {V W : X.Opens} (h : V ≤ W) : (X.presheaf.obj (op W)) →+* (X.presheaf.obj (op V)) := (X.presheaf.map (homOfLE h).op).hom
private lemma res_res {V W Y : X.Opens} (h : V ≤ W) (h' : W ≤ Y) (s : (X.presheaf.obj (op Y))) : res h (res h' s) = res (h.trans h') s := by
  change (X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op) s = _
  rw [← X.presheaf.map_comp]
  rfl
private lemma res_self {V : X.Opens} (s : (X.presheaf.obj (op V))) : res (le_refl V) s = s := by
  change (X.presheaf.map (homOfLE (le_refl V)).op) s = s
  have : (homOfLE (le_refl V)).op = 𝟙 _ := rfl
  rw [this, X.presheaf.map_id]
  rfl
private lemma res_mem_span
  {V W : X.Opens} (h : V ≤ W) {Y : X.Opens} (hW : W ≤ Y) (t : (X.presheaf.obj (op Y))) (s : (X.presheaf.obj (op W)))
  (hs : s ∈ Ideal.span {res hW t}) : res h s ∈ Ideal.span {res (h.trans hW) t} := by
  rw [Ideal.mem_span_singleton'] at hs ⊢
  obtain ⟨a, rfl⟩ := hs
  exact ⟨res h a, by rw [map_mul, res_res]⟩
private noncomputable def LocMem (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (W : X.Opens) (s : (X.presheaf.obj (op W))) (x : X) : Prop :=
  ∃ (V : X.affineOpens) (i : ι) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U i), res hVW s ∈ Ideal.span {res hVU (g i)}
private lemma exists_affine_nhd (U : ι → X.affineOpens) (hU : ⨆ i, (U i : X.Opens) = ⊤) (W : X.Opens) (x : X) (hx : x ∈ W) :
  ∃ (V : X.affineOpens) (i : ι), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ W ∧ (V : X.Opens) ≤ U i := by
  have hx' : x ∈ (⨆ i, (U i : X.Opens)) := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Iff.mp Opens.mem_iSup hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ W ⊓ (U i : X.Opens) from ⟨hx, hi⟩) (W ⊓ U i).2
  exact ⟨⟨V, hV⟩, i, hxV, fun y hy => (hVle hy).1, fun y hy => (hVle hy).2⟩
private lemma LocMem.restrict
  (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) {W : X.Opens} {s : (X.presheaf.obj (op W))} {x : X} (h : LocMem U g W s x)
  (V' : X.affineOpens) (j : ι) (hxV' : x ∈ (V' : X.Opens)) (hV'W : (V' : X.Opens) ≤ W) (hV'U : (V' : X.Opens) ≤ U j)
  (hsmall : ∀ (V : X.affineOpens), x ∈ (V : X.Opens) → ∃ (V'' : X.affineOpens), x ∈ (V'' : X.Opens) ∧ (V'' : X.Opens) ≤ V ∧ (V'' : X.Opens) ≤ V') :
  ∃ (V'' : X.affineOpens) (_ : x ∈ (V'' : X.Opens)) (hle : (V'' : X.Opens) ≤ V'), res (hle.trans hV'W) s ∈ Ideal.span {res (hle.trans hV'U) (g j)} := by
  obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := h
  obtain ⟨V'', hxV'', h1, h2⟩ := hsmall V hxV
  refine ⟨V'', hxV'', h2, ?_⟩
  have hmem' := res_mem_span h1 hVU (g i) _ hmem
  rw [res_res] at hmem'
  rwa [← hcomp i j V'' (h1.trans hVU) (h2.trans hV'U)]
private lemma mul_res_g_injective
  (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors (X.presheaf.obj (op (W : X.Opens)))) (i : ι) (O : X.Opens) (hO : O ≤ U i) (c₁ c₂ : (X.presheaf.obj (op O)))
  (h : c₁ * res hO (g i) = c₂ * res hO (g i)) : c₁ = c₂ := by
  let J := Subtype (fun V : X.affineOpens => (V : X.Opens) ≤ O)
  suffices hcov : O ≤ ⨆ j : J, (j.1 : X.Opens) by
    apply X.sheaf.eq_of_locally_eq' (fun j : J => (j.1 : X.Opens)) O (fun j => homOfLE j.2) hcov
    intro j
    change res j.2 c₁ = res j.2 c₂
    have hj := congrArg (res j.2) h
    rw [map_mul, map_mul, res_res] at hj
    apply Iff.mp (mul_cancel_right_mem_nonZeroDivisors (hg i j.1 (j.2.trans hO))) hj
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
  apply Iff.mpr Opens.mem_iSup ⟨⟨⟨V, hV⟩, hVO⟩, hxV⟩
private lemma mem_span_of_locMem
  (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors (X.presheaf.obj (op (W : X.Opens)))) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) (W₀ : X.Opens) (s : (X.presheaf.obj (op W₀))) (i : ι) (V : X.affineOpens)
  (hVW : (V : X.Opens) ≤ W₀) (hVU : (V : X.Opens) ≤ U i)
  (hloc : ∀ x ∈ (V : X.Opens), LocMem U g W₀ s x) :
  res hVW s ∈ Ideal.span {res hVU (g i)} := by
  classical
  let J := Subtype (fun V' : X.affineOpens => ∃ h : (V' : X.Opens) ≤ V, res (h.trans hVW) s ∈ Ideal.span {res (h.trans hVU) (g i)})
  have hJle : ∀ j : J, (j.1 : X.Opens) ≤ V := fun j => j.2.1
  have hcov : (V : X.Opens) ≤ ⨆ j : J, (j.1 : X.Opens) := by
    intro x hx
    obtain ⟨V'', hxV'', hle, hmem⟩ := (hloc x hx).restrict U g hcomp V i hx hVW hVU (fun V₁ hx₁ => by
      obtain ⟨_, ⟨V₂, hV₂, rfl⟩, hxV₂, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V₁ : X.Opens) ⊓ V from ⟨hx₁, hx⟩) ((V₁ : X.Opens) ⊓ V).2
      exact ⟨⟨V₂, hV₂⟩, hxV₂, fun y hy => (hle hy).1, fun y hy => (hle hy).2⟩)
    exact Iff.mpr Opens.mem_iSup ⟨⟨V'', hle, hmem⟩, hxV''⟩
  have hq : ∀ j : J, ∃ c : (X.presheaf.obj (op (j.1 : X.Opens))), c * res ((hJle j).trans hVU) (g i) = res ((hJle j).trans hVW) s := by
    intro j
    obtain ⟨h, hmem⟩ := j.2
    rwa [Ideal.mem_span_singleton'] at hmem
  choose c hc using hq
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun j : J => (j.1 : X.Opens)) c := by
    intro j k
    apply mul_res_g_injective U g hg i ((j.1 : X.Opens) ⊓ k.1) (inf_le_left.trans ((hJle j).trans hVU))
    have ej := congrArg (res (inf_le_left : (j.1 : X.Opens) ⊓ k.1 ≤ j.1)) (hc j)
    have ek := congrArg (res (inf_le_right : (j.1 : X.Opens) ⊓ k.1 ≤ k.1)) (hc k)
    rw [map_mul, res_res, res_res] at ej ek
    apply ej.trans ek.symm
  obtain ⟨cV', hcV', -⟩ := X.sheaf.existsUnique_gluing' (fun j : J => (j.1 : X.Opens)) V (fun j => homOfLE (hJle j)) hcov c hcompat
  let cV : (X.presheaf.obj (op (V : X.Opens))) := cV'
  have hcV : ∀ j, res (hJle j) cV = c j := hcV'
  rw [Ideal.mem_span_singleton']
  refine ⟨cV, ?_⟩
  apply X.sheaf.eq_of_locally_eq' (fun j : J => (j.1 : X.Opens)) V (fun j => homOfLE (hJle j)) hcov
  intro j
  change res (hJle j) (cV * res hVU (g i)) = res (hJle j) (res hVW s)
  rw [map_mul, res_res, res_res]
  rw [hcV j]
  apply hc j
private lemma exists_affine_le_inf (V₁ V₂ : X.affineOpens) (x : X) (h₁ : x ∈ (V₁ : X.Opens)) (h₂ : x ∈ (V₂ : X.Opens)) :
  ∃ (V : X.affineOpens), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ V₁ ∧ (V : X.Opens) ≤ V₂ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (V₁ : X.Opens) ⊓ V₂ from ⟨h₁, h₂⟩) ((V₁ : X.Opens) ⊓ V₂).2
  exact ⟨⟨V, hV⟩, hxV, fun y hy => (hle hy).1, fun y hy => (hle hy).2⟩
private noncomputable def glueIdeal (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) (W : X.Opens) : Ideal (X.presheaf.obj (op W)) where
  carrier := {s | ∀ x ∈ W, LocMem U g W s x}
  zero_mem' := by
    intro x hx
    obtain ⟨V, i, hxV, hVW, hVU⟩ := exists_affine_nhd U hU W x hx
    refine ⟨V, i, hxV, hVW, hVU, ?_⟩
    rw [map_zero]
    apply zero_mem
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := ha x hx
    obtain ⟨V'', hxV'', hle, hmemb⟩ := (hb x hx).restrict U g hcomp V i hxV hVW hVU
      (fun V₁ hx₁ => exists_affine_le_inf V₁ V x hx₁ hxV)
    refine ⟨V'', i, hxV'', hle.trans hVW, hle.trans hVU, ?_⟩
    rw [map_add]
    refine add_mem ?_ hmemb
    have := res_mem_span hle hVU (g i) _ hmem
    rwa [res_res] at this
  smul_mem' := by
    intro c s hs x hx
    obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := hs x hx
    refine ⟨V, i, hxV, hVW, hVU, ?_⟩
    rw [smul_eq_mul, map_mul]
    apply Ideal.mul_mem_left _ _ hmem
private lemma mem_glueIdeal (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) {W : X.Opens} {s : (X.presheaf.obj (op W))} : s ∈ glueIdeal U g hU hcomp W ↔ ∀ x ∈ W, LocMem U g W s x := Iff.rfl
private lemma glueIdeal_eq_span (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors (X.presheaf.obj (op (W : X.Opens)))) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i) :
  glueIdeal U g hU hcomp W = Ideal.span {res h (g i)} := by
  apply le_antisymm
  ·
    intro s hs
    have := mem_span_of_locMem U g hg hcomp (W : X.Opens) s i W le_rfl h hs
    rwa [res_self] at this
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff]
    intro x hx
    refine ⟨W, i, hx, le_rfl, h, ?_⟩
    rw [res_self]
    apply Ideal.subset_span rfl
private lemma res_mem_glueIdeal (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) {W W' : X.Opens} (hW : W' ≤ W) {s : (X.presheaf.obj (op W))} (hs : s ∈ glueIdeal U g hU hcomp W) :
  res hW s ∈ glueIdeal U g hU hcomp W' := by
  intro x hx
  obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := hs x (hW hx)
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (V : X.Opens) ⊓ W' from ⟨hxV, hx⟩) ((V : X.Opens) ⊓ W').2
  have h1 : (V' : Set X) ≤ (V : X.Opens) := fun y hy => (hle hy).1
  have h2 : (V' : Set X) ≤ (W' : X.Opens) := fun y hy => (hle hy).2
  refine ⟨⟨V', hV'⟩, i, hxV', h2, fun y hy => hVU (h1 hy), ?_⟩
  have := res_mem_span (V := V') h1 hVU (g i) _ hmem
  rw [res_res] at this
  rwa [res_res]
private lemma map_glueIdeal_basicOpen (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors (X.presheaf.obj (op (W : X.Opens)))) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) (W : X.affineOpens) (f : (X.presheaf.obj (op (W : X.Opens)))) :
  Ideal.map (res (X.basicOpen_le f)) (glueIdeal U g hU hcomp W) = glueIdeal U g hU hcomp (X.affineBasicOpen f) := by
  classical
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    apply res_mem_glueIdeal U g hU hcomp (X.basicOpen_le f) hs
  ·
    intro s hs
    let _ := W.2.isLocalization_basicOpen f
    obtain ⟨⟨a₀, ⟨_, m, rfl⟩⟩, ha₀⟩ := IsLocalization.surj (Submonoid.powers f) s
    simp only at ha₀
    have key : ∀ x ∈ (W : X.Opens), ∃ (V : X.affineOpens) (i : ι) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U i), ∃ N : ℕ, res hVW (f ^ N * a₀) ∈ Ideal.span {res hVU (g i)} := by
      intro x hx
      obtain ⟨V, i, hxV, hVW, hVU⟩ := exists_affine_nhd U hU W x hx
      refine ⟨V, i, hxV, hVW, hVU, ?_⟩
      let fV : (X.presheaf.obj (op (V : X.Opens))) := res hVW f
      have hV'V : (X.affineBasicOpen fV : X.Opens) ≤ V := X.basicOpen_le fV
      have hV'D : (X.affineBasicOpen fV : X.Opens) ≤ X.affineBasicOpen f := by
        change X.basicOpen fV ≤ X.basicOpen f
        rw [Scheme.basicOpen_res]
        apply inf_le_right
      have hsV' := mem_span_of_locMem U g hg hcomp (X.affineBasicOpen f) s i (X.affineBasicOpen fV) hV'D (hV'V.trans hVU)
        (fun y hy => hs y (hV'D hy))
      have ha₀V' : res hV'V (res hVW a₀) ∈ Ideal.span {res (hV'V.trans hVU) (g i)} := by
        have e : res hV'D s * res hV'D (res (X.basicOpen_le f) (f ^ m)) = res hV'D (res (X.basicOpen_le f) a₀) := by
          rw [← map_mul]
          apply congrArg (res hV'D) ha₀
        erw [res_res, res_res] at e
        rw [res_res, show res (hV'V.trans hVW) a₀ = res (hV'D.trans (X.basicOpen_le f)) a₀ from rfl, ← e]
        apply Ideal.mul_mem_right _ _ hsV'
      let _ := V.2.isLocalization_basicOpen fV
      have hmap : res hV'V (res hVW a₀) ∈ Ideal.map (algebraMap (X.presheaf.obj (op (V : X.Opens))) (X.presheaf.obj (op (X.basicOpen fV)))) (Ideal.span {res hVU (g i)}) := by
        rw [Ideal.map_span, Set.image_singleton,
          show (algebraMap (X.presheaf.obj (op (V : X.Opens))) (X.presheaf.obj (op (X.basicOpen fV)))) (res hVU (g i)) = res (hV'V.trans hVU) (g i) from res_res _ _ _]
        apply ha₀V'
      obtain ⟨⟨⟨b, hb⟩, ⟨_, k, rfl⟩⟩, hbk0⟩ := Iff.mp (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers fV) (X.presheaf.obj (op (X.basicOpen fV)))) hmap
      have hbk : algebraMap (X.presheaf.obj (op (V : X.Opens))) (X.presheaf.obj (op (X.basicOpen fV))) (res hVW a₀ * fV ^ k) =
          algebraMap (X.presheaf.obj (op (V : X.Opens))) (X.presheaf.obj (op (X.basicOpen fV))) b := by
        rwa [map_mul]
      obtain ⟨⟨_, k', rfl⟩, hk'⟩ := Iff.mp (IsLocalization.eq_iff_exists (Submonoid.powers fV) (X.presheaf.obj (op (X.basicOpen fV)))) hbk
      change fV ^ k' * (res hVW a₀ * fV ^ k) = fV ^ k' * b at hk'
      refine ⟨k' + k, ?_⟩
      have : res hVW (f ^ (k' + k) * a₀) = fV ^ k' * (res hVW a₀ * fV ^ k) := by
        rw [map_mul, map_pow]
        ring
      rw [this, hk']
      apply Ideal.mul_mem_left _ _ hb
    choose V i hxV hVW hVU N hN using key
    obtain ⟨t, ht⟩ := W.2.isCompact.elim_finite_subcover (fun x : (W : X.Opens) => ((V x.1 x.2 : X.Opens) : Set X))
      (fun x => (V x.1 x.2 : X.Opens).2) (fun x hx => Iff.mpr Set.mem_iUnion ⟨⟨x, hx⟩, hxV x hx⟩)
    let Nmax : ℕ := t.sup (fun x => N x.1 x.2)
    have hmemW : f ^ Nmax * a₀ ∈ glueIdeal U g hU hcomp W := by
      intro y hy
      obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ ((V x.1 x.2 : X.Opens) : Set X) := by
        simpa only [Set.mem_iUnion, exists_prop] using ht hy
      refine ⟨V x.1 x.2, i x.1 x.2, hyx, hVW x.1 x.2, hVU x.1 x.2, ?_⟩
      have hle : N x.1 x.2 ≤ Nmax := Finset.le_sup (f := fun x => N x.1 x.2) hxt
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have : f ^ Nmax * a₀ = f ^ d * (f ^ N x.1 x.2 * a₀) := by
        rw [hd]
        ring
      rw [this, map_mul]
      apply Ideal.mul_mem_left _ _ (hN x.1 x.2)
    have hs' : s * algebraMap (X.presheaf.obj (op (W : X.Opens))) (X.presheaf.obj (op (X.basicOpen f))) (f ^ (m + Nmax)) =
        algebraMap (X.presheaf.obj (op (W : X.Opens))) (X.presheaf.obj (op (X.basicOpen f))) (f ^ Nmax * a₀) := by
      rw [pow_add, map_mul, ← mul_assoc, ha₀, map_mul]
      ring
    obtain ⟨u, hu⟩ := IsLocalization.map_units (X.presheaf.obj (op (X.basicOpen f))) (⟨f ^ (m + Nmax), _, rfl⟩ : Submonoid.powers f)
    have hu' : (↑u : (X.presheaf.obj (op (X.basicOpen f)))) = algebraMap (X.presheaf.obj (op (W : X.Opens))) (X.presheaf.obj (op (X.basicOpen f))) (f ^ (m + Nmax)) := hu
    have : s = algebraMap (X.presheaf.obj (op (W : X.Opens))) (X.presheaf.obj (op (X.basicOpen f))) (f ^ Nmax * a₀) * ↑u⁻¹ := by
      rw [← hs', ← hu', mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmemW)
private noncomputable def glueIdealSheafData (U : ι → X.affineOpens) (g : ∀ i, (X.presheaf.obj (op (U i)))) (hU : ⨆ i, (U i : X.Opens) = ⊤) (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors (X.presheaf.obj (op (W : X.Opens)))) (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j), Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)}) : X.IdealSheafData :=
  Scheme.IdealSheafData.mk (fun W => glueIdeal U g hU hcomp W) (fun W f => map_glueIdeal_basicOpen U g hU hg hcomp W f) _ rfl
private lemma exists_affine_res_mem_span_of_germ
  {W : X.Opens} (a b : (X.presheaf.obj (op W))) (x : X) (hx : x ∈ W)
  (h : ∃ u : X.presheaf.stalk x, X.presheaf.germ W x hx a = u * X.presheaf.germ W x hx b) :
  ∃ (V : X.affineOpens) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W), res hVW a ∈ Ideal.span {res hVW b} := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨V₁, hxV₁, u', rfl⟩ := X.presheaf.exists_germ_eq (x := x) u
  have e : X.presheaf.germ (W ⊓ V₁) x ⟨hx, hxV₁⟩ (res inf_le_left a) =
      X.presheaf.germ (W ⊓ V₁) x ⟨hx, hxV₁⟩ (res inf_le_right u' * res inf_le_left b) := by
    rw [map_mul]
    erw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨hx, hxV₁⟩,
      TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨hx, hxV₁⟩,
      TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨hx, hxV₁⟩]
    apply hu
  obtain ⟨V₂, hxV₂, i₁, i₂, heq⟩ := X.presheaf.germ_eq (U := W ⊓ V₁) (V := W ⊓ V₁) x ⟨hx, hxV₁⟩ ⟨hx, hxV₁⟩ (res inf_le_left a) (res inf_le_right u' * res inf_le_left b) e
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV₂ V₂.2
  have hVW : (V : Set X) ≤ (W : X.Opens) := fun y hy => (i₁.le (hle hy)).1
  refine ⟨⟨V, hV⟩, hxV, hVW, ?_⟩
  rw [Ideal.mem_span_singleton']
  refine ⟨res (show (V : X.Opens) ≤ W ⊓ V₁ from fun y hy => i₂.le (hle hy)) (res inf_le_right u'), ?_⟩
  have := congrArg (res (show (V : X.Opens) ≤ V₂ from hle)) heq
  change res hle (X.presheaf.map i₁.op (res inf_le_left a)) = res hle (X.presheaf.map i₂.op (res inf_le_right u' * res inf_le_left b)) at this
  rw [map_mul, map_mul] at this
  erw [res_res, res_res, res_res, res_res, res_res, res_res] at this
  rw [res_res]
  apply this.symm
private lemma span_le_span_of_forall_germ
  (W : X.affineOpens) (a b : (X.presheaf.obj (op (W : X.Opens))))
  (hb : ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W), res h b ∈ nonZeroDivisors (X.presheaf.obj (op (V : X.Opens))))
  (h : ∀ x (hx : x ∈ (W : X.Opens)), ∃ u : X.presheaf.stalk x, X.presheaf.germ W x hx a = u * X.presheaf.germ W x hx b) :
  Ideal.span {a} ≤ Ideal.span {b} := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  have key := mem_span_of_locMem (ι := PUnit.{u+1}) (fun _ => W) (fun _ => b)
    (fun _ V hV => hb V hV) (fun _ _ V hi hj => rfl) (W : X.Opens) a PUnit.unit W le_rfl le_rfl (fun x hx => by
      obtain ⟨V, hxV, hVW, hmem⟩ := exists_affine_res_mem_span_of_germ a b x hx (h x hx)
      exact ⟨V, PUnit.unit, hxV, hVW, hVW, hmem⟩)
  rwa [res_self, res_self] at key
/--
[AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (W : X.affineOpens) (a b : (X.presheaf.obj (op (W : X.Opens))))
  (hb : ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W), (X.presheaf.map (homOfLE h).op).hom b ∈ nonZeroDivisors (X.presheaf.obj (op (V : X.Opens))))
  (h : ∀ (x : ↥X) (hx : x ∈ (W : X.Opens)), ∃ u : X.presheaf.stalk x, (X.presheaf.germ (W : X.Opens) x hx).hom a = u * (X.presheaf.germ (W : X.Opens) x hx).hom b) :
  Ideal.span {a} ≤ Ideal.span {b} :=
  span_le_span_of_forall_germ W a b hb h


-- created on 2026-10-20
