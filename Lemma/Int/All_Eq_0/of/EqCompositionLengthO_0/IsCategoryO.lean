import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3


/--
[CategoryO.subsingleton_of_compositionLengthO_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.subsingleton_of_compositionLengthO_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
-- given
  (hXO : IsCategoryO Δ rd X)
  (hlen : CategoryO.compositionLengthO X hXO = 0) :
-- imply
  ∀ (x : X), x = 0 := by
-- proof
  set cs := Classical.choice (categoryO_has_composition_series hXO) with hcs_def
  have h_len_eq : cs.length = 0 := hlen
  have h_bot := cs.bot
  have h_top := cs.top
  have h_idx : (⟨0, Nat.zero_lt_succ cs.length⟩ : Fin (cs.length + 1)) =
    ⟨cs.length, Nat.lt_succ_iff.mpr le_rfl⟩ := by
    ext; simp [h_len_eq]
  have h_eq : (⊤ : LieSubmodule R 𝔤 X) = ⊥ := by
    rw [← h_top, ← h_bot, h_idx]
  intro x
  have hx : x ∈ (⊤ : LieSubmodule R 𝔤 X) := LieSubmodule.mem_top x
  rw [h_eq] at hx
  exact (LieSubmodule.mem_bot (R := R) x).mp hx

/--
[CategoryO.maximal_weight_hwv_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.maximal_weight_hwv_exists
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
-- given
  (hXO : IsCategoryO Δ rd X)
  (hlen : CategoryO.compositionLengthO X hXO ≠ 0) :
-- imply
  ∃ (lam : Δ.𝔥 →ₗ[R] R) (v : X), v ≠ 0 ∧ (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = lam h • v) ∧ (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by
-- proof
  haveI : Nontrivial X := by
    by_contra h
    haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    apply hlen
    have hall : ∀ (x : X), x = 0 := fun x => Subsingleton.elim x 0
    have htop_eq_bot : (⊤ : LieSubmodule R 𝔤 X) = ⊥ := by
      ext x; constructor
      · intro _; exact (LieSubmodule.mem_bot (R := R) x).mpr (hall x)
      · intro _; exact LieSubmodule.mem_top x
    show (Classical.choice (categoryO_has_composition_series hXO)).length = 0
    set cs := Classical.choice (categoryO_has_composition_series hXO)
    by_contra hlen0
    have hlen_pos : 0 < cs.length := Nat.pos_of_ne_zero hlen0
    have hstrict := cs.strictly_increasing ⟨0, hlen_pos⟩
    have h0 : cs.series ⟨0, Nat.zero_lt_succ cs.length⟩ = ⊥ := cs.bot
    have h1_le : cs.series (Fin.succ ⟨0, hlen_pos⟩) ≤ ⊥ := by
      calc cs.series (Fin.succ ⟨0, hlen_pos⟩) ≤ ⊤ := le_top
        _ = ⊥ := htop_eq_bot
    have h1_eq : cs.series (Fin.succ ⟨0, hlen_pos⟩) = ⊥ :=
      le_antisymm h1_le bot_le
    have h0_eq : cs.series (Fin.castSucc ⟨0, hlen_pos⟩) = ⊥ := by
      have : Fin.castSucc (⟨0, hlen_pos⟩ : Fin cs.length) = ⟨0, Nat.zero_lt_succ cs.length⟩ :=
        Fin.ext rfl
      rw [this]; exact h0
    rw [h0_eq, h1_eq] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨v, lam, hv_ne, hv_wt, hv_killed⟩ := CategoryO.exists_singular_vector hXO
  exact ⟨lam, v, hv_ne, hv_wt, hv_killed⟩

/--
[compositionLengthO_pos_of_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma compositionLengthO_pos_of_ne_bot
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {Z : LieSubmodule R 𝔤 X}
-- given
  (hXO : IsCategoryO Δ rd X)
  (hZO : IsCategoryO Δ rd ↥Z)
  (hZ_ne_bot : Z ≠ ⊥) :
-- imply
  0 < CategoryO.compositionLengthO ↥Z hZO := by
-- proof
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have hall := CategoryO.subsingleton_of_compositionLengthO_zero ↥Z hZO h
  apply hZ_ne_bot
  rw [LieSubmodule.eq_bot_iff]
  intro m hm
  have h_zero := hall ⟨m, hm⟩
  simpa [Subtype.ext_iff, ZeroMemClass.coe_zero] using h_zero

/--
[contragredient_verma_no_hwv_of_ne'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma contragredient_verma_no_hwv_of_ne'
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {mu : Δ.𝔥 →ₗ[R] R}
  {MmuDual : Type uCatO}
  [AddCommGroup MmuDual]
  [Module R MmuDual]
  [LieRingModule 𝔤 MmuDual]
  [LieModule R 𝔤 MmuDual]
  {lam : Δ.𝔥 →ₗ[R] R}
  {w : MmuDual}
-- given
  (hMmuDualO : IsCategoryO Δ rd MmuDual)
  (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
  (hmu : lam ≠ mu)
  (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
  (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0) :
-- imply
  w = 0 := by
-- proof
  obtain ⟨Mmu_inner, _inst_acg, _inst_mod, _inst_lrm, _inst_lm,
    ⟨hVerma_ne⟩, _hMmuO_inner, β, hβ_contra, hβ_left_nd, _hβ_right_nd⟩ := hContra
  apply hβ_left_nd
  intro m'
  set N_w := LieSubmodule.lieSpan R 𝔤 ({w} : Set MmuDual) with hN_w_def
  have hw_mem : w ∈ N_w := LieSubmodule.subset_lieSpan (Set.mem_singleton w)
  suffices h_strong : ∀ w' ∈ N_w, (β w') m' = 0 from h_strong w hw_mem
  have hm'_mem : m' ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma_ne.highestWeightVec} : Set Mmu_inner) := by
    rw [hVerma_ne.generates]; trivial
  revert m'
  intro m' hm'_mem
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun m'' _ => ∀ w' ∈ N_w, (β w') m'' = 0) ?mem ?zero ?add ?smul ?lie hm'_mem
  case mem =>
    intro m'' hm''
    rw [Set.mem_singleton_iff] at hm''
    subst hm''
    intro w' hw'
    exact bilinear_vanishing_on_hwv' mu hVerma_ne β hβ_contra lam hmu w hw_cartan hw_npos w' hw'
  case zero =>
    intro w' _
    exact map_zero (β w')
  case add =>
    intro x y _ _ hx hy w' hw'
    rw [map_add, hx w' hw', hy w' hw', add_zero]
  case smul =>
    intro a x _ hx w' hw'
    rw [map_smul, hx w' hw', smul_zero]
  case lie =>
    intro x y _ hy w' hw'
    have hc := hβ_contra x w' y
    have : (β w') ⁅x, y⁆ = -((β ⁅x, w'⁆) y) := eq_neg_of_add_eq_zero_right hc
    rw [this]
    have hxw'_mem : ⁅x, w'⁆ ∈ N_w := N_w.lie_mem hw'
    rw [hy ⁅x, w'⁆ hxw'_mem, neg_zero]

/--
[hom_vanishing_verma_contragredientVerma_neq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma hom_vanishing_verma_contragredientVerma_neq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {Z : LieSubmodule R 𝔤 X}
  {lam_step : Δ.𝔥 →ₗ[R] R}
  {Q : Type uCatO}
  [AddCommGroup Q]
  [Module R Q]
  [LieRingModule 𝔤 Q]
  [LieModule R 𝔤 Q]
  {_ : IsVermaModule Δ Q lam_step}
  {π : ↥Z →ₗ⁅R, 𝔤⁆ Q}
  {mu : Δ.𝔥 →ₗ[R] R}
  {MmuDual : Type uCatO}
  [AddCommGroup MmuDual]
  [Module R MmuDual]
  [LieRingModule 𝔤 MmuDual]
  [LieModule R 𝔤 MmuDual]
  {f : ↥Z →ₗ⁅R, 𝔤⁆ MmuDual}
-- given
  (_hπ_surj : Function.Surjective π)
  (_hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))
  (hmu_ne : mu ≠ lam_step)
  (hMmuDualO : IsCategoryO Δ rd MmuDual)
  (_hContra : IsContragredientVerma rd MmuDual mu hMmuDualO) :
-- imply
  f = 0 := by
-- proof
  have hVerma := ‹IsVermaModule Δ Q lam_step›
  obtain ⟨z₀, hz₀⟩ := _hπ_surj hVerma.highestWeightVec
  have π_inj : ∀ (a b : ↥Z), π a = π b → a = b := by
    intro a b hab
    have h1 : π (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 := (_hπ_ker (a - b)).mp h1
    rw [LieSubmodule.mem_bot] at h2
    exact sub_eq_zero.mp (Subtype.ext h2)
  have hfz₀ : f z₀ = 0 := by
    apply contragredient_verma_no_hwv_of_ne' mu MmuDual hMmuDualO _hContra lam_step (Ne.symm hmu_ne)
    ·
      intro h
      rw [← f.map_lie]
      have hlie : π ⁅(↑h : 𝔤), z₀⁆ = π (lam_step h • z₀) := by
        rw [π.map_lie, hz₀, hVerma.cartan_action, map_smul, hz₀]
      rw [π_inj _ _ hlie, map_smul]
    ·
      intro e
      rw [← f.map_lie]
      have hlie : π ⁅(↑e : 𝔤), z₀⁆ = 0 := by
        rw [π.map_lie, hz₀, hVerma.npos_action]
      have h_ker := (_hπ_ker ⁅(↑e : 𝔤), z₀⁆).mp hlie
      rw [LieSubmodule.mem_bot] at h_ker
      rw [show ⁅(↑e : 𝔤), z₀⁆ = (0 : ↥Z) from Subtype.ext h_ker, map_zero]
  have hgen : LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hπz_mem : π z ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma.highestWeightVec} : Set Q) := by
      rw [hVerma.generates]; trivial
    suffices h : ∀ q ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma.highestWeightVec} : Set Q),
      ∀ z : ↥Z, π z = q → z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) by
      exact h (π z) hπz_mem z rfl
    intro q hq
    refine LieSubmodule.lieSpan_induction R 𝔤
      (p := fun q _ => ∀ z : ↥Z, π z = q → z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z))
      ?mem ?zero ?add ?smul ?lie hq
    case mem =>
      intro q' hq' z' hπz'
      rw [Set.mem_singleton_iff] at hq'
      subst hq'
      rw [show z' = z₀ from π_inj _ _ (by rw [hπz', hz₀])]
      exact LieSubmodule.subset_lieSpan (Set.mem_singleton z₀)
    case zero =>
      intro z' hπz'
      have := (_hπ_ker z').mp hπz'
      rw [LieSubmodule.mem_bot] at this
      rw [show z' = (0 : ↥Z) from Subtype.ext this]
      exact zero_mem _
    case add =>
      intro a b _ _ ha hb z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      obtain ⟨zb, hzb⟩ := _hπ_surj b
      rw [show z' = za + zb from π_inj _ _ (by rw [map_add, hza, hzb, hπz'])]
      exact add_mem (ha za hza) (hb zb hzb)
    case smul =>
      intro r' a _ ha z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      rw [show z' = r' • za from π_inj _ _ (by rw [map_smul, hza, hπz'])]
      exact SMulMemClass.smul_mem r' (ha za hza)
    case lie =>
      intro x a _ ha z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      rw [show z' = ⁅x, za⁆ from π_inj _ _ (by rw [π.map_lie, hza, hπz'])]
      exact LieSubmodule.lie_mem _ (ha za hza)
  ext z
  have hz_mem : z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) := by
    rw [hgen]; trivial
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun z' _ => f z' = 0) ?mem ?zero ?add ?smul ?lie hz_mem
  case mem =>
    intro z' hz'
    rw [Set.mem_singleton_iff] at hz'
    subst hz'; exact hfz₀
  case zero => simp [map_zero]
  case add =>
    intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  case smul =>
    intro r' a _ ha
    rw [map_smul, ha, smul_zero]
  case lie =>
    intro x a _ ha
    rw [f.map_lie, ha, lie_zero]

/--
[standard_filtration_gluing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma standard_filtration_gluing
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {Z : LieSubmodule R 𝔤 X}
  {lam : Δ.𝔥 →ₗ[R] R}
  {Q : Type uCatO}
  [AddCommGroup Q]
  [Module R Q]
  [LieRingModule 𝔤 Q]
  [LieModule R 𝔤 Q]
  {_ : IsVermaModule Δ Q lam}
  {π : ↥Z →ₗ⁅R, 𝔤⁆ Q}
  {Y : Type uCatO}
  [AddCommGroup Y]
  [Module R Y]
  [LieRingModule 𝔤 Y]
  [LieModule R 𝔤 Y]
  {q : X →ₗ⁅R, 𝔤⁆ Y}
-- given
  (hXO : IsCategoryO Δ rd X)
  (hπ_surj : Function.Surjective π)
  (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))
  (hYO : IsCategoryO Δ rd Y)
  (hq_surj : Function.Surjective q)
  (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)
  (hY_sf : HasStandardFiltration rd Y hYO) :
-- imply
  HasStandardFiltration rd X hXO := by
-- proof
  obtain ⟨n, G, hG_bot, hG_top, hG_strict, hG_verma⟩ := hY_sf
  have hcomap_bot : LieSubmodule.comap q ⊥ = Z := by
    ext x; simp only [LieSubmodule.mem_comap, LieSubmodule.mem_bot]; exact hq_ker x
  have hcomap_top : LieSubmodule.comap q ⊤ = ⊤ := by
    ext x; simp [LieSubmodule.mem_comap]
  have hcomap_G0 : LieSubmodule.comap q (G ⟨0, Nat.zero_lt_succ n⟩) = Z := by
    rw [hG_bot]; exact hcomap_bot
  have hcomap_Gn : LieSubmodule.comap q (G ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩) = ⊤ := by
    rw [hG_top]; exact hcomap_top
  have hcomap_strict : StrictMono (LieSubmodule.comap (f := q)) := by
    intro A B hAB
    refine lt_of_le_of_ne ((LieSubmodule.gc_map_comap q).monotone_u hAB.le) ?_
    intro heq
    have h_surj_map : ∀ N', LieSubmodule.map q (LieSubmodule.comap q N') = N' := by
      intro N'
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact LieSubmodule.mem_comap.mp hx
      · intro hy; obtain ⟨x, rfl⟩ := hq_surj y; exact ⟨x, LieSubmodule.mem_comap.mpr hy, rfl⟩
    have := congr_arg (LieSubmodule.map q) heq
    rw [h_surj_map, h_surj_map] at this
    exact (ne_of_lt hAB) this
  let F : Fin (n + 1 + 1) → LieSubmodule R 𝔤 X := fun ⟨k, hk⟩ =>
    if hk0 : k = 0 then ⊥
    else LieSubmodule.comap q (G ⟨k - 1, by omega⟩)
  have hF_bot : F ⟨0, Nat.zero_lt_succ (n + 1)⟩ = ⊥ := by
    simp only [F, dif_pos rfl]
  have hF_top : F ⟨n + 1, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ := by
    simp only [F, dif_neg (Nat.succ_ne_zero n)]
    simp only [show n + 1 - 1 = n from rfl]
    exact hcomap_Gn
  have hF_strict : ∀ i : Fin (n + 1), F i.castSucc < F i.succ := by
    intro ⟨i, hi⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk, F]
    simp only [dif_neg (Nat.succ_ne_zero i)]
    simp only [show i + 1 - 1 = i from rfl]
    by_cases hi0 : i = 0
    ·
      subst hi0
      show ⊥ < LieSubmodule.comap q (G ⟨0, _⟩)
      rw [bot_lt_iff_ne_bot, hcomap_G0]
      intro hZ_bot
      have hVerma := ‹IsVermaModule Δ Q lam›
      obtain ⟨z, hz⟩ := hπ_surj hVerma.highestWeightVec
      have : (z : X) ∈ (⊥ : LieSubmodule R 𝔤 X) := hZ_bot ▸ z.2
      have : π z = 0 := (hπ_ker z).mpr this
      exact hVerma.hwv_ne_zero (hz ▸ this)
    ·
      simp only [dif_neg hi0]
      apply hcomap_strict
      have hi' : i - 1 < n := by omega
      have := hG_strict ⟨i - 1, hi'⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at this
      convert this using 1
      exact congr_arg G (Fin.ext (by simp; omega))
  have hF_verma : ∀ i : Fin (n + 1), ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
    (Q_i : Type uCatO) (_ : AddCommGroup Q_i) (_ : Module R Q_i)
    (_ : LieRingModule 𝔤 Q_i) (_ : LieModule R 𝔤 Q_i)
    (_ : IsVermaModule Δ Q_i lam_i)
    (π_i : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q_i),
    Function.Surjective π_i ∧
    (∀ x : ↥(F i.succ), π_i x = 0 ↔ (x : X) ∈ F i.castSucc) := by
    intro ⟨i, hi⟩
    by_cases hi0 : i = 0
    ·
      subst hi0
      have hF1_eq : F ⟨1, by omega⟩ = Z := by
        simp only [F, dif_neg one_ne_zero]
        simp only [show 1 - 1 = 0 from rfl]
        exact hcomap_G0
      have hF1_le_Z : F ⟨1, by omega⟩ ≤ Z := hF1_eq ▸ le_refl _
      have hZ_le_F1 : Z ≤ F ⟨1, by omega⟩ := hF1_eq ▸ le_refl _
      let π₀ : ↥(F ⟨1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q :=
        { toFun := fun x => π ⟨x.1, hF1_le_Z x.2⟩
          map_add' := fun a b => by
            have : (⟨(a + b).1, hF1_le_Z (a + b).2⟩ : ↥Z) =
              ⟨a.1, hF1_le_Z a.2⟩ + ⟨b.1, hF1_le_Z b.2⟩ := Subtype.ext rfl
            simp only [this, map_add]
          map_smul' := fun r x => by
            have : (⟨(r • x).1, hF1_le_Z (r • x).2⟩ : ↥Z) =
              r • ⟨x.1, hF1_le_Z x.2⟩ := Subtype.ext rfl
            simp only [this, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have : (⟨(⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).1, hF1_le_Z (⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).2⟩ : ↥Z) =
              ⁅g, (⟨x.1, hF1_le_Z x.2⟩ : ↥Z)⁆ := Subtype.ext rfl
            simp only [this, LieModuleHom.map_lie] }
      refine ⟨lam, Q, inferInstance, inferInstance, inferInstance, inferInstance,
        ‹IsVermaModule Δ Q lam›, π₀, ?_, ?_⟩
      ·
        intro y
        obtain ⟨z, hz⟩ := hπ_surj y
        exact ⟨⟨z.1, hZ_le_F1 z.2⟩, hz⟩
      ·
        intro x
        show π ⟨x.1, hF1_le_Z x.2⟩ = 0 ↔ (x : X) ∈ F ⟨0, by omega⟩
        rw [hF_bot, hπ_ker]
    ·
      have hi1 : i - 1 < n := by omega
      obtain ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, π_j,
        hπj_surj, hπj_ker⟩ := hG_verma ⟨i - 1, hi1⟩
      letI := instQa; letI := instQb; letI := instQc; letI := instQd
      have hFsucc : F ⟨i + 1, by omega⟩ =
        LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := by
        simp only [F, dif_neg (Nat.succ_ne_zero i)]
        exact congr_arg (LieSubmodule.comap q) (congr_arg G (Fin.ext (by simp [Fin.succ_mk]; omega)))
      have hFcast : F ⟨i, by omega⟩ =
        LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).castSucc) := by
        simp only [F, dif_neg hi0, Fin.castSucc_mk]
      have hFsucc_le : F ⟨i + 1, by omega⟩ ≤
        LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := hFsucc ▸ le_refl _
      let πComp : ↥(F ⟨i + 1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q_j :=
        { toFun := fun x =>
          π_j ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩
          map_add' := fun a b => by
            have h1 : (⟨q (a + b).1, LieSubmodule.mem_comap.mp (hFsucc_le (a + b).2)⟩ :
              ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
              ⟨q a.1, LieSubmodule.mem_comap.mp (hFsucc_le a.2)⟩ +
              ⟨q b.1, LieSubmodule.mem_comap.mp (hFsucc_le b.2)⟩ :=
              Subtype.ext (map_add q a.1 b.1)
            simp only [h1, map_add]
          map_smul' := fun r x => by
            have h1 : (⟨q (r • x).1, LieSubmodule.mem_comap.mp (hFsucc_le (r • x).2)⟩ :
              ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
              r • ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :=
              Subtype.ext (map_smul q r x.1)
            simp only [h1, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have h1 : (⟨q (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).1,
              LieSubmodule.mem_comap.mp (hFsucc_le (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).2)⟩ :
              ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
              ⁅g, (⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ))⁆ :=
              Subtype.ext (LieModuleHom.map_lie q g x.1)
            simp only [h1, LieModuleHom.map_lie] }
      refine ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, πComp, ?_, ?_⟩
      ·
        intro y
        obtain ⟨g, hg⟩ := hπj_surj y
        obtain ⟨x, hx⟩ := hq_surj (g : Y)
        have hx_mem : x ∈ F ⟨i + 1, by omega⟩ := by
          rw [hFsucc]; exact LieSubmodule.mem_comap.mpr (hx ▸ g.2)
        refine ⟨⟨x, hx_mem⟩, ?_⟩
        show π_j ⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ = y
        have hqx_eq : (⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ :
          ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) = g :=
          Subtype.ext hx
        rw [hqx_eq, hg]
      ·
        intro x
        show π_j ⟨q x.1, _⟩ = 0 ↔ (x : X) ∈ F ⟨i, by omega⟩
        rw [hπj_ker, hFcast]
        simp [LieSubmodule.mem_comap]
  exact ⟨n + 1, F, hF_bot, hF_top, hF_strict, hF_verma⟩

/--
[Module.Free.of_right_split_ses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma Module.Free.of_right_split_ses
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Ring S]
  [AddCommGroup A]
  [AddCommGroup M]
  [AddCommGroup B]
  [Module S A]
  [Module S M]
  [Module S B]
  {j : A →ₗ[S] M}
  {g : M →ₗ[S] B}
  {s : B →ₗ[S] M}
-- given
  (hj_inj : Function.Injective j)
  (hexact : LinearMap.range j = LinearMap.ker g)
  (hgs : g.comp s = LinearMap.id)
  (hA : Module.Free S A)
  (hB : Module.Free S B) :
-- imply
  Module.Free S M := by
-- proof
  haveI := hA; haveI := hB
  let φ : A × B →ₗ[S] M := j.coprod s
  have hg_j : ∀ a, g (j a) = 0 := by
    intro a
    have : j a ∈ LinearMap.range j := ⟨a, rfl⟩
    rw [hexact] at this; exact this
  have hg_s : ∀ b, g (s b) = b := fun b => LinearMap.ext_iff.mp hgs b
  have φ_bij : Function.Bijective φ := by
    constructor
    · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h' : j a₁ + s b₁ = j a₂ + s b₂ := h
      have hg1 : g (j a₁ + s b₁) = g (j a₂ + s b₂) := congr_arg g h'
      rw [map_add, map_add, hg_j, hg_j, zero_add, zero_add, hg_s, hg_s] at hg1
      subst hg1
      have hja : j a₁ = j a₂ := by rwa [add_right_cancel_iff] at h'
      exact Prod.ext (hj_inj hja) rfl
    · intro m
      have hmsg : m - s (g m) ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker, map_sub, hg_s, sub_self]
      rw [← hexact] at hmsg
      obtain ⟨a, ha⟩ := hmsg
      exact ⟨⟨a, g m⟩, show j a + s (g m) = m from by rw [ha, sub_add_cancel]⟩
  exact Module.Free.of_equiv' (Module.Free.prod S A B)
    (LinearEquiv.ofBijective φ φ_bij)

/--
[standard_filtration_free_nminus_helper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma standard_filtration_free_nminus_helper
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
-- given
  (hXO : IsCategoryO Δ rd X)
  (hSF : HasStandardFiltration rd X hXO) :
-- imply
  letI := instModuleUEASubalg Δ.𝔫_neg X Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X := by
-- proof
  letI instX := instModuleUEASubalg Δ.𝔫_neg X
  obtain ⟨n, F, hbot, htop, hmono, hverma⟩ := hSF
  suffices hfree : ∀ (k : ℕ) (hk : k ≤ n),
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k, Nat.lt_succ_of_le hk⟩)
    Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) ↥(F ⟨k, Nat.lt_succ_of_le hk⟩) by
    have h_Fn_free := hfree n le_rfl
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩)
    haveI := h_Fn_free
    have hFn_top : F ⟨n, Nat.lt_succ_of_le le_rfl⟩ = ⊤ := htop
    let incl : ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩) →ₗ⁅R, 𝔤⁆ X :=
      (F ⟨n, Nat.lt_succ_of_le le_rfl⟩).incl
    have incl_bij : Function.Bijective incl := by
      constructor
      · exact Subtype.val_injective
      · intro x
        have : x ∈ (F ⟨n, Nat.lt_succ_of_le le_rfl⟩ : LieSubmodule R 𝔤 X) := by
          rw [hFn_top]; trivial
        exact ⟨⟨x, this⟩, rfl⟩
    let incl_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) incl
    let e : ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩) ≃ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
      LinearEquiv.ofBijective incl_U incl_bij
    exact Module.Free.of_equiv' h_Fn_free e
  intro k
  induction k with
  | zero =>
    intro hk
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨0, Nat.lt_succ_of_le hk⟩)
    have hF0 : F ⟨0, Nat.lt_succ_of_le hk⟩ = ⊥ := by
      convert hbot using 2
    haveI : Subsingleton ↥(F ⟨0, Nat.lt_succ_of_le hk⟩) := by
      rw [hF0]
      exact subsingleton_of_forall_eq 0 (fun ⟨x, hx⟩ => by
        ext; simp only [LieSubmodule.mem_bot] at hx; exact hx)
    exact Module.Free.of_subsingleton _ _
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have ih_free := ih hk'
    have hkn : k < n := Nat.lt_of_succ_le hk
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k + 1, Nat.lt_succ_of_le hk⟩)
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k, Nat.lt_succ_of_le hk'⟩)
    obtain ⟨lam_k, Q, instACG_Q, instMod_Q, instLRM_Q, instLM_Q, hVerma_Q, π, hπ_surj, hπ_ker⟩ :=
      hverma ⟨k, hkn⟩
    letI := instACG_Q; letI := instMod_Q; letI := instLRM_Q; letI := instLM_Q
    letI := instModuleUEASubalg Δ.𝔫_neg Q
    have hQ_free : Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q := by
      obtain ⟨φ, _⟩ := hVerma_Q.free_over_nminus
      exact Module.Free.of_equiv' (Module.Free.self _) φ
    haveI : Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q := hQ_free
    haveI : Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q :=
      Module.Projective.of_free
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F (⟨k, hkn⟩ : Fin n).succ)
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F (⟨k, hkn⟩ : Fin n).castSucc)
    let π_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) π
    obtain ⟨sect, hsect⟩ := Module.projective_lifting_property π_U LinearMap.id hπ_surj
    have hle : F (⟨k, hkn⟩ : Fin n).castSucc ≤ F (⟨k, hkn⟩ : Fin n).succ :=
      le_of_lt (hmono ⟨k, hkn⟩)
    let j_lie := LieSubmodule.inclusion hle
    let j_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) j_lie
    have hj_inj : Function.Injective j_U := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      have : (j_U ⟨a, ha⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val =
        (j_U ⟨b, hb⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val := congr_arg Subtype.val h
      exact Subtype.ext this
    have hexact : LinearMap.range j_U = LinearMap.ker π_U := by
      ext ⟨x, hx⟩
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨⟨y, hy⟩, heq⟩
        have : π (j_lie ⟨y, hy⟩) = 0 := (hπ_ker (j_lie ⟨y, hy⟩)).mpr hy
        rwa [← heq]
      · intro hmem
        have hx_in_cast : (⟨x, hx⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val ∈
          F (⟨k, hkn⟩ : Fin n).castSucc := by
          exact (hπ_ker ⟨x, hx⟩).mp hmem
        exact ⟨⟨x, hx_in_cast⟩, Subtype.ext rfl⟩
    exact Module.Free.of_right_split_ses j_U π_U sect hj_inj hexact hsect ih_free hQ_free

/--
[free_nminus_is_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma free_nminus_is_projective
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
-- given
  (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X; Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
-- imply
  letI := instModuleUEASubalg Δ.𝔫_neg X; Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X := by
-- proof
  letI := instModuleUEASubalg Δ.𝔫_neg X
  haveI := hXfree
  exact Module.Projective.of_free

/--
[projective_nminus_gives_section](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma projective_nminus_gives_section
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {E : Type uCatO}
  [AddCommGroup E]
  [Module R E]
  [LieRingModule 𝔤 E]
  [LieModule R 𝔤 E]
  {p : E →ₗ⁅R, 𝔤⁆ X}
-- given
  (hp : Function.Surjective p)
  (hXproj : letI := instModuleUEASubalg Δ.𝔫_neg X; Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
-- imply
  letI := instModuleUEASubalg Δ.𝔫_neg X; letI := instModuleUEASubalg Δ.𝔫_neg E; ∃ (s₀ : X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E), ∀ x, p (s₀ x) = x := by
-- proof
  letI := instModuleUEASubalg Δ.𝔫_neg X
  letI := instModuleUEASubalg Δ.𝔫_neg E
  haveI := hXproj
  let p_U : E →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
    lieModuleHomToUEALinearMap_local p
  have hp_surj : Function.Surjective p_U := hp
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property p_U LinearMap.id hp_surj
  exact ⟨s₀, fun x => by
    have := LinearMap.ext_iff.mp hs₀ x
    simp [p_U, LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this⟩

/--
[bgg_reciprocity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma bgg_reciprocity
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam mu : Δ.𝔥 →ₗ[R] R} :
-- imply
  standardFiltrationMultiplicity rd wg lam mu = compositionMultiplicity rd wg mu lam :=
-- proof
  bgg_reciprocity_raw rd wg lam mu

/--
[bilinear_vanishing_on_hwv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma bilinear_vanishing_on_hwv
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {MmuDual : Type uCatO}
  [AddCommGroup MmuDual]
  [Module R MmuDual]
  [LieRingModule 𝔤 MmuDual]
  [LieModule R 𝔤 MmuDual]
  {Mmu_inner : Type uCatO}
  [AddCommGroup Mmu_inner]
  [Module R Mmu_inner]
  [LieRingModule 𝔤 Mmu_inner]
  [LieModule R 𝔤 Mmu_inner]
  {mu : Δ.𝔥 →ₗ[R] R}
  {β : MmuDual →ₗ[R] Mmu_inner →ₗ[R] R}
  {lam : Δ.𝔥 →ₗ[R] R}
  {w : MmuDual}
  {w' : MmuDual}
-- given
  (hVerma : IsVermaModule Δ Mmu_inner mu)
  (hβ_contra : ∀ (x : 𝔤) (m : MmuDual) (m' : Mmu_inner), (β ⁅x, m⁆) m' + (β m) ⁅x, m'⁆ = 0)
  (hmu : lam ≠ mu)
  (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
  (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0)
  (hw' : w' ∈ LieSubmodule.lieSpan R 𝔤 {w}) :
-- imply
  (β w') hVerma.highestWeightVec = 0 :=
-- proof
bilinear_vanishing_on_hwv' mu hVerma β hβ_contra lam hmu w hw_cartan hw_npos w' hw'

/--
[contragredient_verma_no_hwv_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma contragredient_verma_no_hwv_of_ne
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {mu : Δ.𝔥 →ₗ[R] R}
  {MmuDual : Type uCatO}
  [AddCommGroup MmuDual]
  [Module R MmuDual]
  [LieRingModule 𝔤 MmuDual]
  [LieModule R 𝔤 MmuDual]
  {lam : Δ.𝔥 →ₗ[R] R}
  {w : MmuDual}
-- given
  (hMmuDualO : IsCategoryO Δ rd MmuDual)
  (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
  (hmu : lam ≠ mu)
  (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
  (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0) :
-- imply
  w = 0 := by
-- proof
  obtain ⟨Mmu_inner, _inst_acg, _inst_mod, _inst_lrm, _inst_lm,
    ⟨hVerma_ne⟩, _hMmuO_inner, β, hβ_contra, hβ_left_nd, _hβ_right_nd⟩ := hContra
  apply hβ_left_nd
  intro m'
  set N_w := LieSubmodule.lieSpan R 𝔤 ({w} : Set MmuDual) with hN_w_def
  have hw_mem : w ∈ N_w := LieSubmodule.subset_lieSpan (Set.mem_singleton w)
  suffices h_strong : ∀ w' ∈ N_w, (β w') m' = 0 from h_strong w hw_mem
  have hm'_mem : m' ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma_ne.highestWeightVec} : Set Mmu_inner) := by
    rw [hVerma_ne.generates]; trivial
  revert m'
  intro m' hm'_mem
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun m'' _ => ∀ w' ∈ N_w, (β w') m'' = 0) ?mem ?zero ?add ?smul ?lie hm'_mem
  case mem =>
    intro m'' hm''
    rw [Set.mem_singleton_iff] at hm''
    subst hm''
    intro w' hw'
    exact bilinear_vanishing_on_hwv mu hVerma_ne β hβ_contra lam hmu w hw_cartan hw_npos w' hw'
  case zero =>
    intro w' _
    exact map_zero (β w')
  case add =>
    intro x y _ _ hx hy w' hw'
    rw [map_add, hx w' hw', hy w' hw', add_zero]
  case smul =>
    intro a x _ hx w' hw'
    rw [map_smul, hx w' hw', smul_zero]
  case lie =>
    intro x y _ hy w' hw'
    have hc := hβ_contra x w' y
    have : (β w') ⁅x, y⁆ = -((β ⁅x, w'⁆) y) := eq_neg_of_add_eq_zero_right hc
    rw [this]
    have hxw'_mem : ⁅x, w'⁆ ∈ N_w := N_w.lie_mem hw'
    rw [hy ⁅x, w'⁆ hxw'_mem, neg_zero]

/--
[tensor_hom_vanishing_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma tensor_hom_vanishing_ne
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {E : Type uCatO}
  [AddCommGroup E]
  [Module R E]
  [LieRingModule 𝔤 E]
  [LieModule R 𝔤 E]
  [Module.Finite R E]
  [LieModule.IsTrivial 𝔤 E]
  {Mlam : Type uCatO}
  [AddCommGroup Mlam]
  [Module R Mlam]
  [LieRingModule 𝔤 Mlam]
  [LieModule R 𝔤 Mlam]
  {lam : Δ.𝔥 →ₗ[R] R}
  {mu : Δ.𝔥 →ₗ[R] R}
  {MmuDual : Type uCatO}
  [AddCommGroup MmuDual]
  [Module R MmuDual]
  [LieRingModule 𝔤 MmuDual]
  [LieModule R 𝔤 MmuDual]
  {g : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ MmuDual}
-- given
  (hMlamO : IsCategoryO Δ rd Mlam)
  (hMlam_verma : IsVermaModule Δ Mlam lam)
  (hmu : lam ≠ mu)
  (hMmuDualO : IsCategoryO Δ rd MmuDual)
  (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO) :
-- imply
  g = 0 := by
-- proof
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul e m =>
    have hw : g (e ⊗ₜ[R] hMlam_verma.highestWeightVec) = 0 := by
      apply contragredient_verma_no_hwv_of_ne mu MmuDual hMmuDualO hContra lam hmu
      ·
        intro h
        have : g ⁅(↑h : 𝔤), e ⊗ₜ[R] hMlam_verma.highestWeightVec⁆ =
          ⁅(↑h : 𝔤), g (e ⊗ₜ[R] hMlam_verma.highestWeightVec)⁆ :=
          g.map_lie' (x := ↑h)
        rw [← this]
        have htrivial : ⁅(↑h : 𝔤), e⁆ = (0 : E) :=
          LieModule.IsTrivial.trivial (↑h : 𝔤) e
        rw [TensorProduct.LieModule.lie_tmul_right (↑h : 𝔤) e hMlam_verma.highestWeightVec,
          htrivial, TensorProduct.zero_tmul, zero_add,
          hMlam_verma.cartan_action h, TensorProduct.tmul_smul, map_smul]
      ·
        intro n
        have : g ⁅(↑n : 𝔤), e ⊗ₜ[R] hMlam_verma.highestWeightVec⁆ =
          ⁅(↑n : 𝔤), g (e ⊗ₜ[R] hMlam_verma.highestWeightVec)⁆ :=
          g.map_lie' (x := ↑n)
        rw [← this]
        have htrivial : ⁅(↑n : 𝔤), e⁆ = (0 : E) :=
          LieModule.IsTrivial.trivial (↑n : 𝔤) e
        rw [TensorProduct.LieModule.lie_tmul_right (↑n : 𝔤) e hMlam_verma.highestWeightVec,
          htrivial, TensorProduct.zero_tmul, zero_add,
          hMlam_verma.npos_action n, TensorProduct.tmul_zero, map_zero]
    have f_e_eq : ∀ (m : Mlam), g (e ⊗ₜ[R] m) = 0 := by
      let f_e : Mlam →ₗ⁅R, 𝔤⁆ MmuDual :=
        { toLinearMap := (g : TensorProduct R E Mlam →ₗ[R] MmuDual).comp
          (TensorProduct.mk R E Mlam e)
          map_lie' := fun {x m'} => by
            show g ((TensorProduct.mk R E Mlam e) ⁅x, m'⁆) = ⁅x, g ((TensorProduct.mk R E Mlam e) m')⁆
            simp only [TensorProduct.mk_apply]
            have := g.map_lie' (x := x) (m := e ⊗ₜ[R] m')
            rw [TensorProduct.LieModule.lie_tmul_right,
              LieModule.IsTrivial.trivial x e,
              TensorProduct.zero_tmul, zero_add] at this
            exact this }
      have hf_eq_zero : f_e = 0 := by
        apply hMlam_verma.universal_unique
        simp [f_e, TensorProduct.mk_apply, hw]
      intro m'
      have := LieModuleHom.congr_fun hf_eq_zero m'
      simpa [f_e, TensorProduct.mk_apply] using this
    exact f_e_eq m
  | add x y hx hy =>
    simp [map_add, hx, hy]

/--
[CategoryO.exists_singular_vector_in_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.exists_singular_vector_in_submodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {N : LieSubmodule R 𝔤 M}
-- given
  (hM : IsCategoryO Δ rd M)
  (hN : N ≠ ⊥) :
-- imply
  ∃ (v : M) (mu : Δ.𝔥 →ₗ[R] R), v ∈ N ∧ v ≠ 0 ∧ (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = mu h • v) ∧ (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by
-- proof
  have hNO : IsCategoryO Δ rd N := IsCategoryO_lieSubmodule hM N
  haveI : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot R 𝔤 M).mpr hN
  obtain ⟨v, mu, hv_ne, hv_cartan, hv_npos⟩ :=
    CategoryO.exists_singular_vector hNO
  refine ⟨(v : M), mu, v.property, ?_, ?_, ?_⟩
  ·
    intro h; apply hv_ne; exact_mod_cast h
  ·
    intro h; exact_mod_cast hv_cartan h
  ·
    intro e; exact_mod_cast hv_npos e

/--
[contragredient_verma_socle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma contragredient_verma_socle
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {MlamDual : Type uCatO}
  [AddCommGroup MlamDual]
  [Module R MlamDual]
  [LieRingModule 𝔤 MlamDual]
  [LieModule R 𝔤 MlamDual]
  {_ : IsContragredientVerma rd MlamDual lam _hMlamDualO}
  {N : LieSubmodule R 𝔤 MlamDual}
-- given
  (_hMlamDualO : IsCategoryO Δ rd MlamDual)
  (hN : N ≠ ⊥) :
-- imply
  ∃ (v : MlamDual), v ∈ N ∧ v ∈ WeightSpace Δ MlamDual lam ∧ v ≠ 0 := by
-- proof
  obtain ⟨v, mu, hv_N, hv_ne, hv_cartan, hv_npos⟩ :=
    CategoryO.exists_singular_vector_in_submodule _hMlamDualO N hN
  by_cases hmu : lam = mu
  ·
    refine ⟨v, hv_N, ?_, hv_ne⟩
    intro h
    rw [hmu]
    exact hv_cartan h
  ·
    exfalso
    apply hv_ne
    exact contragredient_verma_no_hwv_of_ne lam MlamDual _hMlamDualO ‹_› mu (Ne.symm hmu) v hv_cartan hv_npos

/--
[lie_hom_preserves_weight_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma lie_hom_preserves_weight_space
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {f : K →ₗ⁅R, 𝔤⁆ N}
  {μ : Δ.𝔥 →ₗ[R] R}
  {k : K}
-- given
  (hk : k ∈ WeightSpace Δ K μ) :
-- imply
  f k ∈ WeightSpace Δ N μ := by
-- proof
  intro h
  rw [← LieModuleHom.map_lie, hk h, map_smul]

/--
[weight_space_sum_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma weight_space_sum_disjoint
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {lam : Δ.𝔥 →ₗ[R] R}
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
  {v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ}
  {m : M}
-- given
  (hlamS : lam ∉ S)
  (hm : m ∈ WeightSpace Δ M lam)
  (hm_sum : m = ∑ μ ∈ S, (v μ : M)) :
-- imply
  m = 0 := by
-- proof
  classical
  let w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ := fun μ =>
    if h : μ = lam then
      ⟨-m, h ▸ (WeightSpace Δ M lam).neg_mem hm⟩
    else
      v μ
  have hsum : ∑ μ ∈ Finset.cons lam S hlamS, (w μ : M) = 0 := by
    rw [Finset.sum_cons]
    simp only [w, dif_pos rfl]
    have hsumS : ∑ μ ∈ S, (w μ : M) = ∑ μ ∈ S, (v μ : M) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      have hne : μ ≠ lam := fun h => hlamS (h ▸ hμ)
      show (w μ : M) = (v μ : M)
      simp only [w, dif_neg hne]
    rw [hsumS, ← hm_sum, neg_add_cancel]
  have hw_lam := weightSpace_sum_eq_zero_components
    (Finset.cons lam S hlamS) w hsum lam (Finset.mem_cons_self lam S)
  simp only [w, dif_pos rfl] at hw_lam
  exact neg_eq_zero.mp hw_lam

/--
[contragredient_verma_socle_weight_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma contragredient_verma_socle_weight_preimage
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  {MlamDual : Type uCatO}
  [AddCommGroup MlamDual]
  [Module R MlamDual]
  [LieRingModule 𝔤 MlamDual]
  [LieModule R 𝔤 MlamDual]
  {f : K →ₗ⁅R, 𝔤⁆ MlamDual}
-- given
  (_hKO : IsCategoryO Δ rd K)
  (_hMlamDualO : IsCategoryO Δ rd MlamDual)
  (hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
  (hf : f ≠ 0) :
-- imply
  ∃ (k : K), k ∈ WeightSpace Δ K lam ∧ k ≠ 0 := by
-- proof
  classical
  have hrange : f.range ≠ ⊥ := by
    intro h; apply hf; ext m
    have : f m ∈ f.range := (LieModuleHom.mem_range f (f m)).2 ⟨m, rfl⟩
    rw [h] at this; simp [LieSubmodule.mem_bot] at this; simp [this]
  obtain ⟨v, hv_range, hv_wt, hv_ne⟩ :=
    contragredient_verma_socle lam MlamDual _hMlamDualO hContra f.range hrange
  rw [LieModuleHom.mem_range] at hv_range
  obtain ⟨k, hk⟩ := hv_range
  obtain ⟨S, w, hk_decomp⟩ := _hKO.weight_decomp k
  have hfw : ∀ μ, f (w μ : K) ∈ WeightSpace Δ MlamDual μ :=
    fun μ => lie_hom_preserves_weight_space f μ (w μ).property
  have hfk_sum : f k = ∑ μ ∈ S, f (w μ : K) := by
    rw [hk_decomp]; simp [map_sum]
  by_contra h_no_wt
  push Not at h_no_wt
  have hw_lam_zero : (w lam : K) = 0 := h_no_wt (w lam) (w lam).property
  have hfw_lam_zero : f (w lam : K) = 0 := by rw [hw_lam_zero, map_zero]
  by_cases hlam : lam ∈ S
  ·
    have hv_sum : v = ∑ μ ∈ S.erase lam, f (w μ : K) := by
      rw [← hk, hfk_sum]
      rw [← Finset.add_sum_erase S _ hlam, hfw_lam_zero, zero_add]
    exact hv_ne (weight_space_sum_disjoint lam (S.erase lam) (Finset.notMem_erase lam S)
      (fun μ => ⟨f (w μ : K), hfw μ⟩) v hv_wt hv_sum)
  ·
    exact hv_ne (weight_space_sum_disjoint lam S hlam
      (fun μ => ⟨f (w μ : K), hfw μ⟩) v hv_wt (by rw [← hk, hfk_sum]))

/--
[nonzero_hom_into_contragredient_gives_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma nonzero_hom_into_contragredient_gives_weight
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  {MlamDual : Type uCatO}
  [AddCommGroup MlamDual]
  [Module R MlamDual]
  [LieRingModule 𝔤 MlamDual]
  [LieModule R 𝔤 MlamDual]
  {f : K →ₗ⁅R, 𝔤⁆ MlamDual}
-- given
  (_hKO : IsCategoryO Δ rd K)
  (_hMlamDualO : IsCategoryO Δ rd MlamDual)
  (hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
  (hf : f ≠ 0) :
-- imply
  WeightSpace Δ K lam ≠ ⊥ := by
-- proof
  obtain ⟨k, hk_wt, hk_ne⟩ := contragredient_verma_socle_weight_preimage lam _hKO MlamDual _hMlamDualO hContra f hf
  intro h_bot
  rw [Submodule.eq_bot_iff] at h_bot
  exact hk_ne (h_bot k hk_wt)

/--
[socle_hom_vanishing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma socle_hom_vanishing_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  {MlamDual : Type uCatO}
  [AddCommGroup MlamDual]
  [Module R MlamDual]
  [LieRingModule 𝔤 MlamDual]
  [LieModule R 𝔤 MlamDual]
  {f : K →ₗ⁅R, 𝔤⁆ MlamDual}
-- given
  (hKO : IsCategoryO Δ rd K)
  (hK_lam : WeightSpace Δ K lam = ⊥)
  (hMlamDualO : IsCategoryO Δ rd MlamDual)
  (hContra : IsContragredientVerma rd MlamDual lam hMlamDualO) :
-- imply
  f = 0 := by
-- proof
  by_contra hf
  exact absurd hK_lam
    (nonzero_hom_into_contragredient_gives_weight lam hKO MlamDual hMlamDualO hContra f hf)

/--
[CategoryO.has_simple_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.has_simple_quotient
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  [Nontrivial K]
-- given
  (hKO : IsCategoryO Δ rd K) :
-- imply
  ∃ (mu : Δ.𝔥 →ₗ[R] R) (Lmu : Type uCatO) (_ : AddCommGroup Lmu) (_ : Module R Lmu) (_ : LieRingModule 𝔤 Lmu) (_ : LieModule R 𝔤 Lmu) (hLmuO : IsCategoryO Δ rd Lmu) (_ : LieModule.IsIrreducible R 𝔤 Lmu) (_ : IsHighestWeightModule Δ Lmu mu) (q : K →ₗ⁅R, 𝔤⁆ Lmu), Function.Surjective q ∧ q ≠ 0 := by
-- proof
  obtain ⟨cs⟩ := categoryO_has_composition_series hKO
  have hlen_pos : 0 < cs.length := by
    by_contra h
    simp only [not_lt, Nat.le_zero] at h
    have hlen_zero : cs.length = 0 := h
    have h_bot := cs.bot
    have h_top := cs.top
    have h_idx_eq : (⟨0, Nat.zero_lt_succ cs.length⟩ : Fin (cs.length + 1)) =
      ⟨cs.length, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      ext; simp [hlen_zero]
    rw [h_idx_eq] at h_bot
    rw [h_bot] at h_top
    have hx : ∀ x : K, x = 0 := by
      intro x
      have hx_top : x ∈ (⊤ : LieSubmodule R 𝔤 K) := trivial
      rw [h_top.symm] at hx_top
      exact (LieSubmodule.mem_bot (R := R) x).mp hx_top
    obtain ⟨a, b, hab⟩ := exists_pair_ne (α := K)
    exact hab (by rw [hx a, hx b])
  set n := cs.length
  have hn_sub : n - 1 < n := Nat.sub_one_lt_of_lt hlen_pos
  set i_last : Fin n := ⟨n - 1, hn_sub⟩
  set Z := cs.series i_last.castSucc
  have hZ_lt_top : Z < ⊤ := by
    have h_strict := cs.strictly_increasing i_last
    have h_succ_val : (i_last.succ : Fin (n + 1)).val = n := by
      simp [i_last]; omega
    have h_eq : cs.series i_last.succ = cs.series ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      congr 1; ext; exact h_succ_val
    rwa [h_eq, cs.top] at h_strict
  have hZ_ne_top : Z ≠ ⊤ := ne_of_lt hZ_lt_top
  have hQO : IsCategoryO Δ rd (K ⧸ Z) := IsCategoryO_quotient hKO Z
  have hQirr : LieModule.IsIrreducible R 𝔤 (K ⧸ Z) := by
    have hirr := cs.quotients_irreducible i_last
    have h_succ_eq_top : cs.series i_last.succ = ⊤ := by
      have h_succ_val : (i_last.succ : Fin (n + 1)).val = n := by
        simp [i_last]; omega
      have h_eq : cs.series i_last.succ = cs.series ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
        congr 1; ext; exact h_succ_val
      rw [h_eq]; exact cs.top
    have hirr' : LieModule.IsIrreducible R 𝔤
      (↥(⊤ : LieSubmodule R 𝔤 K) ⧸ Z.comap (⊤ : LieSubmodule R 𝔤 K).incl) :=
      h_succ_eq_top ▸ hirr
    let f := LieModuleEquiv.ofTop R 𝔤 K
    let P := Z.comap (⊤ : LieSubmodule R 𝔤 K).incl
    have hfP : Submodule.map f.toLinearEquiv.toLinearMap P.toSubmodule = Z.toSubmodule := by
      ext x
      simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [LieSubmodule.mem_comap] at hy; convert hy using 1
      · intro hx
        exact ⟨⟨x, trivial⟩, by rwa [LieSubmodule.mem_comap],
          LieModuleEquiv.ofTop_apply K ⟨x, trivial⟩⟩
    let e_lin := Submodule.Quotient.equiv P.toSubmodule Z.toSubmodule f.toLinearEquiv hfP
    let e : (↥(⊤ : LieSubmodule R 𝔤 K) ⧸ P) ≃ₗ⁅R, 𝔤⁆ (K ⧸ Z) := {
      e_lin with
      map_lie' := by
        intro x m
        induction m using Quotient.inductionOn' with
        | h a =>
          show e_lin (Submodule.Quotient.mk ⁅x, a⁆) =
            Submodule.Quotient.mk ⁅x, f.toLinearEquiv a⁆
          rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
          congr 1
    }
    exact ((LieSubmodule.orderIsoMapComap e).isSimpleOrder_iff).mp hirr'
  obtain ⟨mu, ⟨hHW⟩⟩ := CategoryO.simple_objects_are_highest_weight hQO hQirr
  refine ⟨mu, K ⧸ Z, inferInstance, inferInstance, inferInstance, inferInstance, hQO,
    hQirr, hHW,
    LieSubmodule.Quotient.mk' Z, LieSubmodule.Quotient.surjective_mk' Z, ?_⟩
  intro h
  apply hZ_ne_top
  ext x
  simp only [LieSubmodule.mem_top, iff_true]
  have : (LieSubmodule.Quotient.mk' Z) x = 0 := by simp [h]
  rw [LieSubmodule.Quotient.mk'_apply] at this
  rwa [LieSubmodule.Quotient.mk_eq_zero'] at this

/--
[CategoryO.simple_embeds_in_contragredient_verma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.simple_embeds_in_contragredient_verma
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {ci : CartanInvolution rd}
  {mu : Δ.𝔥 →ₗ[R] R}
  {Lmu : Type uCatO}
  [AddCommGroup Lmu]
  [Module R Lmu]
  [LieRingModule 𝔤 Lmu]
  [LieModule R 𝔤 Lmu]
-- given
  (hLmuO : IsCategoryO Δ rd Lmu)
  (hIrr : LieModule.IsIrreducible R 𝔤 Lmu)
  (hHW : IsHighestWeightModule Δ Lmu mu) :
-- imply
  ∃ (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual) (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual) (hMmuDualO : IsCategoryO Δ rd MmuDual) (_ : IsContragredientVerma rd MmuDual mu hMmuDualO) (ι : Lmu →ₗ⁅R, 𝔤⁆ MmuDual), Function.Injective ι := by
-- proof
  obtain ⟨Mmu, instACG_M, instMod_M, instLRM_M, instLM_M, ⟨hVM⟩⟩ :=
    verma_module_exists (R := R) (𝔤 := 𝔤) Δ mu
  letI := instACG_M; letI := instMod_M; letI := instLRM_M; letI := instLM_M
  have hMmuO : IsCategoryO Δ rd Mmu :=
    @verma_module_isCategoryO R _ 𝔤 _ _ Δ rd Mmu instACG_M instMod_M instLRM_M instLM_M mu hVM
  obtain ⟨η, _hη_gen⟩ := hVM.universal_map Lmu hHW.highestWeightVec
    hHW.cartan_action hHW.npos_action
  have hη_surj : Function.Surjective η := by
    rw [← LieModuleHom.range_eq_top]
    haveI : LieModule.IsIrreducible R 𝔤 Lmu := hIrr
    have h_mem : hHW.highestWeightVec ∈ η.range := by
      rw [LieModuleHom.mem_range]
      exact ⟨hVM.highestWeightVec, _hη_gen⟩
    haveI : Nontrivial ↥η.range := by
      refine ⟨⟨⟨hHW.highestWeightVec, h_mem⟩, 0, ?_⟩⟩
      intro h
      have := congr_arg Subtype.val h
      simp only [ZeroMemClass.coe_zero] at this
      exact hHW.hwv_ne_zero this
    exact LieSubmodule.eq_top_of_isIrreducible R 𝔤 Lmu η.range
  have dM : DualInO ci Mmu hMmuO := dualInO ci hMmuO
  have dL : DualInO ci Lmu hLmuO := dualInO ci hLmuO
  have hContra : IsContragredientVerma rd dM.Xdual mu dM.isCategoryO :=
    verma_dual_is_contragredient ci mu hVM hMmuO dM
  obtain ⟨fdual, hfdual_surj_inj, _⟩ :=
    duality_functor_contravariant ci hMmuO hLmuO η dM dL
  have hfdual_inj : Function.Injective fdual := hfdual_surj_inj hη_surj
  obtain ⟨_, _, iso_L_to_Ldual, hiso_bij⟩ :=
    simple_module_self_dual ci mu hLmuO hIrr hHW dL
  refine ⟨dM.Xdual, dM.instAddCommGroup, dM.instModule,
    dM.instLieRingModule, dM.instLieModule,
    dM.isCategoryO, hContra,
    LieModuleHom.comp fdual iso_L_to_Ldual,
    hfdual_inj.comp hiso_bij.1⟩

/--
[CategoryO.nontrivial_has_hom_to_contragredient_verma_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.nontrivial_has_hom_to_contragredient_verma_aux
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {ci : CartanInvolution rd}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  [Nontrivial K]
-- given
  (hKO : IsCategoryO Δ rd K) :
-- imply
  ∃ (mu : Δ.𝔥 →ₗ[R] R) (Lmu : Type uCatO) (_ : AddCommGroup Lmu) (_ : Module R Lmu) (_ : LieRingModule 𝔤 Lmu) (_ : LieModule R 𝔤 Lmu) (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual) (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual) (hMmuDualO : IsCategoryO Δ rd MmuDual) (_ : IsContragredientVerma rd MmuDual mu hMmuDualO) (q : K →ₗ⁅R, 𝔤⁆ Lmu) (ι : Lmu →ₗ⁅R, 𝔤⁆ MmuDual), Function.Surjective q ∧ Function.Injective ι ∧ q ≠ 0 := by
-- proof
  obtain ⟨mu, Lmu, instACG_L, instMod_L, instLRM_L, instLM_L, hLmuO,
    hIrr, hHW, q, hq_surj, hq_ne⟩ :=
    CategoryO.has_simple_quotient hKO
  obtain ⟨MmuDual, instACG_M, instMod_M, instLRM_M, instLM_M,
    hMmuDualO, hContra, ι, hι_inj⟩ :=
    CategoryO.simple_embeds_in_contragredient_verma ci mu Lmu hLmuO hIrr hHW
  exact ⟨mu, Lmu, instACG_L, instMod_L, instLRM_L, instLM_L,
    MmuDual, instACG_M, instMod_M, instLRM_M, instLM_M,
    hMmuDualO, hContra, q, ι, hq_surj, hι_inj, hq_ne⟩

/--
[CategoryO.nonzero_admits_hom_to_contragredient_verma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma CategoryO.nonzero_admits_hom_to_contragredient_verma
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {ci : CartanInvolution rd}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
  [Nontrivial K]
-- given
  (hKO : IsCategoryO Δ rd K) :
-- imply
  ∃ (mu : Δ.𝔥 →ₗ[R] R) (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual) (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual) (hMmuDualO : IsCategoryO Δ rd MmuDual) (_ : IsContragredientVerma rd MmuDual mu hMmuDualO) (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f ≠ 0 := by
-- proof
  obtain ⟨mu, Lmu, instACG, instMod, instLRM, instLM,
    MmuDual, instACG', instMod', instLRM', instLM',
    hMmuDualO, hContra,
    q, ι, hq_surj, hι_inj, hq_ne⟩ :=
    CategoryO.nontrivial_has_hom_to_contragredient_verma_aux ci hKO
  refine ⟨mu, MmuDual, instACG', instMod', instLRM', instLM', hMmuDualO, hContra,
    ι.comp q, ?_⟩
  intro h_zero
  apply hq_ne
  ext k
  have h1 : ι (q k) = 0 := by
    have := LieModuleHom.congr_fun h_zero k
    simpa using this
  have h2 : ι (q k) = ι 0 := by rw [h1, map_zero]
  exact hι_inj h2

/--
[finite_length_hom_vanishing_implies_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma finite_length_hom_vanishing_implies_zero
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {ci : CartanInvolution rd}
  {K : Type uCatO}
  [AddCommGroup K]
  [Module R K]
  [LieRingModule 𝔤 K]
  [LieModule R 𝔤 K]
-- given
  (hKO : IsCategoryO Δ rd K)
  (hHomVanish : ∀ (mu : Δ.𝔥 →ₗ[R] R) (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual] [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual] (hMmuDualO : IsCategoryO Δ rd MmuDual) (_ : IsContragredientVerma rd MmuDual mu hMmuDualO), ∀ (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f = 0) :
-- imply
  ∀ (k : K), k = 0 := by
-- proof
  by_contra h
  push Not at h
  obtain ⟨k, hk⟩ := h
  haveI : Nontrivial K := ⟨⟨k, 0, hk⟩⟩
  obtain ⟨mu, MmuDual, inst1, inst2, inst3, inst4, hMmuDualO, hContra, f, hf_ne⟩ :=
    CategoryO.nonzero_admits_hom_to_contragredient_verma ci hKO
  exact hf_ne (@hHomVanish mu MmuDual inst1 inst2 inst3 inst4 hMmuDualO hContra f)

/--
[cartan_standard_filtration_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma cartan_standard_filtration_decomposition
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam mu : Δ.𝔥 →ₗ[R] R}
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
-- given
  (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S → standardFiltrationMultiplicity rd wg lam nu = 0 ∨ compositionMultiplicity rd wg nu mu = 0) :
-- imply
  cartanMatrixEntry rd wg lam mu = S.sum (fun nu => standardFiltrationMultiplicity rd wg lam nu * compositionMultiplicity rd wg nu mu) := by
-- proof
  have hS' : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
    compositionMultiplicity rd wg nu lam = 0 ∨
    compositionMultiplicity rd wg nu mu = 0 := by
    intro nu hnu
    have h := hS nu hnu
    rwa [bgg_reciprocity_raw rd wg lam nu] at h
  change cartanMultiplicity rd wg lam mu = _
  rw [corollary_20_7 rd wg lam mu S hS']
  congr 1
  ext nu
  rw [bgg_reciprocity_raw rd wg lam nu]

/--
[cartan_matrix_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma cartan_matrix_factorization
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam mu : Δ.𝔥 →ₗ[R] R}
  {S : Finset (Δ.𝔥 →ₗ[R] R)}
-- given
  (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S → compositionMultiplicity rd wg nu lam = 0 ∨ compositionMultiplicity rd wg nu mu = 0) :
-- imply
  cartanMatrixEntry rd wg lam mu = S.sum (fun nu => compositionMultiplicity rd wg nu lam * compositionMultiplicity rd wg nu mu) := by
-- proof
  have hS' : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
    standardFiltrationMultiplicity rd wg lam nu = 0 ∨
    compositionMultiplicity rd wg nu mu = 0 := by
    intro nu hnu
    have h := hS nu hnu
    rwa [← bgg_reciprocity_raw rd wg lam nu] at h
  rw [cartan_standard_filtration_decomposition rd wg lam mu S hS']
  congr 1
  ext nu
  rw [bgg_reciprocity_raw rd wg lam nu]

/--
[bgg_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma bgg_theorem
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam mu : Δ.𝔥 →ₗ[R] R}
-- given
  (hcomp : compositionMultiplicity rd wg lam mu ≠ 0) :
-- imply
  BruhatLE rd mu lam :=
-- proof
  bgg_theorem_bruhat_order R 𝔤 Δ rd wg lam mu hcomp

/--
[UEA_induction_on_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma UEA_induction_on_gen_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  {C : UniversalEnvelopingAlgebra R L → Prop}
  {u : UniversalEnvelopingAlgebra R L}
-- given
  (h_alg : ∀ r : R, C (algebraMap R _ r))
  (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b)) :
-- imply
  C u := by
-- proof
  apply UEA_induction_on_gen R 𝔤 u h_alg h_ι h_mul h_add

/--
[lieModuleHom_ueaSubalg_compat_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma lieModuleHom_ueaSubalg_compat_gen_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {f : M →ₗ⁅R, 𝔤⁆ N}
  {u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
-- proof
  apply lieModuleHom_ueaSubalg_compat_gen R 𝔤 f u m

/--
[UEA_induction_on_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma UEA_induction_on_local_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [LieRing L]
  [LieAlgebra R L]
  {C : UniversalEnvelopingAlgebra R L → Prop}
  {u : UniversalEnvelopingAlgebra R L}
-- given
  (h_alg : ∀ r : R, C (algebraMap R _ r))
  (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b)) :
-- imply
  C u := by
-- proof
  apply UEA_induction_on_local R 𝔤 u h_alg h_ι h_mul h_add

/--
[lieModuleHom_ueaSubalg_compat_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean)
-/
@[path]
private lemma lieModuleHom_ueaSubalg_compat_local_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {f : M →ₗ⁅R, 𝔤⁆ N}
  {u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
-- proof
  apply lieModuleHom_ueaSubalg_compat_local R 𝔤 f u m


-- created on 2026-10-23
-- updated on 2026-10-26
