import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite Topology
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma top_le_preimage_iff
  {Y : (Scheme : Type 1)}
  (q : Spec (CommRingCat.of ℂ) ⟶ Y)
  (U : Y.Opens) :
  -- imply
  ⊤ ≤ (TopologicalSpace.Opens.map q.base).obj U ↔ q.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  -- proof
  constructor
  ·
    intro h
    apply h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  ·
    intro h p _
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    apply h

private lemma val_fromSpec
  {M : (Scheme : Type 1)}
  {U : M.Opens}
  (σ : RingHom (M.presheaf.obj (op U)) ℂ)
  (a : M.presheaf.obj (op U))
  -- given
  (hU : IsAffineOpen U)
  (h : ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec).base).obj U) :
  -- imply
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec).appLE U ⊤ h) a) = σ a := by
  -- proof
  rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self]
  have e1 : (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
    (Spec.map (CommRingCat.ofHom σ)).appLE ((TopologicalSpace.Opens.map hU.fromSpec.base).obj U) ⊤ h =
    (Spec.map (CommRingCat.ofHom σ)).appTop := by
    rw [Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have key : (((Scheme.ΓSpecIso (M.presheaf.obj (op U))).inv ≫
      (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op) ≫
      (Spec.map (CommRingCat.ofHom σ)).appLE ((TopologicalSpace.Opens.map hU.fromSpec.base).obj U) ⊤ h) ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = CommRingCat.ofHom σ := by
    simp only [Category.assoc]
    rw [← Category.assoc ((Spec (M.presheaf.obj (op U))).presheaf.map _), e1, Scheme.ΓSpecIso_naturality]
    erw [Iso.inv_hom_id_assoc]
  have := congrFun (congrArg (fun k => (CommRingCat.Hom.hom k : _ → _)) key) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
  apply this

private lemma top_le_preimage_basicOpen_iff
  {M : (Scheme : Type 1)}
  {U : M.Opens}
  (σ : RingHom (M.presheaf.obj (op U)) ℂ)
  (b : M.presheaf.obj (op U))
  -- given
  (hU : IsAffineOpen U) :
  -- imply
  ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec).base).obj (M.basicOpen b) ↔ σ b ≠ 0 := by
  -- proof
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_basicOpen, top_le_preimage_iff]
  change PrimeSpectrum.comap σ (IsLocalRing.closedPoint ℂ) ∈ PrimeSpectrum.basicOpen b ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change σ b ∉ IsLocalRing.maximalIdeal ℂ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]

private lemma val_map
  {G : (Scheme : Type 1)}
  (p : Spec (CommRingCat.of ℂ) ⟶ G)
  {U U' : G.Opens}
  (s : G.presheaf.obj (op U'))
  -- given
  (hle : U ≤ U')
  (h : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj U)
  (h' : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj U') :
  -- imply
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ h) (G.presheaf.map (homOfLE hle).op s)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U' ⊤ h') s) := by
  -- proof
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/--
[AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn.lean)
-/
@[path]
private lemma main
  (M : (Scheme : Type 1))
  (U : M.Opens)
  (D : Set ℂ)
  (σ : ℂ → RingHom (M.presheaf.obj (op U)) ℂ)
  (U' : M.Opens)
  (s : M.presheaf.obj (op U'))
  -- given
  (hU : IsAffineOpen U)
  (hD : IsOpen D)
  (hσ : ∀ a : M.presheaf.obj (op U), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ ∀ w ∈ D, σ w a = F w) :
  -- imply
  IsOpen {w : ℂ | w ∈ D ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).base).obj U'} ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {w : ℂ | w ∈ D ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).base).obj U'} ∧ ∀ (w : ℂ), w ∈ D → ∀ (hw : ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).base).obj U'), G w = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ hw) s) := by
  -- proof
  classical
  let pre (w : ℂ) (V : M.Opens) :=
    (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).base).obj V
  set p : ℂ → (Spec (CommRingCat.of ℂ) ⟶ M) := fun w => Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec with hp
  set S : Set ℂ := {w : ℂ | w ∈ D ∧ ⊤ ≤ pre w U'} with hS
  choose Fa hFa hFaval using hσ
  have hpU : ∀ w, ⊤ ≤ pre w U := by
    intro w
    unfold pre
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    simp
  have hloc : ∀ w₀ ∈ S, ∃ (b a : M.presheaf.obj (op U)) (k : ℕ), M.basicOpen b ≤ U' ∧ σ w₀ b ≠ 0 ∧ ∀ w ∈ D, σ w b ≠ 0 → ∃ hw : ⊤ ≤ pre w U', (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ hw) s) * (σ w b) ^ k = σ w a := by
    rintro w₀ ⟨hw₀D, hw₀⟩
    set x₀ : M := (Spec.map (CommRingCat.ofHom (σ w₀)) ≫ hU.fromSpec).base (IsLocalRing.closedPoint ℂ) with hx₀
    have hx₀U' : x₀ ∈ U' := (top_le_preimage_iff _ _).mp hw₀
    have hx₀U : x₀ ∈ U := (top_le_preimage_iff _ _).mp (hpU w₀)
    obtain ⟨b, hbU', hx₀b⟩ := hU.exists_basicOpen_le ⟨x₀, hx₀U'⟩ hx₀U
    have hb0 : σ w₀ b ≠ 0 := (top_le_preimage_basicOpen_iff (σ w₀) b hU).mp ((top_le_preimage_iff _ _).mpr hx₀b)
    let _ := hU.isLocalization_basicOpen b
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hak⟩ := IsLocalization.surj (Submonoid.powers b) (M.presheaf.map (homOfLE hbU').op s)
    refine ⟨b, a, k, hbU', hb0, fun w hwD hwb => ?_⟩
    have hwb' : ⊤ ≤ pre w (M.basicOpen b) := (top_le_preimage_basicOpen_iff (σ w) b hU).mpr hwb
    have hwU' : ⊤ ≤ pre w U' := (top_le_preimage_iff _ _).mpr (hbU' ((top_le_preimage_iff _ _).mp hwb'))
    refine ⟨hwU', ?_⟩
    have hev := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE (M.basicOpen b) ⊤ hwb') t)) hak
    simp only [map_mul, map_pow] at hev
    have halg : ∀ r : M.presheaf.obj (op U), algebraMap _ (M.presheaf.obj (op (M.basicOpen b))) r =
        M.presheaf.map (homOfLE (M.basicOpen_le b)).op r := fun r => rfl
    rw [halg, halg, val_map _ _ hbU' hwb' hwU', val_map _ _ (M.basicOpen_le b) hwb' (hpU w),
      val_map _ _ (M.basicOpen_le b) hwb' (hpU w), val_fromSpec (hU := hU), val_fromSpec (hU := hU)] at hev
    apply hev
  constructor
  ·
    rw [isOpen_iff_mem_nhds]
    intro w₀ hw₀
    obtain ⟨b, a, k, hbU', hb0, hval⟩ := hloc w₀ hw₀
    have hcont : ContinuousOn (fun w => Fa b w) D := (hFa b).continuousOn
    have hnb : {w | w ∈ D ∧ Fa b w ≠ 0} ∈ 𝓝 w₀ := by
      have ho : IsOpen ({w | w ∈ D ∧ Fa b w ≠ 0}) := by
        have : {w | w ∈ D ∧ Fa b w ≠ 0} = D ∩ (fun w => Fa b w) ⁻¹' {z | z ≠ 0} := by
          ext w
          simp
        rw [this]
        apply hcont.isOpen_inter_preimage hD isOpen_ne
      refine ho.mem_nhds ⟨hw₀.1, ?_⟩
      rwa [← hFaval b w₀ hw₀.1]
    refine Filter.mem_of_superset hnb ?_
    rintro w ⟨hwD, hwb⟩
    rw [← hFaval b w hwD] at hwb
    refine ⟨hwD, (hval w hwD hwb).1⟩
  ·
    let G : ℂ → ℂ := fun w => if h : w ∈ D ∧ ⊤ ≤ pre w U' then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ h.2) s) else 0
    refine ⟨G, ?_, ?_⟩
    ·
      intro w₀ hw₀
      obtain ⟨b, a, k, hbU', hb0, hval⟩ := hloc w₀ hw₀
      have hnb : ∀ᶠ w in 𝓝 w₀, w ∈ D ∧ Fa b w ≠ 0 := by
        have hcont : ContinuousOn (fun w => Fa b w) D := (hFa b).continuousOn
        have ho : IsOpen ({w | w ∈ D ∧ Fa b w ≠ 0}) := by
          have : {w | w ∈ D ∧ Fa b w ≠ 0} = D ∩ (fun w => Fa b w) ⁻¹' {z | z ≠ 0} := by
            ext w
            simp
          rw [this]
          apply hcont.isOpen_inter_preimage hD isOpen_ne
        refine ho.mem_nhds ⟨hw₀.1, ?_⟩
        rwa [← hFaval b w₀ hw₀.1]
      have heq : ∀ᶠ w in 𝓝 w₀, G w = Fa a w / Fa b w ^ k := by
        filter_upwards [hnb] with w hw
        obtain ⟨hwD, hwb⟩ := hw
        have hwb' : σ w b ≠ 0 := by
          rwa [hFaval b w hwD]
        obtain ⟨hwU', hv⟩ := hval w hwD hwb'
        unfold G
        rw [dite_eq_left ⟨hwD, hwU'⟩, eq_div_iff (pow_ne_zero _ hwb), ← hFaval a w hwD, ← hFaval b w hwD]
        apply hv
      have hdiff : DifferentiableAt ℂ (fun w => Fa a w / Fa b w ^ k) w₀ := by
        have hDn : D ∈ 𝓝 w₀ := hD.mem_nhds hw₀.1
        refine ((hFa a).differentiableAt hDn).div (((hFa b).differentiableAt hDn).pow k) ?_
        refine pow_ne_zero _ ?_
        rwa [← hFaval b w₀ hw₀.1]
      refine (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
    ·
      intro w hwD hw
      beta_reduce
      unfold G
      rw [dite_eq_left ⟨hwD, hw⟩]


-- created on 2026-10-20
