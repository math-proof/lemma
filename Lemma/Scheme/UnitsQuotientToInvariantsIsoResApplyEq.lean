import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma apply_algebraMap_of_mem {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) {s : M ≃ₐ[E] M} (hs : s ∈ S) (y : L) : s (algebraMap L M y) = algebraMap L M y := by
  rw [← hι s y, (QuotientGroup.eq_one_iff s).2 hs, map_one, AlgEquiv.one_apply]
private lemma mem_of_forall_apply_algebraMap {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) {g : M ≃ₐ[E] M} (hg : ∀ y : L, g (algebraMap L M y) = algebraMap L M y) : g ∈ S := by
  rw [← QuotientGroup.eq_one_iff, ← MulEquiv.map_eq_one_iff ι]
  ext y
  apply (algebraMap L M).injective
  rw [hι, hg, AlgEquiv.one_apply]
private lemma exists_algebraMap_eq_of_forall {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M] (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) (m : M) (hm : ∀ s ∈ S, s m = m) : ∃ y : L, algebraMap L M y = m := by
  let K : IntermediateField E M := (IsScalarTower.toAlgHom E L M).fieldRange
  have hle : K.fixingSubgroup ≤ S := by
    intro g hg
    refine mem_of_forall_apply_algebraMap S ι hι fun y => ?_
    apply (mem_fixingSubgroup_iff (M ≃ₐ[E] M)).1 hg _ ⟨y, rfl⟩
  have hmem : m ∈ IntermediateField.fixedField S := (IntermediateField.mem_fixedField_iff S m).2 hm
  have hK : m ∈ K := by
    rw [← IsGalois.fixedField_fixingSubgroup K]
    apply IntermediateField.fixedField_antitone hle hmem
  obtain ⟨y, hy⟩ := hK
  exact ⟨y, hy⟩
private lemma map_mem_invariants {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) (a : Units L) : (Additive.ofMul (Units.map (algebraMap L M : L →* M) a) : Additive (Units M)) ∈ Representation.invariants ((Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (Units M)).ρ.comp S.subtype) := by
  intro s
  change Additive.ofMul ((s : M ≃ₐ[E] M) • Units.map (algebraMap L M : L →* M) a) = _
  refine congrArg Additive.ofMul (Units.ext ?_)
  rw [hactM, Units.coe_map, MonoidHom.coe_coe, apply_algebraMap_of_mem S ι hι s.2]
private noncomputable def toInvariants {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L)) (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) : Representation.IntertwiningMap ((Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (Units L)).ρ.comp ι.toMonoidHom) ((Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (Units M)).ρ.quotientToInvariants S) where
  toLinearMap := LinearMap.codRestrict _ (MonoidHom.toAdditive (Units.map (algebraMap L M : L →* M))).toIntLinearMap (fun a => map_mem_invariants hactM S ι hι (Additive.toMul a))
  isIntertwining' := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change (Additive.ofMul (Units.map (algebraMap L M : L →* M) (ι (QuotientGroup.mk g) • Additive.toMul (show Additive (Units L) from a))) : Additive (Units M)) = Additive.ofMul (g • Units.map (algebraMap L M : L →* M) (Additive.toMul (show Additive (Units L) from a)))
    refine congrArg Additive.ofMul (Units.ext ?_)
    rw [Units.coe_map, MonoidHom.coe_coe, hactL, hι, hactM, Units.coe_map, MonoidHom.coe_coe]
private lemma toInvariants_apply {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L)) (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) (a : Additive (Units L)) : (toInvariants hactL hactM S ι hι a).1 = Additive.ofMul (Units.map (algebraMap L M : L →* M) (Additive.toMul a)) := rfl
private lemma toInvariants_bijective {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L)) (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) : Function.Bijective (toInvariants hactL hactM S ι hι) := by
  constructor
  ·
    intro a b h
    have h' := congrArg (fun x => ((Additive.toMul (Subtype.val x) : Units M) : M)) h
    simp only [toInvariants_apply, toMul_ofMul, Units.coe_map, MonoidHom.coe_coe] at h'
    apply Additive.toMul.injective (Units.ext ((algebraMap L M).injective h'))
  ·
    intro hvpair
    obtain ⟨v', hv⟩ := hvpair
    let v : Units M := Additive.toMul (show Additive (Units M) from v')
    have hfix : ∀ s ∈ S, s (v : M) = v := by
      intro s hs
      have h1 := hv ⟨s, hs⟩
      change Additive.ofMul (s • v) = Additive.ofMul v at h1
      have h2 := congrArg (fun x : Additive (Units M) => ((Additive.toMul x : Units M) : M)) h1
      simpa only [toMul_ofMul, hactM] using h2
    obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_forall S ι hι _ hfix
    have hy0 : y ≠ 0 := by
      intro h0
      subst h0
      rw [map_zero] at hy
      apply v.ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), Subtype.ext ?_⟩
    rw [toInvariants_apply]
    change Additive.ofMul _ = Additive.ofMul v
    refine congrArg Additive.ofMul (Units.ext ?_)
    simp at hy ⊢
    apply hy
private noncomputable def iso {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L)) (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) : (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (Units M)).quotientToInvariants S ≅ Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (Units L)) :=
  (Rep.mkIso ((toInvariants hactL hactM S ι hι).ofBijective (toInvariants_bijective hactL hactM S ι hι))).symm
private lemma iso_inv_hom_apply {E L M : Type} [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)] (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L)) (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M)) (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L)) (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) (a : Units L) : ((iso hactL hactM S ι hι).inv.hom (Additive.ofMul a)).1 = Additive.ofMul (Units.map (algebraMap L M : L →* M) a) := rfl
/--
[IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq.lean)
-/
@[path]
private lemma main
  (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M] [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M] [MulDistribMulAction (L ≃ₐ[E] L) (Units L)] [MulDistribMulAction (M ≃ₐ[E] M) (Units M)]
  (S : Subgroup (M ≃ₐ[E] M)) [S.Normal]
  (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
  -- given
  (hactL : ∀ (g : L ≃ₐ[E] L) (a : Units L), ((g • a : Units L) : L) = g (a : L))
  (hactM : ∀ (g : M ≃ₐ[E] M) (a : Units M), ((g • a : Units M) : M) = g (a : M))
  (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) :
  -- imply
  ∃ e : (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (Units M)).quotientToInvariants S ≅ Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (Units L)), ∀ a : Units L, (e.inv.hom (Additive.ofMul a)).1 = Additive.ofMul (Units.map (algebraMap L M : L →* M) a) :=
  ⟨iso hactL hactM S ι hι, fun a => iso_inv_hom_apply hactL hactM S ι hι a⟩


-- created on 2026-10-20
