import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso.lean)
-/
@[path]
private lemma main
  (q : ℕ) [Fact q.Prime]
  (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  [MulDistribMulAction G (Units ↥L)]
  (hcompat : ∀ (g : G) (u : Units ↥L), ((g • u : Units ↥L) : L) = g • (u : L))
  (N : Subgroup G) [N.Normal] :
  -- imply
  ∃ (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L') (_ : MulSemiringAction (G ⧸ N) L') (_ : FaithfulSMul (G ⧸ N) L') (_ : MulDistribMulAction (G ⧸ N) (Units ↥L')), (∀ (g : G ⧸ N) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧ (∀ (g : G ⧸ N) (u : Units ↥L'), ((g • u : Units ↥L') : L') = g • (u : L')) ∧ Nonempty ((Rep.ofMulDistribMulAction G (Units ↥L)).quotientToInvariants N ≅ Rep.ofMulDistribMulAction (G ⧸ N) (Units ↥L')) := by
  -- proof
  classical
  let _ : SMulCommClass N ℚ_[q] L := ⟨fun n c x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    apply hG n c⟩
  let E : IntermediateField ℚ_[q] L := FixedPoints.intermediateField N
  have hmemE : ∀ x : L, x ∈ E ↔ ∀ n : N, n • x = x := fun x => Iff.rfl
  have hstab : ∀ (g : G) (x : L), x ∈ E → g • x ∈ E := fun g x hx => by
    rw [hmemE] at hx ⊢
    intro n
    have h := hx ⟨g⁻¹ * n * g, Subgroup.Normal.conj_mem' inferInstance _ n.2 g⟩
    change (g⁻¹ * (n : G) * g) • x = x at h
    calc
      _ = g • ((g⁻¹ * (n : G) * g) • x) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
      _ = g • x := by
        rw [h]
  have hglue : ∀ (x : E) (g₁ g₂ : G), g₁⁻¹ * g₂ ∈ N → g₁ • (x : L) = g₂ • (x : L) := by
    intro x g₁ g₂ hn
    have := Iff.mp (hmemE x) x.2 ⟨g₁⁻¹ * g₂, hn⟩
    change (g₁⁻¹ * g₂) • (x : L) = x at this
    calc
      _ = g₁ • ((g₁⁻¹ * g₂) • (x : L)) := by
        rw [this]
      _ = g₂ • (x : L) := by
        rw [← mul_smul, mul_inv_cancel_left]
  let act : G ⧸ N → E → E := fun c x => Quotient.liftOn' c (fun g => (⟨g • (x : L), hstab g x x.2⟩ : E))
    (fun g₁ g₂ h12 => Subtype.ext (hglue x g₁ g₂ (QuotientGroup.leftRel_apply.mp h12)))
  have hact : ∀ (g : G) (x : E), ((act (g : G ⧸ N) x : E) : L) = g • (x : L) := fun _ _ => rfl
  let instE : MulSemiringAction (G ⧸ N) E :=
    { smul := act
      one_smul := fun x => by
        change ((act ((1 : G) : G ⧸ N) x : E) : L) = x
        rw [hact, one_smul]
      mul_smul := fun c₁ c₂ x => by
        refine QuotientGroup.induction_on c₁ ?_
        intro g₁
        refine QuotientGroup.induction_on c₂ ?_
        intro g₂
        apply Subtype.ext
        change ((act ((g₁ * g₂ : G) : G ⧸ N) x : E) : L) = ((act (g₁ : G ⧸ N) (act (g₂ : G ⧸ N) x) : E) : L)
        rw [hact, hact, hact, mul_smul]
      smul_zero := fun c => by
        refine QuotientGroup.induction_on c ?_
        intro g
        apply Subtype.ext
        change ((act (g : G ⧸ N) 0 : E) : L) = 0
        rw [hact]
        apply smul_zero g
      smul_add := fun c x y => by
        refine QuotientGroup.induction_on c ?_
        intro g
        apply Subtype.ext
        change ((act (g : G ⧸ N) (x + y) : E) : L) = ((act (g : G ⧸ N) x : E) : L) + ((act (g : G ⧸ N) y : E) : L)
        rw [hact, hact, hact]
        apply smul_add g (x : L) (y : L)
      smul_one := fun c => by
        refine QuotientGroup.induction_on c ?_
        intro g
        apply Subtype.ext
        change ((act (g : G ⧸ N) 1 : E) : L) = 1
        rw [hact]
        apply smul_one g
      smul_mul := fun c x y => by
        refine QuotientGroup.induction_on c ?_
        intro g
        apply Subtype.ext
        change ((act (g : G ⧸ N) (x * y) : E) : L) = ((act (g : G ⧸ N) x : E) : L) * ((act (g : G ⧸ N) y : E) : L)
        rw [hact, hact, hact]
        apply smul_mul' g (x : L) (y : L) }
  have hsmulE : ∀ (g : G) (x : E), (((g : G ⧸ N) • x : E) : L) = g • (x : L) := fun _ _ => rfl
  let L' : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.lift E
  let ε : E ≃ₐ[ℚ_[q]] L' := IntermediateField.liftAlgEquiv E
  let instL' : MulSemiringAction (G ⧸ N) L' :=
    { smul := fun c y => ε (c • ε.symm y)
      one_smul := fun y => by
        change ε ((1 : G ⧸ N) • ε.symm y) = y
        rw [one_smul, AlgEquiv.apply_symm_apply]
      mul_smul := fun c₁ c₂ y => by
        change ε ((c₁ * c₂) • ε.symm y) = ε (c₁ • ε.symm (ε (c₂ • ε.symm y)))
        rw [AlgEquiv.symm_apply_apply, mul_smul]
      smul_zero := fun c => by
        change ε (c • ε.symm 0) = 0
        rw [map_zero, smul_zero, map_zero]
      smul_add := fun c a b => by
        change ε (c • ε.symm (a + b)) = ε (c • ε.symm a) + ε (c • ε.symm b)
        rw [map_add, smul_add, map_add]
      smul_one := fun c => by
        change ε (c • ε.symm 1) = 1
        rw [map_one, smul_one, map_one]
      smul_mul := fun c a b => by
        change ε (c • ε.symm (a * b)) = ε (c • ε.symm a) * ε (c • ε.symm b)
        rw [map_mul, smul_mul', map_mul] }
  have hsmulL' : ∀ (c : G ⧸ N) (y : L'), c • y = ε (c • ε.symm y) := fun _ _ => rfl
  let instFD : FiniteDimensional ℚ_[q] L' := LinearEquiv.finiteDimensional ε.toLinearEquiv
  have hG' : ∀ (c : G ⧸ N) (x : ℚ_[q]), c • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x := by
    intro c x
    refine QuotientGroup.induction_on c ?_
    intro g
    rw [hsmulL', AlgEquiv.commutes]
    have : ((g : G ⧸ N) • algebraMap ℚ_[q] E x : E) = algebraMap ℚ_[q] E x := by
      apply Subtype.ext
      rw [hsmulE]
      apply hG g x
    rw [this, AlgEquiv.commutes]
  let instU : MulDistribMulAction (G ⧸ N) (Units ↥L') := Units.mulDistribMulActionRight
  have hcompat' : ∀ (c : G ⧸ N) (u : Units ↥L'), ((c • u : Units ↥L') : L') = c • (u : L') := fun _ _ => rfl
  let instF : FaithfulSMul (G ⧸ N) L' := ⟨fun {c₁ c₂} h => by
    refine QuotientGroup.induction_on c₁ ?_
    intro g₁
    refine QuotientGroup.induction_on c₂ ?_
    intro g₂
    rw [QuotientGroup.eq]
    have hE : ∀ x : L, x ∈ E → (g₁⁻¹ * g₂) • x = x := by
      intro x hx
      have hy := h (ε ⟨x, hx⟩)
      rw [hsmulL', hsmulL', AlgEquiv.symm_apply_apply] at hy
      have hy'' := congrArg (fun z : E => (z : L)) (ε.injective hy)
      simp only [hsmulE] at hy''
      rw [mul_smul, ← hy'', ← mul_smul, inv_mul_cancel, one_smul]
    let θ := FixedPoints.toAlgAutMulEquiv G L
    have hθ : ∀ (g : G) (x : L), θ g x = g • x := fun _ _ => rfl
    let N' : Subgroup (L ≃ₐ[FixedPoints.subfield G L] L) := N.map θ.toMonoidHom
    have hfix : θ (g₁⁻¹ * g₂) ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N') := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [hθ]
      apply hE
      rw [hmemE]
      intro n
      have := hx ⟨θ n, n, n.2, rfl⟩
      apply this
    rw [IntermediateField.fixingSubgroup_fixedField] at hfix
    obtain ⟨n, hn, hn'⟩ := hfix
    have : n = g₁⁻¹ * g₂ := θ.injective hn'
    rw [← this]
    apply hn⟩
  let A := Rep.ofMulDistribMulAction G (Units ↥L)
  let ρN : Representation ℤ N (Additive (Units ↥L)) := A.ρ.comp N.subtype
  let uof : ρN.invariants → (Units ↥L) := fun x => Additive.toMul (show Additive (Units ↥L) from x.1)
  have huN : ∀ (x : ρN.invariants) (n : N), (n : G) • uof x = uof x := fun x n => x.2 n
  have huE : ∀ x : ρN.invariants, ((uof x : Units ↥L) : L) ∈ E := fun x => by
    rw [hmemE]
    intro n
    change (n : G) • ((uof x : Units ↥L) : L) = _
    rw [← hcompat, huN]
  have huE' : ∀ x : ρN.invariants, (((uof x)⁻¹ : Units ↥L) : L) ∈ E := fun x => by
    rw [hmemE]
    intro n
    change (n : G) • (((uof x)⁻¹ : Units ↥L) : L) = _
    rw [← hcompat, smul_inv', huN]
  let uE : ρN.invariants → Eˣ := fun x =>
    ⟨⟨_, huE x⟩, ⟨_, huE' x⟩, Subtype.ext (uof x).mul_inv, Subtype.ext (uof x).inv_mul⟩
  let fwdU : ρN.invariants → (Units ↥L') := fun x => Units.map (ε : E →* L') (uE x)
  have hfwdU : ∀ x, ((fwdU x : Units ↥L') : L') = ε ⟨((uof x : Units ↥L) : L), huE x⟩ := fun _ => rfl
  let ψ : L' →* L := (E.val : E →ₐ[ℚ_[q]] L).toRingHom.toMonoidHom.comp
    (ε.symm : L' ≃ₐ[ℚ_[q]] E).toRingEquiv.toRingHom.toMonoidHom
  have hψ : ∀ y : L', ψ y = ((ε.symm y : E) : L) := fun _ => rfl
  have hψE : ∀ y : L', ψ y ∈ E := fun y => (ε.symm y).2
  let bwd : Additive (Units ↥L') → ρN.invariants := fun w =>
    ⟨(Additive.ofMul (Units.map ψ (Additive.toMul w)) : Additive (Units ↥L)), fun n => by
      change Additive.ofMul ((n : G) • Units.map ψ (Additive.toMul w)) = Additive.ofMul (Units.map ψ (Additive.toMul w))
      congr 1
      apply Units.ext
      rw [hcompat, Units.coe_map, hψ]
      apply Iff.mp (hmemE _) (ε.symm _).2 n⟩
  have hfwd_add : ∀ x y, fwdU (x + y) = fwdU x * fwdU y := fun x y => by
    apply Units.ext
    rw [Units.val_mul, hfwdU (x + y), hfwdU x, hfwdU y, ← map_mul]
    congr 1
  let fwdL : ρN.invariants →ₗ[ℤ] Additive (Units ↥L') :=
    (({ toFun := fun x => Additive.ofMul (fwdU x)
        map_zero' := by
          change Additive.ofMul (fwdU 0) = Additive.ofMul 1
          apply congrArg Additive.ofMul
          apply Units.ext
          rw [hfwdU, Units.val_one, ← map_one ε]
          rfl
        map_add' := fun x y => by
          change Additive.ofMul (fwdU (x + y)) = Additive.ofMul (fwdU x) + Additive.ofMul (fwdU y)
          rw [hfwd_add]
          rfl } : ρN.invariants →+ Additive (Units ↥L'))).toIntLinearMap
  have hfwdL : ∀ x, fwdL x = Additive.ofMul (fwdU x) := fun _ => rfl
  have hleft : ∀ x, bwd (fwdL x) = x := fun x => by
    apply Subtype.ext
    change Additive.ofMul (Units.map ψ (fwdU x)) = x.1
    have : Units.map ψ (fwdU x) = uof x := by
      apply Units.ext
      rw [Units.coe_map, hfwdU, hψ, AlgEquiv.symm_apply_apply]
    rw [this]
    rfl
  have hright : ∀ w, fwdL (bwd w) = w := fun w => by
    rw [hfwdL]
    change Additive.ofMul (fwdU (bwd w)) = Additive.ofMul (Additive.toMul w)
    refine congrArg Additive.ofMul (Units.ext ?_)
    rw [hfwdU]
    have : (⟨((uof (bwd w) : Units ↥L) : L), huE (bwd w)⟩ : E) = ε.symm (Additive.toMul w : Units ↥L') := by
      apply Subtype.ext
      change ψ _ = _
      rw [hψ]
    rw [this, AlgEquiv.apply_symm_apply]
  have hinter : ∀ c : G ⧸ N, LinearMap.comp fwdL ((A.ρ.quotientToInvariants N) c) = LinearMap.comp ((Representation.ofMulDistribMulAction (G ⧸ N) (Units ↥L')) c) fwdL := by
    intro c
    refine QuotientGroup.induction_on c ?_
    intro g
    apply LinearMap.ext
    intro x
    show fwdL ((A.ρ.quotientToInvariants N) (g : G ⧸ N) x) = (Representation.ofMulDistribMulAction (G ⧸ N) (Units ↥L')) (g : G ⧸ N) (fwdL x)
    rw [hfwdL, hfwdL, Representation.ofMulDistribMulAction_apply_apply]
    change Additive.ofMul (fwdU _) = Additive.ofMul ((g : G ⧸ N) • fwdU x)
    refine congrArg Additive.ofMul (Units.ext ?_)
    rw [hcompat', hsmulL', hfwdU, hfwdU, AlgEquiv.symm_apply_apply]
    refine congrArg ε (Subtype.ext ?_)
    rw [hsmulE]
    change ((uof ((A.ρ.quotientToInvariants N) (g : G ⧸ N) x) : Units ↥L) : L) = g • ((uof x : Units ↥L) : L)
    rw [← hcompat]
    rfl
  let EQ : (A.ρ.quotientToInvariants N).Equiv (Representation.ofMulDistribMulAction (G ⧸ N) (Units ↥L')) :=
    Representation.Equiv.mk' ⟨fwdL, hinter⟩ bwd hleft hright
  refine ⟨L', instFD, instL', instF, instU, hG', hcompat', ⟨Rep.mkIso EQ⟩⟩


-- created on 2026-10-20
