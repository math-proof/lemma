import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian.Part2


/--
[GaloisAction.vsub_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
lemma GaloisAction.vsub_compat
  {G : Type u}
  [Group G]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {C_pts : Type u}
  [AddTorsor E_pts C_pts]
  {ga : GaloisAction G E_pts C_pts}
  {σ : G}
  {P Q : C_pts}
-- given
  (hga : ga.IsEquivariant) :
-- imply
  ga.actE σ (P -ᵥ Q) = (ga.actC σ P) -ᵥ (ga.actC σ Q) := by
-- proof
  have h := hga σ (P -ᵥ Q) Q
  rw [vsub_vadd] at h
  rw [h, vadd_vsub]

/--
[torsor_basepoint_galois_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
lemma torsor_basepoint_galois_compat
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {G : Type u}
  [Group G]
  {ga : GaloisAction G E_pts C_pts}
  [AddTorsor E_pts C_pts]
  {Q₀ : C_pts}
-- given
  (hga : ga.IsEquivariant) :
-- imply
  IsGaloisCompatible ga (Equiv.vaddConst Q₀).symm := by
-- proof
  intro σ
  use Q₀ -ᵥ (ga.actC σ Q₀)
  intro Q
  show ga.actE σ (Q -ᵥ Q₀) = (ga.actC σ Q -ᵥ Q₀) + (Q₀ -ᵥ ga.actC σ Q₀)
  rw [ga.vsub_compat hga σ Q Q₀]
  rw [← vsub_add_vsub_cancel (ga.actC σ Q) Q₀ (ga.actC σ Q₀)]

/--
[galois_action_of_k_torsor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
lemma galois_action_of_k_torsor
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {C_pts : Type u}
-- given
  (hT : IsETorsor k W E_pts C_pts) :
-- imply
  ∃ (ga : GaloisAction (AbsGaloisGroup k) E_pts C_pts), @GaloisAction.IsEquivariant _ _ _ _ _ hT.toAddTorsor ga := by
-- proof
  letI := hT.toAddTorsor
  refine ⟨⟨fun _ => AddEquiv.refl E_pts, fun _ => Equiv.refl C_pts⟩, ?_⟩
  intro σ g c
  simp

/--
[isETorsor_imp_isJacobianOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
lemma isETorsor_imp_isJacobianOf
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
-- given
  (hT : IsETorsor k W E_pts C_pts) :
-- imply
  IsJacobianOf k W E_pts C_pts := by
-- proof
  constructor
  ·
    exact hT.genusOne
  ·
    obtain ⟨ga, hga⟩ := galois_action_of_k_torsor k W E_pts C_pts hT
    letI := hT.toAddTorsor
    obtain ⟨Q₀⟩ := hT.genusOne.nonempty_over_closure
    let φ := (Equiv.vaddConst Q₀).symm
    exact ⟨ga, φ, torsor_basepoint_galois_compat ga hga Q₀⟩

/--
[eTorsor_iff_jacobian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
lemma eTorsor_iff_jacobian
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic] :
-- imply
  Nonempty (IsETorsor k W E_pts C_pts) ↔ IsJacobianOf k W E_pts C_pts :=
-- proof
  ⟨fun ⟨hT⟩ => isETorsor_imp_isJacobianOf hT,
    fun hJ => ⟨isJacobianOf_imp_isETorsor hJ⟩⟩

/--
[isActionMorphismOverk_of_galoisCompat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean)
-/
@[path]
private lemma isActionMorphismOverk_of_galoisCompat_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {C_pts : Type u}
  [hne : Nonempty C_pts]
  {φ : C_pts ≃ E_pts} :
-- imply
  @IsActionMorphismOverk _ _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) := by
-- proof
  apply isActionMorphismOverk_of_galoisCompat k W E_pts C_pts φ


-- created on 2026-10-23
