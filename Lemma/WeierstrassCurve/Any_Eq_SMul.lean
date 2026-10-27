import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_Flat
import Def.GaloisRep_Residual
import Lemma.FLTPrelim.GaloisRep
import Lemma.Int.P2MUtil
open scoped NNReal
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Int
set_option maxHeartbeats 800000


/--
[WeierstrassCurve_exists_addEquiv_torsionBy_ratBaseChange_eq_padicMap_padicAlgClosure](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_addEquiv_torsionBy_ratBaseChange_eq_padicMap_padicAlgClosure.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
  {E : WeierstrassCurve ℚ}
  {n : ℕ} :
-- imply
  ∃ c : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ_[p])).Point n ≃+
        Submodule.torsionBy ℤ ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n,
    ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P,
      c (σ • P) = σ • c P := by
-- proof
  have hEeq : (E⁄(AlgebraicClosure ℚ_[p])) = ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])) := by
    show E.baseChange _ = (E.map _).baseChange _
    unfold WeierstrassCurve.baseChange; rw [WeierstrassCurve.map_map]; congr 1
  let c_fwd : (E⁄(AlgebraicClosure ℚ_[p])).Point → ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point :=
    fun P => match P with
      | .zero => .zero
      | .some x y h => .some x y (hEeq ▸ h)
  have hσ_fwd : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) Q,
      c_fwd (σ • Q) = σ • c_fwd Q := by
    intro σ Q
    cases Q with
    | zero => rfl
    | some x y h =>
      show c_fwd (σ • (Affine.Point.some x y h)) = σ • c_fwd (Affine.Point.some x y h)
      rw [algEquiv_smul_def, algEquiv_smul_def, Affine.Point.map_some, Affine.Point.map_some]
  have h_fwd_heq : ∀ P, HEq (c_fwd P) P := by
    intro P
    cases P with
    | zero =>
      show HEq (Affine.Point.zero : ((E.map _)⁄_).Point) (Affine.Point.zero : (E⁄_).Point)
      exact hEeq ▸ HEq.rfl
    | some x y h =>
      show HEq (Affine.Point.some x y (hEeq ▸ h)) (Affine.Point.some x y h)
      exact @Eq.rec _ (E⁄(AlgebraicClosure ℚ_[p]))
        (fun W heq => HEq (Affine.Point.some x y (heq ▸ h) : W.Point)
                          (Affine.Point.some x y h : (E⁄(AlgebraicClosure ℚ_[p])).Point))
        HEq.rfl _ hEeq
  let cPt : (E⁄(AlgebraicClosure ℚ_[p])).Point ≃+
      ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point :=
    hEeq ▸ AddEquiv.refl _
  have h_cPt_heq : ∀ P : (E⁄(AlgebraicClosure ℚ_[p])).Point, HEq (cPt P) P := by
    intro P
    exact @Eq.rec _ (E⁄(AlgebraicClosure ℚ_[p]))
      (fun W heq => HEq ((heq ▸ AddEquiv.refl (E⁄(AlgebraicClosure ℚ_[p])).Point :
            (E⁄(AlgebraicClosure ℚ_[p])).Point ≃+ W.Point) P) P)
      HEq.rfl _ hEeq
  have hcast : ∀ P, c_fwd P = cPt P :=
    fun P => eq_of_heq ((h_fwd_heq P).trans (h_cPt_heq P).symm)
  refine ⟨{
    toFun := fun ⟨P, hP⟩ => ⟨cPt P, by
      rw [Submodule.mem_torsionBy_iff] at hP ⊢
      rw [← map_zsmul, hP, cPt.map_zero]⟩
    invFun := fun ⟨Q, hQ⟩ => ⟨cPt.symm Q, by
      rw [Submodule.mem_torsionBy_iff] at hQ ⊢
      rw [← map_zsmul, hQ, cPt.symm.map_zero]⟩
    left_inv := fun ⟨P, _⟩ => Subtype.ext (cPt.symm_apply_apply P)
    right_inv := fun ⟨Q, _⟩ => Subtype.ext (cPt.apply_symm_apply Q)
    map_add' := fun ⟨P, _⟩ ⟨Q, _⟩ => Subtype.ext (cPt.map_add P Q)
  }, ?_⟩
  intro σ ⟨P, hP⟩
  apply Subtype.ext
  show cPt (σ • P) = σ • cPt P
  rw [← hcast, ← hcast]
  exact hσ_fwd σ P


-- created on 2026-10-24
