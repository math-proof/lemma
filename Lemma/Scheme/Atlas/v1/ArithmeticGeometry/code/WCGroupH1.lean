import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1
open GaloisCohomology


/--
[galoisAction_mul_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean)
-/
@[path]
lemma galoisAction_mul_compat
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [TopologicalSpace E_pts]
  [DistribMulAction G E_pts]
  [ContinuousSMul G E_pts]
  {T : ETorsor k W E_pts}
  {ga : GaloisActionOnTorsor k W E_pts G T}
  {τ σ : G}
  {c : T.C_pts} :
-- imply
  ga.σ_C (τ * σ) c = ga.σ_C τ (ga.σ_C σ c) :=
-- proof
  ga.mul_compat τ σ c

/--
[cocycleCondition_of_galoisAction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean)
-/
@[path]
lemma cocycleCondition_of_galoisAction
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [TopologicalSpace E_pts]
  [DistribMulAction G E_pts]
  [ContinuousSMul G E_pts]
  {T : ETorsor k W E_pts}
  {ga : GaloisActionOnTorsor k W E_pts G T}
  {Q₀ : T.C_pts} :
-- imply
  haveI :=
-- proof
  T.torsor.toAddTorsor
    IsCrossedHom (fun σ => ga.σ_C σ Q₀ -ᵥ Q₀ : G → E_pts) := by
    letI : AddTorsor E_pts T.C_pts := T.torsor.toAddTorsor
    intro τ σ
    show ga.σ_C (τ * σ) Q₀ -ᵥ Q₀ = τ • (ga.σ_C σ Q₀ -ᵥ Q₀) + (ga.σ_C τ Q₀ -ᵥ Q₀)
    rw [galoisAction_mul_compat k W E_pts G T ga τ σ Q₀]
    conv_lhs => rw [show ga.σ_C σ Q₀ = (ga.σ_C σ Q₀ -ᵥ Q₀) +ᵥ Q₀ from (vsub_vadd _ _).symm]
    rw [ga.compat τ (ga.σ_C σ Q₀ -ᵥ Q₀) Q₀]
    exact vadd_vsub_assoc _ _ _

/--
[galoisAction_kIsom_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean)
-/
@[path]
lemma galoisAction_kIsom_compat
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [TopologicalSpace E_pts]
  [DistribMulAction G E_pts]
  [ContinuousSMul G E_pts]
  {T₁ T₂ : ETorsor k W E_pts}
  {e : T₁.C_pts ≃ T₂.C_pts}
  {ga₁ : GaloisActionOnTorsor k W E_pts G T₁}
  {ga₂ : GaloisActionOnTorsor k W E_pts G T₂}
  {σ : G}
  {q : T₁.C_pts}
-- given
  (_hcompat : haveI := T₁.torsor.toAddTorsor; haveI := T₂.torsor.toAddTorsor; ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ e q)
  (hgal : ∀ σ q, e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q)) :
-- imply
  e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q) :=
-- proof
  hgal σ q

/--
[wc_equiv_h1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean)
-/
@[path]
lemma wc_equiv_h1
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [TopologicalSpace E_pts]
  [DistribMulAction G E_pts]
  [ContinuousAdd E_pts]
  [ContinuousNeg E_pts]
  [ContinuousSMul G E_pts] :
-- imply
  ∃ (f : WC k W E_pts → H1 G E_pts), Function.Bijective f := by
-- proof
  let data := WCH1Data.mk' k W E_pts G
  have hwd : ∀ (T₁ T₂ : ETorsor k W E_pts),
    T₁ ≈ T₂ → data.cocycleMap T₁ = data.cocycleMap T₂ :=
    data.cocycleMap_wellDefined
  let f : WC k W E_pts → H1 G E_pts :=
    Quotient.lift data.cocycleMap hwd
  refine ⟨f, ?_, ?_⟩
  ·
    intro a b hab
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound (data.cocycleMap_injective _ _ hab)
  ·
    intro h
    obtain ⟨T, hT⟩ := data.cocycleMap_surjective h
    exact ⟨Quotient.mk _ T, hT⟩

/--
[corollary_26_25](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WCGroupH1.lean)
-/
@[path]
lemma corollary_26_25
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [TopologicalSpace E_pts]
  [DistribMulAction G E_pts]
  [ContinuousAdd E_pts]
  [ContinuousNeg E_pts]
  [ContinuousSMul G E_pts] :
-- imply
  ∃ (grp : AddCommGroup (WC k W E_pts)), Nonempty (@AddEquiv (WC k W E_pts) (H1 G E_pts) grp.toAdd (inferInstance : Add (H1 G E_pts))) := by
-- proof
  let data := WCH1Data.mk' k W E_pts G
  exact ⟨WC.addCommGroupOfData data, ⟨wc_h1_equiv data⟩⟩


-- created on 2026-10-23
