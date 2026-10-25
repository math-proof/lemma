import Structure.AlgebraicCurve_TotallyDegenerateCovering

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open Finset

variable {E₁ V₁ E₂ V₂ : Type*} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [DecidableEq E₂] [DecidableEq V₂]


structure DegeneracyData.FiniteHom (D₁ : DegeneracyData E₁ V₁) (D₂ : DegeneracyData E₂ V₂) where

  mapV : V₁ → V₂

  mapE : E₁ → E₂

  a_mapE : ∀ e, D₂.a (mapE e) = mapV (D₁.a e)

  b_mapE : ∀ e, D₂.b (mapE e) = mapV (D₁.b e)

  deg : E₁ → ℕ+

  degV : V₁ → ℕ+

  degTotal : ℕ+

  w_mapE : ∀ e, D₂.w (mapE e) = deg e * D₁.w e

  sum_deg_a : ∀ (v : V₁) (e' : E₂), D₂.a e' = mapV v →
    ∑ e ∈ univ.filter (fun e => D₁.a e = v ∧ mapE e = e'), (deg e : ℕ) = degV v

  sum_deg_b : ∀ (v : V₁) (e' : E₂), D₂.b e' = mapV v →
    ∑ e ∈ univ.filter (fun e => D₁.b e = v ∧ mapE e = e'), (deg e : ℕ) = degV v

  sum_degV : ∀ v' : V₂, ∑ v ∈ univ.filter (fun v => mapV v = v'), (degV v : ℕ) = degTotal

namespace DegeneracyData.FiniteHom

variable {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂)


variable [Fintype E₂]


section IdComp

omit [Fintype E₂]


variable {E₃ V₃ : Type*} [Fintype E₂] [Fintype V₂] [DecidableEq E₃] [DecidableEq V₃] {D₃ : DegeneracyData E₃ V₃}


end IdComp

end DegeneracyData.FiniteHom

end CerednikDrinfeld

namespace AlgebraicCurve

namespace TotallyDegenerateCovering

open CerednikDrinfeld

variable {L : Type} [Field L] {A : ValuationSubring L} {ϖ : A}
variable {Fj Fk : Type} [Field Fj] [Field Fk] [Algebra L Fj] [Algebra L Fk] [Algebra Fj Fk]

def PlaceOver (P : Place L Fk) (Q : Place L Fj) : Prop :=
  P.toValuationSubring.comap (algebraMap Fj Fk) = Q.toValuationSubring

variable [IsScalarTower L Fj Fk]

structure Hom [IsScalarTower L Fj Fk] (𝒞k : TotallyDegenerateCovering A Fk ϖ) (𝒞j : TotallyDegenerateCovering A Fj ϖ)
    extends DegeneracyData.FiniteHom 𝒞k.toDegeneracyData 𝒞j.toDegeneracyData where

  side_mapV : ∀ v, 𝒞j.side (mapV v) = 𝒞k.side v

  integers_comap : ∀ v, (𝒞k.chart v).integers.comap (algebraMap Fj Fk) = (𝒞j.chart (mapV v)).integers

  dom_chart : ∀ (v : 𝒞k.V) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q →
    P ∈ (𝒞k.chart v).dom → Q ∈ (𝒞j.chart (mapV v)).dom

  dom_ann : ∀ (e : 𝒞k.E) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q →
    P ∈ (𝒞k.annOut e).dom → Q ∈ (𝒞j.annOut (mapE e)).dom

  valuation_evalAt_param : ∀ (e : 𝒞k.E) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q → P ∈ (𝒞k.annOut e).dom →
    A.valuation (Q.evalAt (𝒞j.annOut (mapE e)).param) = A.valuation (P.evalAt (𝒞k.annOut e).param) ^ (deg e : ℕ)

namespace Hom

variable {𝒞k : TotallyDegenerateCovering A Fk ϖ} {𝒞j : TotallyDegenerateCovering A Fj ϖ} (μ : 𝒞k.Hom 𝒞j)


end Hom

end TotallyDegenerateCovering

end AlgebraicCurve

end
