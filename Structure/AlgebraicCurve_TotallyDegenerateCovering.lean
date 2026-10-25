import Structure.AlgebraicCurve_SemistableCharts
import Structure.CerednikDrinfeld_Ribbon
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing CerednikDrinfeld

variable {L : Type} [Field L] (A : ValuationSubring L) (F : Type) [Field F] [Algebra L F]

structure TotallyDegenerateCovering (ϖ : A) : Type 1 where

  ϖ_mem : ϖ ∈ maximalIdeal A
  ϖ_ne_zero : (ϖ : L) ≠ 0

  V : Type
  [instFintypeV : Fintype V]
  [instDecidableEqV : DecidableEq V]

  side : V → Fin 2

  E : Type
  [instFintypeE : Fintype E]
  [instDecidableEqE : DecidableEq E]

  chart : V → ComponentChart A F (RatFunc (ResidueField A))

  annOut : E → Annulus A F

  annIn : E → Annulus A F

  src : E → V

  tgt : E → V
  side_src : ∀ e, side (src e) = 0
  side_tgt : ∀ e, side (tgt e) = 1

  nodeOut : E → Place (ResidueField A) (RatFunc (ResidueField A))
  nodeIn : E → Place (ResidueField A) (RatFunc (ResidueField A))
  attachedOut : ∀ e, (annOut e).IsAttached (chart (src e)) (nodeOut e)
  attachedIn : ∀ e, (annIn e).IsAttached (chart (tgt e)) (nodeIn e)

  dom_eq : ∀ e, (annIn e).dom = (annOut e).dom
  modulus_eq : ∀ e, (annIn e).modulus = (annOut e).modulus
  param_mul_param : ∀ e, (annOut e).param * (annIn e).param = algebraMap L F ((annOut e).modulus : L)

  width : E → ℕ+

  valuation_modulus : ∀ e, A.valuation ((annOut e).modulus : L) = A.valuation (ϖ : L) ^ (width e : ℕ)

  mem_nodes_iff : ∀ (v : V) (x : Place (ResidueField A) (RatFunc (ResidueField A))),
    x ∈ (chart v).nodes ↔ (∃ e, src e = v ∧ nodeOut e = x) ∨ (∃ e, tgt e = v ∧ nodeIn e = x)

  nodeOut_injective : ∀ e e', src e = src e' → nodeOut e = nodeOut e' → e = e'
  nodeIn_injective : ∀ e e', tgt e = tgt e' → nodeIn e = nodeIn e' → e = e'

  cover : ∀ P : Place L F, (∃ v, P ∈ (chart v).dom) ∨ (∃ e, P ∈ (annOut e).dom)

  disjoint_chart : ∀ v v', v ≠ v' → Disjoint (chart v).dom (chart v').dom
  disjoint_chart_ann : ∀ v e, Disjoint (chart v).dom (annOut e).dom
  disjoint_ann : ∀ e e', e ≠ e' → Disjoint (annOut e).dom (annOut e').dom

attribute [instance] TotallyDegenerateCovering.instFintypeV TotallyDegenerateCovering.instDecidableEqV
  TotallyDegenerateCovering.instFintypeE TotallyDegenerateCovering.instDecidableEqE

namespace TotallyDegenerateCovering

variable {A F} {ϖ : A} (𝒞 : TotallyDegenerateCovering A F ϖ)


end TotallyDegenerateCovering

end AlgebraicCurve

end
