import Mathlib
import Lemma.UpperHalfPlane.Gamma0ExactVolume
import Instance.AutomorphicForm_L2ProductionInstance

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal Modular

namespace FLT.ModularFundamentalDomain

open FLT.HyperbolicMeasure FLT.Gamma0ExactVolume FLT.FundamentalDomainExactVolume
open FLT.L2ProductionInstance


def goodSet : Set ℍ := {z | ∃ γ : SL(2, ℤ), γ • z ∈ (𝒟ᵒ : Set ℍ)}

end FLT.ModularFundamentalDomain
