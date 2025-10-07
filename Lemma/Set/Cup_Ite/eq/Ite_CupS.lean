import sympy.core.logic
import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Logic.BFnUFnFunIte.Cond.of.AndBFnUFn
import Lemma.Bool.BFnUFnFunIte.Not.of.AndBFnUFn
import Lemma.Logic.Or_Not
open Logic Bool


@[main, comm]
private lemma main
-- given
  (A : Set α)
  (p : τ → Prop)
  (t : τ)
  (f g : α → τ → Set β)
  (h : Decidable (p t)) :
-- imply
  (⋃ x ∈ A, if p t then
    f x t
  else
    g x t) = if p t then
    ⋃ x ∈ A, f x t
  else
    ⋃ x ∈ A, g x t := by
-- proof
  apply BFn_Ite.of.OrAndS
  mpr [BFnUFnFunIte.Cond.of.AndBFnUFn (p := p t) (σ := fun h => ⋃ x ∈ A, h x)]
  mpr [BFnUFnFunIte.Not.of.AndBFnUFn (p := p t) (σ := fun h => ⋃ x ∈ A, h x)]
  simp
  apply Or_Not


-- created on 2025-07-29
