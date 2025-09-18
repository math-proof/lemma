import sympy.core.relational
import Lemma.Algebra.EqCeil.is.Lt.Le
import Lemma.Set.In_Ioc.of.Lt.Le
open Algebra Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  x ∈ Ioc (⌈x⌉ - 1 : α) (⌈x⌉ : α) := by
-- proof
  denote h_d : d = ⌈x⌉
  have := Lt.Le.of.EqCeil h_d.symm
  let ⟨h₀, h₁⟩ := this
  rw [h_d] at h₀
  rw [h_d] at h₁
  apply In_Ioc.of.Lt.Le h₀ h₁


-- created on 2025-03-30
