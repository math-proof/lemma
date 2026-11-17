module

public import Theorem.Hyperreal.EqSt_0.of.Infinitesimal
public import Theorem.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
public import Theorem.Hyperreal.Coe

public section

open Hyperreal


@[mt]
public theorem Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
  [NeZero (d : ℕ)]
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : (a / b - d) → 0) :
-- imply
  b → 0 := by
-- proof
  contrapose! h_b
  rw [Coe d]
  have h_d := NeZero.ne d
  by_contra h
  have h_st := EqSt.of.InfinitesimalSub (x := a / b) (r := (d : ℝ)) (lt_of_not_ge h)
  have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a (not_lt.mpr h_b)
  have h_ab := EqSt_0.of.Infinitesimal h_ab
  simp [h_ab] at h_st
  symm at h_st
  norm_cast at h_st


-- created on 2025-12-09
