module

public import Theorem.Hyperreal.StInv.eq.InvSt

public section

open Hyperreal ArchimedeanClass


public theorem Hyperreal.StInv.eq.Inv.of.EqSt
  [LinearOrder K] [Field K] [IsOrderedRing K]
  {x : K}
  {a : ℝ}
-- given
  (h : stdPart x = a) :
-- imply
  stdPart x⁻¹ = a⁻¹ := by
-- proof
  rw [StInv.eq.InvSt]
  rw [h]


-- created on 2025-12-08
-- updated on 2026-10-26
