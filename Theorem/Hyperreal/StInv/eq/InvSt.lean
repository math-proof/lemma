module

public import Def.Analysis.Real.Limits.Basic

public section

open ArchimedeanClass


public theorem Hyperreal.StInv.eq.InvSt
  [LinearOrder K] [Field K] [IsOrderedRing K]
-- given
  (x : K) :
-- imply
  stdPart x⁻¹ = (stdPart x)⁻¹ :=
-- proof
  ArchimedeanClass.stdPart_inv x


-- created on 2025-12-09
-- updated on 2026-10-26
