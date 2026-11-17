module

public import Theorem.Hyperreal.Infinitesimal.is.All_LtAbs

public section

open Hyperreal


public theorem Hyperreal.Infinitesimal0 :
-- imply
  (0 : ℝ*) → 0 := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  simp


-- created on 2025-12-09
