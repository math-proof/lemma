module

public section


public theorem Bool.Imp.is.ImpNotS :
-- imply
  q → p ↔ ¬p → ¬q := by
-- proof
  grind


public theorem Bool.ImpNotS.is.Imp :
-- imply
  ¬p → ¬q ↔ q → p :=
  (Bool.Imp.is.ImpNotS (p := p) (q := q)).symm


public theorem Bool.ImpNotS.of.Imp
-- given
  (h : q → p) :
-- imply
  ¬p → ¬q :=
  (Bool.Imp.is.ImpNotS (p := p) (q := q)).mp h


public theorem Bool.Imp.of.ImpNotS
-- given
  (h : ¬p → ¬q) :
-- imply
  q → p :=
  (Bool.Imp.is.ImpNotS (p := p) (q := q)).mpr h


-- created on 2026-11-17
