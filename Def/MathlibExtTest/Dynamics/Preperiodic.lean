/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

module

public import Def.Dynamics.Preperiodic.Part2
public import Theorem.Set.Preperiodic
public import Lean.Elab.Tactic.Omega
public import Theorem.MathlibExtTest.Dynamics.Preperiodic

@[expose] public section

def swap : Bool → Bool
  | true => false
  | false => true

