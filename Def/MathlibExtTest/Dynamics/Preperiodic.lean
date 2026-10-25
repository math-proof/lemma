/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/Preperiodic.lean -/

import Def.Dynamics.Preperiodic.Part2
import Lemma.Set.Preperiodic
import Lean.Elab.Tactic.Omega
import Theorem.MathlibExtTest.Dynamics.Preperiodic


def swap : Bool → Bool
  | true => false
  | false => true

