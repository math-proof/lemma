/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EulerCircuit.lean -/


module

public import Theorem.SimpleGraph.EulerCircuit
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section


namespace MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

abbrev triangle := SimpleGraph.cycleGraph 3

end MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit
