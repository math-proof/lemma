/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/LongestCycle.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.LongestCycle

namespace SimpleGraph.Walk

example {V : Type*} {G : SimpleGraph V} {v : V} (p : G.Walk v v) :
    p.IsLongestCycle ↔
      p.IsCycle ∧ ∀ (w : V) (q : G.Walk w w), q.IsCycle → q.length ≤ p.length :=
  Iff.rfl

example {V : Type*} {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsLongestCycle) : p.IsCycle :=
  hp.1

end SimpleGraph.Walk
