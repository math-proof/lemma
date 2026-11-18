module

public import Structure.Dynamics.MarkovDecisionProcess

public section

open MeasureTheory ProbabilityTheory

namespace PolicyGradient

/-- `init` is a probability measure (compatibility with the former structure field `init_prob`). -/
public theorem StochasticMDP.init_prob {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (m : StochasticMDP S A) :
    IsProbabilityMeasure (m.init : Measure S) := inferInstance

end PolicyGradient
