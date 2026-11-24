module
public import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
public import Theorem.Analysis.MeasureTheory.Section_1_4_3.Part4


public section

def CountablyAdditiveMeasure.restrict_alg {X:Type*} {B B': ConcreteSigmaAlgebra X} (μ: CountablyAdditiveMeasure B) (hBB' : B' ≤ B) : CountablyAdditiveMeasure B' :=
  {
    toFinitelyAdditiveMeasure := μ.toFinitelyAdditiveMeasure.restrict_alg hBB',
    measure_countable_additive := fun E hE hdisj =>
      μ.measure_countable_additive E (fun n => hBB' (E n) (hE n)) hdisj
  }

