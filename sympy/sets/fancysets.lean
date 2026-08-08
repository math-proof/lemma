import sympy.sets.sets

/--
SymPy [`Range(start, stop, step)`](https://docs.sympy.org/latest/modules/sets/fancysets.html#sympy.sets.fancysets.Range)
Python `range(start, stop, step)` as a list of integers. `stop` is exclusive.
-/
def Range (start stop step : ℤ) : List ℤ :=
  (List.range (((stop - start) * step.sign + |step| - 1) / |step|).toNat).map (start + · * step)
