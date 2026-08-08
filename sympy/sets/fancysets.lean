import sympy.sets.sets

def Range.length (start stop step : ℤ) : ℕ :=
  if step = 0 then
    0
  else if 0 < step then
    if start < stop then ((stop - start + step - 1) / step).toNat else 0
  else if stop < start then
    ((start - stop - step - 1) / (-step)).toNat
  else
    0

/--
SymPy [`Range(start, stop, step)`](https://docs.sympy.org/latest/modules/sets/fancysets.html#sympy.sets.fancysets.Range)
Python `range(start, stop, step)` as a list of integers. `stop` is exclusive.
-/
def Range (start stop step : ℤ) : List ℤ :=
  (List.range (Range.length start stop step)).map (start + · * step)
