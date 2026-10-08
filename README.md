# The irrationality measure of the logarithm of a rational number is 2

For every positive rational α ≠ 1, μ(log α) = 2. In particular μ(log 2) = 2.

* Paper: `logmeasure.pdf` (source `logmeasure.tex`, build with `make`).
* Main theorem: `lean/LogIrrationalityMeasure.lean`, theorem `irrationality_measure_log`
  (also `irrationality_measure_log_two` and `log_not_liouvilleWith`, the latter in Mathlib's `LiouvilleWith` vocabulary).
* Proof: `lean/LogIrrationalityMeasure/`, a module-by-module modification of OpenAI's formalization of μ(π) = 2 (github.com/openai/math, `lean/OAI/NumberTheory/PiExponent/` at the Mathlib commit pinned in `lake-manifest.json`).

## Building and checking

```
cd lean
lake exe cache get          # Mathlib oleans
lake build LogIrrationalityMeasure
lake env lean AxiomCheck.lean
```

The last command is silent when every `#guard_msgs` block passes, i.e. when each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
