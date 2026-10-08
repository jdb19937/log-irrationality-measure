import OAI.NumberTheory.LogExponent.Analysis.AnalyticAggregate
import OAI.NumberTheory.LogExponent.Approximation.Exponent

namespace OAI

namespace LogExponent

theorem log_ne_zero_of_rat {α : ℚ} (hα : 0 < α) (hα1 : α ≠ 1) : Real.log α ≠ 0 := by
  apply Real.log_ne_zero_of_pos_of_ne_one
  · exact_mod_cast hα
  · exact_mod_cast hα1

/-- Theorem N1 (conditional form): the interpolation hypothesis (Theorem 2.1′ for the
centres `(α^j, j p_i / q_i)`) implies the eventual lower bound
`|log α − p/q| ≥ q^{−ν}` for every `ν > 2`. -/
theorem logEventualLowerBound_of_globalInterpolation (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1)
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement α) :
    LogEventualLowerBound α :=
  DeterminantContradiction.logEventualLowerBound_of_interpolation_and_analytic_aggregate α
    (log_ne_zero_of_rat hα hα1) hgeometry (LiteralAnalytic.analyticAggregate α hα)

theorem log_integerEventualLowerBound_of_globalInterpolation (α : ℚ) (hα : 0 < α)
    (hα1 : α ≠ 1)
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement α) :
    IntegerEventualLowerBound (Real.log α) :=
  (eventualLowerBound_iff_integer (Real.log α)).mp
    (logEventualLowerBound_of_globalInterpolation α hα hα1 hgeometry)

/-- The irrationality exponent of `log α` is `2`, conditionally on the interpolation
hypothesis. -/
theorem log_irrationalityExponent_of_globalInterpolation (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1)
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement α) :
    irrationalityExponent (Real.log α) = 2 :=
  log_irrationalityExponent_eq_two_of_eventualLowerBound
    (logEventualLowerBound_of_globalInterpolation α hα hα1 hgeometry)

/-- The specialisation `α = 2`: `μ(log 2) = 2` under the interpolation hypothesis. -/
theorem log_two_irrationalityExponent_of_globalInterpolation
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement 2) :
    irrationalityExponent (Real.log 2) = 2 := by
  have h := log_irrationalityExponent_of_globalInterpolation 2 (by norm_num) (by norm_num) hgeometry
  simpa using h

end LogExponent

end OAI
