/- Verification harness for the `LogExponent` port. Each `#guard_msgs` block fails
elaboration unless `#print axioms` reports exactly Lean's three standard axioms. -/
import LogIrrationalityMeasure.Approximation.InterpolationConsequence
import LogIrrationalityMeasure.Main
import LogIrrationalityMeasure

/-- info: 'LogIrrationalityMeasure.LogExponent.log_irrationalityExponent_of_globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_irrationalityExponent_of_globalInterpolation

/-- info: 'LogIrrationalityMeasure.LogExponent.logEventualLowerBound_of_globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.logEventualLowerBound_of_globalInterpolation

/-- info: 'LogIrrationalityMeasure.LogExponent.log_integerEventualLowerBound_of_globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_integerEventualLowerBound_of_globalInterpolation

/-- info: 'LogIrrationalityMeasure.LogExponent.log_two_irrationalityExponent_of_globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_two_irrationalityExponent_of_globalInterpolation

/-- info: 'LogIrrationalityMeasure.LogExponent.DeterminantContradiction.logEventualLowerBound_of_interpolation_and_analytic_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.DeterminantContradiction.logEventualLowerBound_of_interpolation_and_analytic_aggregate

/-- info: 'LogIrrationalityMeasure.LogExponent.LiteralAnalytic.analyticAggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.LiteralAnalytic.analyticAggregate

/-- info: 'LogIrrationalityMeasure.LogExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound

/-- info: 'LogIrrationalityMeasure.LogExponent.MatrixTranslation.det_matrix_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.MatrixTranslation.det_matrix_translation

/-- info: 'LogIrrationalityMeasure.LogExponent.formal_period_collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.formal_period_collision_bound

/-- info: 'LogIrrationalityMeasure.LogExponent.exists_admissible_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.exists_admissible_parameters

/-- info: 'LogIrrationalityMeasure.LogExponent.irrational_of_eventualLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.irrational_of_eventualLowerBound

/-- info: 'LogIrrationalityMeasure.LogExponent.exp_logarithmicPeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.exp_logarithmicPeriod

/-! ## Unconditional theorems (stage 2: the interpolation hypothesis discharged) -/

/-- info: 'LogIrrationalityMeasure.LogExponent.globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.globalInterpolation

/-- info: 'LogIrrationalityMeasure.LogExponent.log_irrationalityExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_irrationalityExponent

/-- info: 'LogIrrationalityMeasure.LogExponent.log_two_irrationalityExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_two_irrationalityExponent

/-- info: 'LogIrrationalityMeasure.LogExponent.log_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_main

/-- info: 'LogIrrationalityMeasure.LogExponent.log_not_liouvilleWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.LogExponent.log_not_liouvilleWith

/-! ## Main theorems of the repository (`LogIrrationalityMeasure.lean`) -/

/-- info: 'LogIrrationalityMeasure.irrationality_measure_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.irrationality_measure_log

/-- info: 'LogIrrationalityMeasure.irrationalityExponent_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.irrationalityExponent_log

/-- info: 'LogIrrationalityMeasure.irrationality_measure_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.irrationality_measure_log_two

/-- info: 'LogIrrationalityMeasure.log_not_liouvilleWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogIrrationalityMeasure.log_not_liouvilleWith
