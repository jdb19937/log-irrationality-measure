/- Verification harness for the `LogExponent` port. Each `#guard_msgs` block fails
elaboration unless `#print axioms` reports exactly Lean's three standard axioms. -/
import OAI.NumberTheory.LogExponent.Approximation.InterpolationConsequence
import OAI.NumberTheory.LogExponent.Main

/-- info: 'OAI.LogExponent.log_irrationalityExponent_of_globalInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_irrationalityExponent_of_globalInterpolation

/-- info: 'OAI.LogExponent.logEventualLowerBound_of_globalInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.logEventualLowerBound_of_globalInterpolation

/-- info: 'OAI.LogExponent.log_integerEventualLowerBound_of_globalInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_integerEventualLowerBound_of_globalInterpolation

/-- info: 'OAI.LogExponent.log_two_irrationalityExponent_of_globalInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_two_irrationalityExponent_of_globalInterpolation

/-- info: 'OAI.LogExponent.DeterminantContradiction.logEventualLowerBound_of_interpolation_and_analytic_aggregate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.DeterminantContradiction.logEventualLowerBound_of_interpolation_and_analytic_aggregate

/-- info: 'OAI.LogExponent.LiteralAnalytic.analyticAggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.LiteralAnalytic.analyticAggregate

/-- info: 'OAI.LogExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound

/-- info: 'OAI.LogExponent.MatrixTranslation.det_matrix_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.MatrixTranslation.det_matrix_translation

/-- info: 'OAI.LogExponent.formal_period_collision_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.formal_period_collision_bound

/-- info: 'OAI.LogExponent.exists_admissible_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.exists_admissible_parameters

/-- info: 'OAI.LogExponent.irrational_of_eventualLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.irrational_of_eventualLowerBound

/-- info: 'OAI.LogExponent.exp_logarithmicPeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.exp_logarithmicPeriod

/-! ## Unconditional theorems (stage 2: the interpolation hypothesis discharged) -/

/-- info: 'OAI.LogExponent.globalInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.globalInterpolation

/-- info: 'OAI.LogExponent.log_irrationalityExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_irrationalityExponent

/-- info: 'OAI.LogExponent.log_two_irrationalityExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_two_irrationalityExponent

/-- info: 'OAI.LogExponent.log_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_main

/-- info: 'OAI.LogExponent.log_not_liouvilleWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.LogExponent.log_not_liouvilleWith
