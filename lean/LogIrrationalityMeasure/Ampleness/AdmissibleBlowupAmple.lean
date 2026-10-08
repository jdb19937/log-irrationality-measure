import LogIrrationalityMeasure.Ampleness.NumericalAmplenessTheorem
import LogIrrationalityMeasure.Geometry.AdmissibleCurveDegreeData

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.AdmissibleBlowupGeometry
variable {α : ℚ} {ν Λ D : ℝ} (d : AdmissibleParameters α ν Λ D)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end LogExponent.AdmissibleBlowupGeometry

end

end LogIrrationalityMeasure
