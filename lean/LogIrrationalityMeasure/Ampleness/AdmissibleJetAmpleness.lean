import LogIrrationalityMeasure.Ampleness.AdmissibleBlowupAmple
import LogIrrationalityMeasure.Ampleness.GlobalBlowupJetSurjectivity

namespace LogIrrationalityMeasure

namespace LogExponent.AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry
open LogExponent.AdmissibleBlowupGeometry LogExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable {α : ℚ} {ν Λ D : ℝ} (d : AdmissibleParameters α ν Λ D)

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply LogExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end LogExponent.AdmissibleJetSurjectivity

end LogIrrationalityMeasure
