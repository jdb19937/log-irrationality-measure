import OAI.NumberTheory.LogExponent.Ampleness.AdmissibleCurveModelDegrees

namespace OAI

noncomputable section
namespace LogExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {α : ℚ} {ν Λ D : ℝ} (d : AdmissibleParameters α ν Λ D)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := AdmissibleCurveModel.existsModelData d C hn hm
  exact ⟨AdmissibleCurveModel.degreeData d C r⟩

end LogExponent.AdmissibleBlowupMargin

namespace LogExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry
variable {α : ℚ} {ν Λ D : ℝ} (d : AdmissibleParameters α ν Λ D)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (AdmissibleBlowupMargin.affineCurveDegreeData d)

end LogExponent.AdmissibleBlowupGeometry

end

end OAI
