import LogIrrationalityMeasure.Ampleness.AdmissibleJetAmpleness
import LogIrrationalityMeasure.Ampleness.BlowupJetSurjectivityComplete

namespace LogIrrationalityMeasure

namespace LogExponent.AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry
open LogExponent.AdmissibleBlowupGeometry LogExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable {α : ℚ} {ν Λ D : ℝ} (d : AdmissibleParameters α ν Λ D)

theorem eventual_jetRestriction_surjective :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  exact eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) (blowupBundle_ample d)

theorem eventually_jetRestriction_surjective :
    ∀ᶠ n in Filter.atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  obtain ⟨N,hN⟩ := eventual_jetRestriction_surjective d
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

end
end LogExponent.AdmissibleJetSurjectivity

end LogIrrationalityMeasure
