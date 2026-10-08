import OAI.NumberTheory.LogExponent.Ampleness.ExceptionalAffineChart
import OAI.NumberTheory.LogExponent.Ampleness.ReesExceptionalSheaf
import OAI.NumberTheory.LogExponent.Ampleness.ReesProductSchemeChart

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
namespace LogExponent.ReesProductPowerSections
open LogExponentSeshadri.ReesGrading LogExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)
variable {p : J} (hp : p ∈ s)
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  LogExponentSeshadri.Geometry.LineBundle.pow LogExponentSeshadri.Geometry.PresentsPullbackIdeal
  LogExponent.ExceptionalAffineChart.sectionsEquiv LogExponent.ExceptionalAffineChart.idealChartFrame

include hp in

theorem chartFrame_nonempty :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme) := by
  rw [exceptionalLineBundle_sheaf_eq]
  exact ⟨ExceptionalAffineChart.idealChartFrame (Y := affineBlowup I) (chartMorphism I a hs) (exceptionalIdeal I)
    (chartEquation I a (s := s) (p := p))
    (exceptional_chart I a hs hp) (chartEquation_regular I a hp)⟩

def chartFrame :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end LogExponent.ReesProductPowerSections
end

end OAI
