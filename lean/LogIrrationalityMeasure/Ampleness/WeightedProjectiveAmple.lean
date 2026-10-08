import LogIrrationalityMeasure.Ampleness.ClosedAmpleRestriction
import LogIrrationalityMeasure.Ampleness.ProjectiveO1Ample
import LogIrrationalityMeasure.Geometry.WeightedProjectiveEmbedding

namespace LogIrrationalityMeasure

noncomputable section

namespace LogExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

theorem lineBundle_ample [IsDomain R] [Finite σ] [Nonempty σ] (a : σ → ι →₀ ℕ) :
    (lineBundle (R := R) a).IsAmple :=
  LineBundle.IsAmple.pullback_closedImmersion (ProjectiveO1.lineBundle (R := R) (σ := σ))
    ProjectiveO1.lineBundle_ample (projectiveMonomialMap a)

end LogExponent.WeightedCompactification

end

end LogIrrationalityMeasure
