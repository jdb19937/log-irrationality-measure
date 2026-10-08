import OAI.NumberTheory.LogExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.LogExponent.Ampleness.ProjectiveO1Ample
import OAI.NumberTheory.LogExponent.Geometry.WeightedProjectiveEmbedding

namespace OAI

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

end OAI
