import OAI.NumberTheory.LogExponent.Ampleness.AmpleFromCover
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveSpaceIntegral

namespace OAI

noncomputable section

namespace LogExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry

variable {R σ : Type} [CommRing R] [IsDomain R] [Finite σ] [Nonempty σ]

theorem lineBundle_ample : (lineBundle (R := R) (σ := σ)).IsAmple := by
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact LineBundle.ample_of_affine_section_cover (lineBundle (R := R) (σ := σ))
    coordinateSection coordinateSection_cover coordinateSection_isAffineOpen

end LogExponent.ProjectiveO1

end

end OAI
