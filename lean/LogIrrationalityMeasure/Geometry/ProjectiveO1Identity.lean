import LogIrrationalityMeasure.Geometry.ProjectiveO1Morphism

namespace LogIrrationalityMeasure

noncomputable section

namespace LogExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Projective LogExponentSeshadri.Frames LogExponentSeshadri.LineBundleGluing

attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism

variable {R σ : Type} [CommRing R]

theorem coordinateSection_isoOpen (i : σ) :
    LogExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i) = coordinateOpen i := by
  exact identityCoordinateOpen (lineBundle (R := R) (σ := σ)).sheaf
    (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) i

theorem coordinateSection_isAffineOpen (i : σ) :
    IsAffineOpen (LogExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i)) := by
  rw [coordinateSection_isoOpen]
  exact standardChart_isAffineOpen i

end LogExponent.ProjectiveO1

end

end LogIrrationalityMeasure
