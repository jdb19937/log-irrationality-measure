import OAI.NumberTheory.LogExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveSectionsPullback
import OAI.NumberTheory.LogExponent.Geometry.WeightedProjectiveLineBundle

namespace OAI

noncomputable section

namespace LogExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.Projective LogExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

def scalars (a : σ → ι →₀ ℕ) : R →+* Γ(Proj (imageGrade (R := R) a), ⊤) :=
  (projectiveMonomialMap a).appTop.hom.comp (ProjectiveO1.scalars (R := R) (σ := σ))

theorem coordinateSection_cover (a : σ → ι →₀ ℕ) :
    (⨆ i : σ, LogExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i)) = ⊤ :=
  pullback_sections_cover (ProjectiveO1.coordinateSection (R := R))
    ProjectiveO1.coordinateSection_cover (projectiveMonomialMap a)

theorem coordinateSection_isoOpen (a : σ → ι →₀ ℕ) (i : σ) :
    LogExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a i) := by
  have h := pullback_isoOpen_eq (ProjectiveO1.lineBundle (R := R) (σ := σ))
    (ProjectiveO1.coordinateSection i) (projectiveMonomialMap a)
  rw [ProjectiveO1.coordinateSection_isoOpen] at h
  exact h

theorem coordinateSection_isAffineOpen (a : σ → ι →₀ ℕ) (i : σ) :
    IsAffineOpen (LogExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i)) := by
  rw [coordinateSection_isoOpen]
  exact Proj.isAffineOpen_basicOpen _ _ (imageCoordinate_mem a i) (by decide)

theorem coordinate_sectionsMorphism_embedding (a : σ → ι →₀ ℕ) :
    sectionsMorphism (scalars (R := R) a) (coordinateSection a) (coordinateSection_cover a) =
      projectiveMonomialMap a := by
  exact (sectionsMorphism_pullback (ProjectiveO1.scalars (R := R) (σ := σ))
    ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (projectiveMonomialMap a)).symm.trans
      ((congrArg (fun g => projectiveMonomialMap (R := R) a ≫ g)
        ProjectiveO1.coordinate_sectionsMorphism_identity).trans (Category.comp_id _))

instance coordinate_sectionsMorphism_isClosedImmersion (a : σ → ι →₀ ℕ) :
    IsClosedImmersion
      (sectionsMorphism (scalars (R := R) a) (coordinateSection a) (coordinateSection_cover a)) := by
  rw [coordinate_sectionsMorphism_embedding]
  infer_instance

end LogExponent.WeightedCompactification

end

end OAI
