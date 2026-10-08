import LogIrrationalityMeasure.Ampleness.BlowupPresentationRestriction
import LogIrrationalityMeasure.Ampleness.BlowupUniversalBaseChange
import LogIrrationalityMeasure.Ampleness.ReesRelativeSections

namespace LogIrrationalityMeasure

namespace LogExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open LogExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  let A := I.ideal ⟨⊤,isAffineOpen_top X⟩
  have hp := hπ.postIso X.isoSpec (IdealPullback.specIdeal A)
    (IdealPullback.specIdeal_comap_toSpec I)
  obtain ⟨s,hs,ha⟩ := ReesGrading.relative_affine_section_cover A
    (π ≫ X.isoSpec.hom) J ι (presents_post_toSpec J ι hJ) hp
  exact ⟨A,s,hs,ha⟩

end
end LogExponentSeshadri.Geometry

end LogIrrationalityMeasure
