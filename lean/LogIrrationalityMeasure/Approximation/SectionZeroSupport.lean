import LogIrrationalityMeasure.Approximation.SectionImageSupport
import LogIrrationalityMeasure.LocalAlgebra.SectionZeroIdeal

namespace LogIrrationalityMeasure

namespace LogExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
open LogExponent.InverseFrames LogExponent.SectionImageSupport
variable {X : Scheme.{0}}

theorem dualSection_isoOpen (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    LogExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) = sectionOpen X s := by
  ext x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  change (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ LogExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) ↔
    (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ LogExponentSeshadri.SectionOpens.isoOpen s
  erw [isoOpen_preimage_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U e), dualSection_restrict_coefficient,
    preimage_isoOpen s U.ι e]

theorem zeroIdeal_support (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    ((zeroIdeal L s).support : Set X) = (sectionOpen X s : Set X)ᶜ := by
  let := LogExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : SheafOfModules.IsQuasicoherent L.inverse.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change ((LogExponent.SectionImageIdeal.imageIdealSheaf (L.dualSection s)).support : Set X) = _
  rw [imageIdealSheaf_support, dualSection_isoOpen]

end
end LogExponent.SectionZeroIdeal

end LogIrrationalityMeasure
