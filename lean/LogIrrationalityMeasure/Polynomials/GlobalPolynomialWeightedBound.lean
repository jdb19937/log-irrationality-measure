import LogIrrationalityMeasure.Approximation.WeightedFrameDegree
import LogIrrationalityMeasure.Jets.AffineJetCoefficientFrame
import LogIrrationalityMeasure.Jets.AffineJetCoefficientInterface
import LogIrrationalityMeasure.Polynomials.GlobalPolynomialCoefficientLaw

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.GlobalPolynomialWeightedBound
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
open LogExponent.WeightedSliceDegree LogExponent.AffineJetCoefficientInterface

theorem coefficient_bound {X Y : Scheme.{0}} {K ι B : Type}
    [Field K] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : GlobalPolynomialCoefficientLaw.CoefficientLaw V e E P)
    (ev : B →+* MvPolynomial ι K)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q)
    (ρ : ι → ℝ) (r : ℝ) (eTarget : Frame φ (L.pullback f)) (s : Sections L n)
    (hbound : SupportBound ρ r (ev (P s))) :
    SupportBound ρ r (AffineJetCoefficientInterface.coefficient φ (L.pullback f) n eTarget
      (pullbackPowerSection L f n s)) := by
  obtain ⟨F, hF⟩ := GlobalPolynomialCoefficientLaw.exists_power_frame_of_law
    L f φ V g hg n e E P hP ev hev
  erw [AffineJetCoefficientInterface.coefficient_eq,
    AffineJetCoefficientFrame.polynomialCoefficient_eq]
  apply WeightedFrameDegree.coefficient_supportBound ρ r F
  exact Eq.mpr (congrArg (SupportBound ρ r) (hF s)) hbound

end LogExponent.GlobalPolynomialWeightedBound
end

end LogIrrationalityMeasure
