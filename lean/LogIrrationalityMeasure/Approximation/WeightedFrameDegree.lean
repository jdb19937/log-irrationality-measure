import LogIrrationalityMeasure.Approximation.WeightedSliceDegree
import LogIrrationalityMeasure.Polynomials.FrameCoefficients

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.WeightedFrameDegree
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Frames
open LogExponent.WeightedSliceDegree
variable {K ι : Type} [Field K]

theorem supportBound_unit_mul (ρ : ι → ℝ) (B : ℝ)
    (u p : MvPolynomial ι K) (hu : IsUnit u) (hp : SupportBound ρ B p) :
    SupportBound ρ B (u * p) := by
  obtain ⟨c, _, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  simpa only [zero_add] using (supportBound_C ρ c).mul hp

theorem coefficient_supportBound (ρ : ι → ℝ) (B : ℝ)
    {M : (Spec (CommRingCat.of (MvPolynomial ι K))).Modules}
    (E F : M ≅ O (Spec (CommRingCat.of (MvPolynomial ι K))))
    (s : O (Spec (CommRingCat.of (MvPolynomial ι K))) ⟶ M)
    (h : SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient E s))) :
    SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient F s)) := by
  rw [coefficient_change E F, map_mul]
  apply supportBound_unit_mul ρ B _ _ ?_ h
  exact (frameChange E F).isUnit.map
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom.hom

end LogExponent.WeightedFrameDegree
end

end LogIrrationalityMeasure
