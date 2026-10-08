import LogIrrationalityMeasure.Ampleness.ReesFixedPower
import LogIrrationalityMeasure.Ampleness.ReesFixedRestriction

namespace LogIrrationalityMeasure

namespace LogExponent.ReesFrozenPower
noncomputable section
open LogExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem pieceEquiv_restriction {s t : Finset J} {p r : J} (hp : p ∈ s) (hr : r ∈ t)
    (hst : s ⊆ t) (n : ℕ) (z : ReesLocalizedIntersections.Piece I a s n) :
    letI := ReesPolynomialPresentation.presentationAlgebra I a
    letI := ReesGradedModule.gradedScalarAction I a
    (pieceEquiv I a hr n (GradedCech.setRestriction
      (GradedPolynomialLaurent.grading (J := J) (R := R)) (ReesGradedModule.integerPiece I)
      MvPolynomial.X GradedPolynomialLaurent.variable_mem hst n z)).val =
      restriction I a hst (pieceEquiv I a hp n z).val := by
  let := ReesPolynomialPresentation.presentationAlgebra I a
  let := ReesGradedModule.gradedScalarAction I a
  apply (coordinateEquiv I a t).injective
  rw [coordinate_pieceEquiv, ReesProductRestriction.chartPowerMap_restriction I a hp hr hst n]
  change ReesProductRestriction.chartRestriction I a hst
    (ReesProductPower.chartPowerMap I a hp n z).val = _
  simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [coordinate_pieceEquiv]

end
end LogExponent.ReesFrozenPower

end LogIrrationalityMeasure
