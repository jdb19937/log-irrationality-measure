import LogIrrationalityMeasure.LocalAlgebra.RegularSequenceLowExt
import LogIrrationalityMeasure.Polynomials.PolynomialLocalRegularParameters

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u

theorem polynomialLocal_residueExt_below_height
    (K : Type u) [Field K] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (i : ℕ) (hi : (i : ℕ∞) < Q.height) :
    Subsingleton (Ext
      (ModuleCat.of (Localization.AtPrime Q)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)))
      (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  obtain ⟨h, hh, xs, hlen, hreg, hmax⟩ :=
    LogExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height K n Q
  apply residueFieldExt_below_regular_length xs hreg hmax i
  rw [hlen]
  exact ENat.natCast_lt_natCast.mp (by simpa only [hh] using hi)

end LogExponentSiegelAux.W30

end

end LogIrrationalityMeasure
