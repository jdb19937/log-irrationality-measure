import OAI.NumberTheory.LogExponent.Ampleness.AffineReesCanonicalRecovery
import OAI.NumberTheory.LogExponent.Ampleness.GlobalReesRecoveryComparison

namespace OAI

noncomputable section
namespace LogExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.BlowupGluing
open CanonicalRecoveryProperties

theorem eventually_ordinaryMap_app_bijective {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      OrdinaryBijective (projection I) I (exceptionalLineBundle I)
        (exceptionalInclusion I) (exceptional_presents I) n U.1 := by
  let : IsAffine U.1.toScheme := U.2
  let : IsNoetherianRing Γ(U.1.toScheme,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  obtain ⟨N,hN⟩ := AffineReesCanonicalRecovery.eventually_comap_bijective (affineCenterIdeal I U)
  exact ⟨N, fun n hn => (ordinary_iff_comap (projection I) I
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n U.1).mpr
      ((comap_app_bijective_iff_affine I U n).mpr (hN n hn))⟩

end LogExponent.GlobalReesRecoveryComparison

end

end OAI
