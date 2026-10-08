import OAI.NumberTheory.LogExponent.Ampleness.ReesExceptional
import OAI.NumberTheory.LogExponent.Geometry.LineBundleCoherent

namespace OAI

namespace LogExponent.ReesCohomologySetup
noncomputable section
open AlgebraicGeometry LogExponentSeshadri.ReesGrading
variable {R : Type} [CommRing R] (I : Ideal R)

instance [IsNoetherianRing R] : IsNoetherian (affineBlowup I) := by
  let : CompactSpace (affineBlowup I) :=
    QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian (projection I) }

theorem exceptionalPower_isQuasicoherent (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.IsQuasicoherent :=
  GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent (exceptionalLineBundle I) n

end
end LogExponent.ReesCohomologySetup

end OAI
