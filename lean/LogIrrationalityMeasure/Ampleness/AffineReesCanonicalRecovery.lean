import LogIrrationalityMeasure.Ampleness.ReesSheafCanonicalValue
import LogIrrationalityMeasure.Approximation.CanonicalAffineRecovery
import LogIrrationalityMeasure.LocalAlgebra.IdealFiniteGenerators

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.AffineReesCanonicalRecovery
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.ReesGrading LogExponentSeshadri.IdealPullback
open CanonicalRecoveryProperties
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion
  ReesSheafCechRecovery.ordinaryGlobalSection

theorem eventually_comap_bijective {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ComapBijective (projection I) (specIdeal (I^n)) ⊤ := by
  classical
  obtain ⟨m,a,ha⟩ := IdealFiniteGenerators.exists_generators I
  obtain ⟨N,hN⟩ := ReesSheafCechRecovery.eventually_recovery_and_cohomology I a ha
  refine ⟨N, ?_⟩
  intro n hn
  exact (CanonicalAffineRecovery.power_bijective_iff_comap I (projection I)
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n
    (ReesSheafCechRecovery.ordinaryGlobalSection I a ha n)
    (ReesSheafCechRecovery.ordinaryGlobalSection_inclusion I a ha n)).mp (hN n hn).1

end LogExponent.AffineReesCanonicalRecovery

end

end LogIrrationalityMeasure
