import LogIrrationalityMeasure.Ampleness.FiniteReesComparison
import LogIrrationalityMeasure.Ampleness.GlobalBlowupJetSurjectivity

namespace LogIrrationalityMeasure

namespace LogExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LogExponentSeshadri.Geometry
open LogExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_affine_recovery
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n → Function.Bijective
      ((ExceptionalRecoveryMap.ordinaryMap (LogExponentSeshadri.BlowupGluing.projection I)
        I (LogExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
        (LogExponentSeshadri.BlowupGluing.exceptionalInclusion I)
        (LogExponentSeshadri.BlowupGluing.exceptional_presents I) n).app U.1)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    have h : IsSeparated (p ≫ terminal.from (Spec (CommRingCat.of R))) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  obtain ⟨k,U,hcover,N,hN⟩ :=
    ExceptionalRecoveryMap.eventual_comparison_of_affine_recovery
      (LogExponentSeshadri.BlowupGluing.projection I) I
      (LogExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
      (LogExponentSeshadri.BlowupGluing.exceptionalInclusion I)
      (LogExponentSeshadri.BlowupGluing.exceptional_presents I) A hrecover
  exact eventual_blowup_jetRestriction_surjective_of_section_comparison
    p I A hample (fun i => (U i).1) (fun i => (U i).2) hcover ⟨N,hN⟩

end
end LogExponent.BlowupJetSurjectivity

end LogIrrationalityMeasure
