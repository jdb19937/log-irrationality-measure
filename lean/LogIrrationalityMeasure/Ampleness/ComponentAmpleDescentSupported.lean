import LogIrrationalityMeasure.Approximation.ModuleLinePowerLaws
import LogIrrationalityMeasure.Cohomology.NoetherianAmpleSerreVanishing

namespace LogIrrationalityMeasure

namespace LogExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open LogExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_tensor_cohomology_zero_of_closed_pushforward
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : (Scheme.Modules.pushforward f).obj N ≅ M)
    (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, ∀ q, 0 < q →
      ∀ x : cohomology (moduleTensor X M (K.tensor (L.pow n)).sheaf) q, x = 0 := by
  let D : Y.Modules := moduleTensor Y N (K.pullback f).sheaf
  have : D.IsFinitePresentation :=
    LogExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation (K.pullback f) 1 N
  obtain ⟨B,hB⟩ :=
    LogExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing
      (f ≫ p) (L.pullback f) hL D
  let e₀ : (Scheme.Modules.pushforward f).obj D ≅ moduleTensor X M K.sheaf :=
    (LogExponent.ProjectionFormula.iso f N K).symm ≪≫
      moduleTensorIso e (Iso.refl K.sheaf)
  refine ⟨B,fun n hn q hq => ?_⟩
  have hz := (LogExponent.ClosedImmersionSerreTransfer.twist_ext_zero_iff f D L n q).mp
    (hB n hn q hq)
  let eₙ : (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj D) ≅
      moduleTensor X M (K.tensor (L.pow n)).sheaf :=
    (moduleTwistFunctor L n).mapIso e₀ ≪≫
      moduleTwistPowerIso L (moduleTensor X M K.sheaf) n ≪≫
      moduleLineTensorAssoc M K (L.pow n)
  exact LogExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso eₙ q hz

end
end LogExponentSeshadri.ComponentAmpleDescent

end LogIrrationalityMeasure
