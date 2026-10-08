import OAI.NumberTheory.LogExponent.Ampleness.BlowupProperIntegral
import OAI.NumberTheory.LogExponent.Ampleness.ExceptionalRecoveryMap
import OAI.NumberTheory.LogExponent.Ampleness.GlobalBlowupAffineSquare
import OAI.NumberTheory.LogExponent.Ampleness.GlobalExceptionalComparison
import OAI.NumberTheory.LogExponent.Geometry.CanonicalRecoveryProperties
import OAI.NumberTheory.LogExponent.LocalAlgebra.IdealModuleRestriction
import OAI.NumberTheory.LogExponent.LocalAlgebra.IdealPullbackOpenSquare

namespace OAI

noncomputable section
namespace LogExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open LogExponentSeshadri.Geometry LogExponentSeshadri.IdealModule
open GeometrySupport CanonicalRecoveryProperties

theorem ordinaryMap_bijective_iff_comap {X Y : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f] (I : X.IdealSheafData)
    (E : LineBundle Y) (ι : E.sheaf ⟶ structureSheaf Y)
    (hE : PresentsPullbackIdeal I f E ι) (n : ℕ) (U : X.Opens) :
    Function.Bijective ((ExceptionalRecoveryMap.ordinaryMap f I E ι hE n).app U) ↔
      Function.Bijective ((IdealPullbackMap.comap f (I^n)).app U) := by
  have hb := ConcreteCategory.bijective_of_isIso
    ((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U))
  change Function.Bijective
    (((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U)) ∘
      ((IdealPullbackMap.comap f (I^n)).app U)) ↔ _
  exact hb.of_comp_iff' _

attribute [local irreducible] LogExponentSeshadri.BlowupGluing.affineRestrictionIso
  LogExponentSeshadri.ReesGrading.affineBlowup LogExponentSeshadri.ReesGrading.projection
  IdealPullbackMap.map IdealPullbackMap.comap

local instance affineChartNoetherian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (U : X.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) := by
  let : IsAffine U.1.toScheme := U.2
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩

instance affineProjection_quasiCompact {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    QuasiCompact (LogExponentSeshadri.ReesGrading.projection
      (LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) := by infer_instance

theorem comap_app_bijective_iff_affine_raw {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (U : X.affineOpens) :
    ComapBijective (LogExponentSeshadri.BlowupGluing.projection I) J U.1 ↔
      ComapBijective (LogExponentSeshadri.ReesGrading.projection
        (LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (J.comap (LogExponentSeshadri.BlowupGluing.baseChart U)) ⊤ :=
  CanonicalRecoveryProperties.comap_open_square
    (LogExponentSeshadri.BlowupGluing.projection I)
    (LogExponentSeshadri.BlowupGluing.baseChart U)
    (LogExponentSeshadri.BlowupGluing.totalChart I U)
    (LogExponentSeshadri.ReesGrading.projection
      (LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
    (LogExponentSeshadri.BlowupGluing.totalChart_projection I U) J U.1 ⊤ ⊤
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      LogExponentSeshadri.BlowupGluing.baseChart_opensRange])
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      LogExponentSeshadri.BlowupGluing.totalChart_opensRange])
    (by simp)

theorem comap_app_bijective_iff_affine {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    ComapBijective (LogExponentSeshadri.BlowupGluing.projection I) (I^n) U.1 ↔
      ComapBijective (LogExponentSeshadri.ReesGrading.projection
        (LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (LogExponentSeshadri.IdealPullback.specIdeal
          ((LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n)) ⊤ := by
  have hh := comap_app_bijective_iff_affine_raw I (I^n) U
  have he : (I^n).comap (LogExponentSeshadri.BlowupGluing.baseChart U) =
      LogExponentSeshadri.IdealPullback.specIdeal
        ((LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n) := by
    rw [LogExponentSeshadri.IdealPullback.comap_pow,
      LogExponentSeshadri.BlowupGluing.center_comap_baseChart,
      LogExponentSeshadri.IdealPullback.specIdeal_pow]
  exact hh.trans (iff_of_eq (congrArg (fun J => ComapBijective
    (LogExponentSeshadri.ReesGrading.projection
      (LogExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) J ⊤) he))

end LogExponent.GlobalReesRecoveryComparison

end

end OAI
