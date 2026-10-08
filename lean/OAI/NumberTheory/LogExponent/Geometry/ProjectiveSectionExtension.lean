import OAI.NumberTheory.LogExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.LogExponent.Approximation.ClosedPushforwardCoherent
import OAI.NumberTheory.LogExponent.Approximation.SerreSectionLifting
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveGlobalPolynomials
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveSpaceSerre
import OAI.NumberTheory.LogExponent.LocalAlgebra.IdealModule

namespace OAI

namespace LogExponent.ProjectiveSectionExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open LogExponentSeshadri.Geometry
open GeometrySupport

variable {X Y : Scheme.{0}}

def quotientPowerRestriction (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) :=
  s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (LogExponentSeshadri.IdealModule.structureMap f)

lemma idealModule_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (LogExponentSeshadri.IdealModule.idealModule f).IsFinitePresentation := by
  let : (LogExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (LogExponentSeshadri.IdealModule.unit Y).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward f).obj
      (LogExponentSeshadri.IdealModule.unit X)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj
        (LogExponentSeshadri.IdealModule.unit X))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (LogExponentSeshadri.IdealModule.structureMap f)

theorem quotientPowerRestriction_surjective_of_h1_zero
    (L : LineBundle Y) (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ)
    (hzero : ∀ x : cohomology
      ((moduleTwistFunctor L n).obj (LogExponentSeshadri.IdealModule.idealModule f)) 1, x = 0) :
    Function.Surjective (quotientPowerRestriction L f n) := by
  let S := ShortComplex.mk (LogExponentSeshadri.IdealModule.inclusion f)
    (LogExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  have hS : S.ShortExact := LogExponentSeshadri.IdealModule.closedSequence_exact f
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor L n)) (moduleTwistFunctor_shortExact L n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso L n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor L n).map
    (LogExponentSeshadri.IdealModule.structureMap f) = s at ht
  change (t ≫ (moduleTwistUnitIso L n).hom) ≫ (moduleTwistUnitIso L n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_projective_quotientPowerRestriction_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (quotientPowerRestriction (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  let := idealModule_isFinitePresentation f
  obtain ⟨N, hN⟩ := ProjectiveO1.serre_vanishing R σ
    (LogExponentSeshadri.IdealModule.idealModule f)
  exact ⟨N, fun n hn => quotientPowerRestriction_surjective_of_h1_zero
    (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n (hN n hn 1 (by decide))⟩

end
end LogExponent.ProjectiveSectionExtension

end OAI
