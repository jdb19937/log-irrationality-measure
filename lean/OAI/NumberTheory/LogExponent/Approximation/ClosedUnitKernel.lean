import OAI.NumberTheory.LogExponent.Approximation.ClosedSectionLifting
import OAI.NumberTheory.LogExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.LogExponent.Approximation.SerrePowerDescent

namespace OAI

noncomputable section
namespace LogExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open LogExponentSeshadri.TensorPure


variable {X Y : Scheme.{0}}

def closedLineQuotientIso (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) M.sheaf ≅
      (Scheme.Modules.pushforward f).obj (M.pullback f).sheaf :=
  LogExponent.ProjectionFormula.iso f (structureSheaf Y) M ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (M.pullback f).sheaf)

theorem closedLineQuotientIso_map (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensorMap (LogExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) ≫
      (closedLineQuotientIso f M).hom =
    (moduleTensorUnit M.sheaf).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf := by
  apply LogExponentSeshadri.TensorPure.hom_ext
  intro U a m
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf).val.app (op U)
  have ht := map_pure (LogExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) U a m
  have hp := LogExponent.ProjectionFormula.hom_pure f (structureSheaf Y) M.sheaf U
    ((LogExponentSeshadri.IdealModule.structureMap f).app U a) m
  have hu := unit_pure (M.pullback f).sheaf (f ⁻¹ᵁ U)
    ((LogExponentSeshadri.IdealModule.structureMap f).app U a) (η m)
  have hv := unit_pure M.sheaf U a m
  have hs := η.hom.map_smul a m
  exact (congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U)
      ((LogExponent.ProjectionFormula.hom f (structureSheaf Y) M.sheaf).app U z)) ht).trans
    ((congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U) z) hp).trans
      (hu.trans (hs.symm.trans (congrArg (fun z => η z) hv).symm)))

def closedLineUnitKernelIso (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    moduleTensor X (LogExponentSeshadri.IdealModule.idealModule f) M.sheaf ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) := by
  let S := ShortComplex.mk (LogExponentSeshadri.IdealModule.inclusion f)
    (LogExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  let T := S.map (moduleTwistFunctor M 1)
  have hT : T.ShortExact := moduleTwistFunctor_shortExact M 1 S
    (LogExponentSeshadri.IdealModule.closedSequence_exact f)
  let e : T.X₁ ≅ kernel T.g :=
    hT.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  exact e ≪≫ kernel.mapIso T.g
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)
    (moduleTensorUnit M.sheaf) (closedLineQuotientIso f M)
    (closedLineQuotientIso_map f M)

theorem pullbackSection_surjective_of_idealTensor_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (moduleTensor X (LogExponentSeshadri.IdealModule.idealModule f) M.sheaf) 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  apply pullbackSection_surjective_of_kernel_cohomology_zero f M
  exact LogExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso
    (closedLineUnitKernelIso f M) 1 hzero

end LogExponentSeshadri.Geometry

end

end OAI
