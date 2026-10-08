import OAI.NumberTheory.LogExponent.Approximation.ClosedPushforwardCoherent
import OAI.NumberTheory.LogExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.LogExponent.Jets.CompactJetIdeal
import OAI.NumberTheory.LogExponent.LocalAlgebra.IdealModule

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LogExponent.CompactJetIdeal


theorem closedModule_isFinitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (LogExponentSeshadri.IdealModule.closedModule I).IsFinitePresentation := by
  let : (LogExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (LogExponentSeshadri.IdealModule.unit I.subscheme).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (LogExponentSeshadri.IdealModule.unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (LogExponentSeshadri.IdealModule.unit I.subscheme))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (LogExponentSeshadri.IdealModule.structureMap I.subschemeι)

theorem extend_isFinitePresentation {U X : Scheme} [IsLocallyNoetherian X]
    (I : U.IdealSheafData) (j : U ⟶ X) :
    (LogExponentSeshadri.IdealModule.closedModule (extend I j)).IsFinitePresentation :=
  closedModule_isFinitePresentation (extend I j)

end LogExponent.CompactJetIdeal
end

end OAI
