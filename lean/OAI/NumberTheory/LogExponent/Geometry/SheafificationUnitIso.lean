import OAI.NumberTheory.LogExponent.Approximation.TensorPure

namespace OAI

namespace LogExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso (M : X.Modules) :
    IsIso ((LogExponentSeshadri.TensorPure.adj X).unit.app M.val) := by
  exact (LogExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso (Iso.refl M.val)

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((LogExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (LogExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end LogExponentSeshadri.Geometry

end OAI
