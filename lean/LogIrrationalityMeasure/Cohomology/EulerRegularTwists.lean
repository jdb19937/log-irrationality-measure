import LogIrrationalityMeasure.Ampleness.AmpleAllPowersGeneration
import LogIrrationalityMeasure.Geometry.LineBundleProduct

namespace LogIrrationalityMeasure

namespace LogExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_common_tensor_generators [IsNoetherian X]
    (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ n : ℕ, ∃ G : (H.pow n).sheaf.GeneratingSections, G.IsFiniteType ∧
      ∃ G' : (L.tensor (H.pow n)).sheaf.GeneratingSections, G'.IsFiniteType := by
  let : L.sheaf.IsFinitePresentation :=
    LogExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := LogExponent.AmpleGlobalGeneration.ample_eventual_power_global_generators H hH
  obtain ⟨N', hN'⟩ := LogExponent.AmpleGlobalGeneration.ample_eventual_global_generators H hH L.sheaf
  let n := max N N'
  obtain ⟨G, hG⟩ := hN n (le_max_left _ _)
  obtain ⟨G', hG'⟩ := hN' n (le_max_right _ _)
  exact ⟨n, G, hG,
    SheafOfModules.GeneratingSections.equivOfIso (moduleTwistPowerIso H L.sheaf n) G',
    ⟨hG'.finite⟩⟩

end
end LogExponent.NumericalAmpleness

end LogIrrationalityMeasure
