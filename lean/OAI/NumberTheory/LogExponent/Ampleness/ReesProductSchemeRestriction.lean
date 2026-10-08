import OAI.NumberTheory.LogExponent.Ampleness.ReesProductRestriction
import OAI.NumberTheory.LogExponent.Ampleness.ReesProductSchemeChart

namespace OAI

namespace LogExponent.ReesProductSchemeRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry
open LogExponentSeshadri.ReesGrading
open LogExponent.ReesProductChart LogExponent.ReesProductRestriction
open LogExponent.ReesProductPowerSections
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem chartRestriction_chartMorphism {s t : Finset J} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (chartRestriction I a hst)) ≫ chartMorphism I a hs =
      chartMorphism I a ht := by
  have h := Proj.SpecMap_awayMap_awayι (piece I)
    (productGenerator_mem I a s) (Finset.card_pos.mpr hs)
    (productGenerator_mem I a (t \ s)) (productGenerator_factor I a hst)
  rw [chartMorphism_eq, chartMorphism_eq]
  unfold chartRestriction
  simpa only [Proj.awayι, Proj.basicOpenIsoSpec, affineBlowup] using h

end
end LogExponent.ReesProductSchemeRestriction

end OAI
