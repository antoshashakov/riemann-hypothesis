module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IntersectionNumberFieldEquiv
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.intersection_number_field_equiv : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (V : Ideal (MRing ι F)) (l : List (K → ℤ)), intNumL F' (V.map (MvPolynomial.map (e : F →+* F'))) l = intNumL F V l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv | exact GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.intNumL_map_ringEquiv <;> assumption)
