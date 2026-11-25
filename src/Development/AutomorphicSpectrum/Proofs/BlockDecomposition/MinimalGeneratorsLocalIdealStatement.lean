module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsLocalIdeal
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.minimal_generators_local_ideal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ (r : ℕ) (t : Fin r → R), Ideal.span (Set.range t) = I ∧
      ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.exists_minimal_generators | exact GlobalTheory.CompanionTheory.FewEq.exists_minimal_generators | (intros; apply GlobalTheory.CompanionTheory.FewEq.exists_minimal_generators <;> assumption)
